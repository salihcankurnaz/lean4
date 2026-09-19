/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv

namespace Lean

namespace CollectAxioms

private inductive CacheEntry where
  /-- The declaration is currently being traversed. -/
  | active
  /-- The traversal encountered an active dependency, so this result is not safe to reuse. -/
  | incomplete
  /-- A complete, reusable set of axiom dependencies. -/
  | done (axioms : Array Name)

structure State where
  /-- Cache and traversal state for constants. -/
  seen   : NameMap CacheEntry := {}
  /-- Axioms accumulated for the current constant being processed. -/
  axioms : NameSet := {}
  /-- Active declarations whose contribution was skipped while closing a dependency cycle. -/
  openDeps : Array Name := #[]

abbrev M := ReaderT Environment $ StateM State

def runM (env : Environment) (x : M α) : α :=
  x.run env |>.run' {}

private def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

/--
Collect axioms reachable from constant `c`, using `extFind?` to look up pre-computed axioms
for imported declarations. Results are cached in `State.seen`.

An `active` cache entry marks a declaration on the current recursion stack. Encountering one
records an open dependency instead of treating the temporary marker as a completed empty result.
Results that still depend on an outer active declaration are marked `incomplete` and recomputed
when needed. When the traversal returns to the declaration that opened a cycle, that dependency
is closed and the now-complete result can be cached.
-/
private partial def collect
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M Unit := do
  let env ← read
  -- Check extension for pre-computed axioms (imported declarations)
  if let some axs := extFind? env c then
    modify fun s => { s with axioms := insertArray s.axioms axs, seen := s.seen.insert c (.done axs) }
    return
  -- Check local cache
  let s ← get
  if let some entry := s.seen.find? c then
    match entry with
    | .done axs =>
      modify fun s => { s with axioms := insertArray s.axioms axs }
      return
    | .active =>
      -- Do not use the in-progress result. Propagate the open dependency until the
      -- traversal returns to `c`, where the cycle can be closed safely.
      modify fun s => { s with openDeps := s.openDeps.push c }
      return
    | .incomplete => pure ()
  -- Recurse: temporarily clear axioms to isolate this constant's contribution.
  let savedAxioms := s.axioms
  let savedOpenDeps := s.openDeps
  modify fun s => { s with axioms := {}, openDeps := #[], seen := s.seen.insert c .active }
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM (collect extFind?)
  -- Take constants from the kernel env, which may differ from the elab env for (async) errors.
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collect extFind?)
  | none                 => pure ()
  let s ← get
  let collected := s.axioms
  -- An open dependency on `c` represents a back-edge into the current traversal. At this
  -- point all dependencies reachable from `c` have been traversed, so that dependency is
  -- closed. Dependencies on outer active declarations still make this result incomplete.
  let openDeps := s.openDeps.filter fun dep => dep != c
  let result := collected.toArray.qsort Name.lt
  let entry := if openDeps.isEmpty then CacheEntry.done result else CacheEntry.incomplete
  modify fun s => { s with
    seen     := s.seen.insert c entry
    axioms   := insertArray savedAxioms result
    openDeps := savedOpenDeps ++ openDeps
  }

/-- Collect axioms for `c` and return its sorted axiom list from the cache. -/
private def collectAndGet
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M (Array Name) := do
  collect extFind? c
  match (← get).seen.find? c with
  | some (.done axs) => return axs
  | _ => panic! s!"collectAndGet: '{c}' has no complete cache entry after collect"

end CollectAxioms

/--
Extension state holding imported module entries for efficient lookup of
pre-computed axiom data.

We use `registerPersistentEnvExtension` with manual lookup instead of `MapDeclarationExtension`
because `exportEntriesFnEx` needs to call `collect`, which needs the extension's `find?`, but
`exportEntriesFnEx` is defined inside the `builtin_initialize` that creates the extension and
thus cannot reference it. This state replicates `MapDeclarationExtension.find?`'s per-module
binary search without requiring the extension object.
-/
private structure ExportedAxiomsState where
  importedModuleEntries : Array (Array (Name × Array Name)) := #[]

instance : Inhabited ExportedAxiomsState := ⟨{}⟩

/-- Look up pre-computed axioms for an imported declaration. -/
private def ExportedAxiomsState.find? (s : ExportedAxiomsState) (env : Environment)
    (c : Name) : Option (Array Name) :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
    if h : modIdx.toNat < s.importedModuleEntries.size then
      match s.importedModuleEntries[modIdx].binSearch (c, #[]) (fun a b => Name.quickLt a.1 b.1) with
      | some entry => some entry.2
      | none       => none
    else none
  | none => none

/--
Environment extension that records axiom dependencies for all declarations in a module.
Entries are computed once by `beforeExportFn` when the olean is serialized, not during
elaboration. During elaboration, `collectAxioms` walks bodies directly. Downstream modules
look up pre-computed entries for imported declarations, so axiom collection never crosses
module boundaries.
-/
private builtin_initialize exportedAxiomsExt :
    PersistentEnvExtension (Name × Array Name) (Name × Array Name) ExportedAxiomsState ←
  registerPersistentEnvExtension {
    mkInitial     := pure {}
    addImportedFn := fun importedEntries => pure { importedModuleEntries := importedEntries }
    addEntryFn    := fun s _ => s
    exportEntriesFnEx := fun env s =>
      let exportedEnv := env.setExporting true
      let privateEnv := env.setExporting false
      -- Collect current-module declarations visible in the exported view.
      -- By pre-computing axiom data for every exported declaration, downstream modules can
      -- look up any imported declaration without walking its body, keeping collection
      -- module-local.
      let allNames := env.checked.get.constants.foldStage2
        (fun names name _ =>
          if (exportedEnv.find? name).isSome then names.push name
          else names) #[]
      -- Compute axioms within a shared state (for caching across declarations).
      -- Use `privateEnv` so that `collect` can see all constant bodies.
      let entries := CollectAxioms.runM privateEnv do
        allNames.mapM fun name =>
          return (name, ← CollectAxioms.collectAndGet s.find? name)
      -- Sort by name for binary search at import time.
      let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
      .uniform entries
    asyncMode     := .mainOnly
  }

/-- Collect all axioms transitively used by a constant. -/
public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  return CollectAxioms.runM privateEnv do
    CollectAxioms.collectAndGet s.find? constName

end Lean
