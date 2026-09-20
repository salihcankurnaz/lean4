module

public section

noncomputable def mutualPick : Nat := Classical.choice ⟨0⟩

mutual
  inductive M1 where
    | mk : Fin (mutualPick + 1) → M2 → M1
  inductive M2 where
    | mk : M1 → M2
end

end
