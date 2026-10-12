module

meta import Lean.Elab.Tactic.RCases
-- Public finite numeral signatures retain the owned successor certificates.
public import Purelib.Data.Nat.Order

/-!
# The two coordinates of a finite pair

Direct natural constructor cases enumerate the two possible coordinates.
The public case certificate retains the exact two displayed alternatives.
-/

/-- Every index of `Fin 2` is its first or second coordinate.

The retained natural bound excludes any coordinate after the second.
Natural constructor cases identify the two displayed finite values. -/
public theorem Purelib.Data.Fin.Two.finTwo_cases (coordinate : Fin 2) :
    coordinate = 0 ∨ coordinate = 1 := by
  rcases coordinate with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr rfl
  exact False.elim
    (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))
