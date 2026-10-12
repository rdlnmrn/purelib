module

/-!
# Boolean decision certificates

Direct constructor cases identify the false branch of a retained Boolean
decision when its true branch is excluded.
-/

namespace Purelib.Data.Bool.Decide

/-- A Boolean value that is not true is false.

The two original Boolean constructors exhaust the retained decision. Excluding
the true constructor therefore identifies that same value with false. -/
public theorem bool_eq_false_of_not_eq_true
    (value : Bool) (notTrue : value ≠ true) : value = false := by
  cases value with
  | false => rfl
  | true => exact (notTrue rfl).elim
/-- Boolean values agree when their retained true-branch certificates are equivalent.

The two original constructors exhaust each Boolean. In a mixed constructor pair,
the supplied implication would identify false with true. -/
public theorem eq_of_true_iff {left right : Bool}
    (branches : left = true ↔ right = true) : left = right := by
  cases left with
  | false =>
      cases right with
      | false => rfl
      | true => exact Bool.noConfusion (branches.mpr rfl)
  | true =>
      cases right with
      | false => exact Bool.noConfusion (branches.mp rfl)
      | true => rfl

/-- A negated Boolean accepts exactly the false branch of its original value.

The certificate follows the two retained constructors of the Boolean and the
original negation table, without replacing either decision. -/
public theorem not_true_iff (value : Bool) : ((!value) = true ↔ value = false) := by
  cases value <;> decide

/-- A Boolean conjunction accepts exactly when both retained inputs accept.

The four original constructor pairs determine the conjunction table. Its true
branch retains the separate true-branch certificates of the same two inputs. -/
public theorem and_true_iff (left right : Bool) :
    ((left && right) = true ↔ left = true ∧ right = true) := by
  cases left <;> cases right <;> decide

end Purelib.Data.Bool.Decide
