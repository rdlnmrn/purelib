module

/-!
# Decidable proposition certificates

Constructive laws relate retained proposition witnesses to their actual Boolean
decisions.
-/

public section
namespace Purelib.Logic.Decidable

/-- A true decidable proposition cannot have decision value false. -/
public theorem false_of_decide_false {proposition : Prop}
    [Decidable proposition] (holds : proposition)
    (fails : decide proposition = false) : False := by
  rw [decide_eq_true holds] at fails
  exact Bool.noConfusion fails

end Purelib.Logic.Decidable
