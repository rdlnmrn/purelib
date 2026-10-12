module

public import Purelib.Data.Sign.Basic

/-!
# Stability of formal signs against retained nearby signs

A zero endpoint sign imposes no nearby restriction. A nonzero endpoint
retains its exact nearby sign, including under negation and multiplication.
-/

namespace Purelib.Data.Sign

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- A formal endpoint sign is stable when it is zero or equals the nearby sign.

A nonzero endpoint therefore forces the same nearby sign; a zero endpoint places no
restriction on the nearby sign. -/
@[expose] public def Stable (atEndpoint nearby : Sign) : Prop :=
  atEndpoint = zero ∨ atEndpoint = nearby

/-- Decide stability of two formal signs by their equality and zero tests. -/
public instance instDecidableStable (atEndpoint nearby : Sign) : Decidable (Sign.Stable atEndpoint nearby) := by
  unfold Sign.Stable
  infer_instance

end Purelib.Data.Sign

namespace Purelib.Data.Sign.Stable

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- Stability of two sign pairs is preserved by coordinatewise multiplication. -/
public theorem mul {a a' b b' : Sign}
    (left : Sign.Stable a a') (right : Sign.Stable b b') :
    Sign.Stable (Sign.mul a b) (Sign.mul a' b') := by
  rcases left with aZero | aEqual
  · subst a
    left
    cases b <;> rfl
  · subst a'
    rcases right with bZero | bEqual
    · subst b
      left
      cases a <;> rfl
    · subst b'
      exact Or.inr rfl

/-- Stability of a sign pair is preserved by negating both signs. -/
public theorem neg {a a' : Sign} (stable : Sign.Stable a a') :
    Sign.Stable (Sign.neg a) (Sign.neg a') := by
  rcases stable with aZero | aEqual
  · subst a
    exact Or.inl rfl
  · subst a'
    exact Or.inr rfl

end Purelib.Data.Sign.Stable

namespace Purelib.Data.Sign

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- A nonzero stable endpoint sign equals its nearby sign. -/
public theorem eq_of_stable_of_ne_zero {x y : Sign}
    (stable : Sign.Stable x y) (nonzero : x ≠ zero) : x = y :=
  stable.resolve_left nonzero

/-- A nonzero formal center pair stable against both endpoint sign pairs.

At least one center coordinate is nonzero, and each of its two coordinates is stable
separately against the corresponding lower and upper endpoint signs. -/
@[expose] public def EventCenterAdmissible
    (P Q Pₗ Qₗ Pᵣ Qᵣ : Sign) : Prop :=
  (P ≠ zero ∨ Q ≠ zero) ∧
    Sign.Stable P Pₗ ∧ Sign.Stable Q Qₗ ∧
    Sign.Stable P Pᵣ ∧ Sign.Stable Q Qᵣ

/-- Decide center admissibility by nonzero coordinates and the four endpoint stability
tests. -/
public instance instDecidableEventCenterAdmissible (P Q Pₗ Qₗ Pᵣ Qᵣ : Sign) :
    Decidable (Sign.EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ) := by
  unfold Sign.EventCenterAdmissible
  infer_instance

end Purelib.Data.Sign
