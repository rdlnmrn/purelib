module

public import Purelib.Data.Sign.CauchyIndex.Endpoint
public import Purelib.Data.Sign.Stability
import Purelib.Algebra.Ring.Int
import Purelib.Tactic.Ring

/-!
# Two-sided formal Cauchy contributions

Subtract the two retained one-sided readings to obtain an event contribution.
Stable nonzero centers retain that exact integer contribution.
-/

namespace Purelib.Data.Sign

/-- Net doubled contribution of one isolated two-sided event.

The displayed center fixes the same denominator-zero test for both one-sided contributions. Their subtraction retains
the signed orientation of the two endpoints. -/
@[expose] public def eventIndex2
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : Sign) : Int :=
  Sign.leftEndpointIndex2 Pₑ Qₑ Pᵣ Qᵣ -
    Sign.leftEndpointIndex2 Pₑ Qₑ Pₗ Qₗ

/-- Re-centering a formal event at its displayed left endpoint leaves exactly the
one-sided contribution toward the right endpoint.

The contribution from an endpoint to itself is zero. The retained subtraction therefore leaves the one-sided
contribution toward the other endpoint. -/
public theorem eventIndex2_self_left
    (P Q Pᵣ Qᵣ : Sign) :
    Sign.eventIndex2 P Q P Q Pᵣ Qᵣ =
      Sign.leftEndpointIndex2 P Q Pᵣ Qᵣ := by
  cases P <;> cases Q <;> cases Pᵣ <;> cases Qᵣ <;> decide

/-- The corresponding right-endpoint statement after reversing orientation.

The self contribution at the right endpoint is zero. Reversing the signed subtraction leaves the one-sided contribution
toward the left endpoint. -/
public theorem neg_eventIndex2_self_right
    (P Q Pₗ Qₗ : Sign) :
    -Sign.eventIndex2 P Q Pₗ Qₗ P Q =
      Sign.leftEndpointIndex2 P Q Pₗ Qₗ := by
  cases P <;> cases Q <;> cases Pₗ <;> cases Qₗ <;> decide

/-- The event index is independent of which nonzero stable finite sign pair is used as
its formal center.

This is an exhaustive statement about three explicit signs, not a choice of a point
or root. -/
public theorem eventIndex2_eq_of_stable
    (P Q P' Q' Pₗ Qₗ Pᵣ Qᵣ : Sign)
    (first : Sign.EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ)
    (second : Sign.EventCenterAdmissible P' Q' Pₗ Qₗ Pᵣ Qᵣ) :
    Sign.eventIndex2 P Q Pₗ Qₗ Pᵣ Qᵣ =
      Sign.eventIndex2 P' Q' Pₗ Qₗ Pᵣ Qᵣ := by
  by_cases qZero : Q = zero
  · have pNonzero : P ≠ zero := first.1.resolve_right (fun h => h qZero)
    have leftP : P = Pₗ := first.2.1.resolve_left pNonzero
    have rightP : P = Pᵣ := first.2.2.2.1.resolve_left pNonzero
    by_cases q'Zero : Q' = zero
    · have p'Nonzero : P' ≠ zero := second.1.resolve_right (fun h => h q'Zero)
      have leftP' : P' = Pₗ := second.2.1.resolve_left p'Nonzero
      have equalP : P = P' := leftP.trans leftP'.symm
      subst Q
      subst Q'
      subst P'
      rfl
    · have leftQ : Q' = Qₗ := second.2.2.1.resolve_left q'Zero
      have rightQ : Q' = Qᵣ := second.2.2.2.2.resolve_left q'Zero
      rw [← leftP, ← rightP, ← leftQ, ← rightQ]
      unfold eventIndex2
      repeat first
        | rewrite [leftEndpointIndex2]
        | rewrite [if_pos qZero]
        | rewrite [if_neg q'Zero]
      ring1
  · by_cases q'Zero : Q' = zero
    · have p'Nonzero : P' ≠ zero := second.1.resolve_right (fun h => h q'Zero)
      have leftP : P' = Pₗ := second.2.1.resolve_left p'Nonzero
      have rightP : P' = Pᵣ := second.2.2.2.1.resolve_left p'Nonzero
      have leftQ : Q = Qₗ := first.2.2.1.resolve_left qZero
      have rightQ : Q = Qᵣ := first.2.2.2.2.resolve_left qZero
      rw [← leftP, ← rightP, ← leftQ, ← rightQ]
      unfold eventIndex2
      repeat first
        | rewrite [leftEndpointIndex2]
        | rewrite [if_neg qZero]
        | rewrite [if_pos q'Zero]
      ring1
    · unfold eventIndex2
      repeat first
        | rewrite [leftEndpointIndex2]
        | rewrite [if_neg qZero]
        | rewrite [if_neg q'Zero]
      ring1

/-- A formal zero denominator and stable nonzero numerator represent exactly the change
of the first signed-chain jump.

The nonzero numerator sign is the same at both endpoints. The two endpoint denominator signs determine the exact
difference of the original formal sign jumps. -/
public theorem eventIndex2_of_stableNumerator
    (P Qₗ Qᵣ : Sign) (PNonzero : P ≠ zero) :
    Sign.eventIndex2 P zero P Qₗ P Qᵣ =
      (jump Qₗ P : Int) - jump Qᵣ P := by
  cases P
  · cases Qₗ <;> cases Qᵣ <;> decide
  · exact (PNonzero rfl).elim
  · cases Qₗ <;> cases Qᵣ <;> decide

end Purelib.Data.Sign
