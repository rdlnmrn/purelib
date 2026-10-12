module

public import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.CauchyIndex.Endpoint
import Purelib.Data.Sign.Stability

/-!
# Quarter-turn readings of formal Cauchy events

The original finite phase table and integer division by four determine a
quarter-turn correction. Nonzero stable centers certify the exact phase law.
-/

namespace Purelib.Data.Sign.CauchyIndex.Phase

open Purelib.Data.Sign.CauchyIndex

/-- Assign an integer quarter-turn phase to a formal coordinate pair.

The open half-planes receive odd phases and the real half-axes receive even phases.
Assign zero to the zero pair to keep the function total. -/
@[expose] public def signQuarterPhase (real imaginary : Sign) : Int :=
  match imaginary with
  | .positive => 1
  | .negative => -1
  | .zero =>
      match real with
      | .negative => 2
      | .zero => 0
      | .positive => 0

/-- Compute the integer correction for a finite Cauchy event's quarter-turn phase change.

The finite sign cases select the multiple of four needed to reconcile the endpoint
phase difference with the doubled event index. -/
@[expose] public def signQuarterTurns
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : Sign) : Int :=
  (Sign.eventIndex2 Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ -
      (Phase.signQuarterPhase Pᵣ Qᵣ -
        Phase.signQuarterPhase Pₗ Qₗ)) / 4

/-- The local modulo-four winding law is a finite table on the three formal signs.

Stability and a nonzero center exclude precisely the impossible rows. -/
public theorem sign_eventIndex2_eq_phase_change_add_four_mul
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : Sign)
    (nonzero : Pₑ ≠ .zero ∨ Qₑ ≠ .zero)
    (PₗStable : Sign.Stable Pₑ Pₗ)
    (QₗStable : Sign.Stable Qₑ Qₗ)
    (PᵣStable : Sign.Stable Pₑ Pᵣ)
    (QᵣStable : Sign.Stable Qₑ Qᵣ) :
    Sign.eventIndex2 Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ =
      Phase.signQuarterPhase Pᵣ Qᵣ -
        Phase.signQuarterPhase Pₗ Qₗ +
        4 * Phase.signQuarterTurns Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ := by
  revert nonzero PₗStable QₗStable PᵣStable QᵣStable
  cases Pₑ <;> cases Qₑ <;> cases Pₗ <;> cases Qₗ <;>
    cases Pᵣ <;> cases Qᵣ <;> decide

end Purelib.Data.Sign.CauchyIndex.Phase
