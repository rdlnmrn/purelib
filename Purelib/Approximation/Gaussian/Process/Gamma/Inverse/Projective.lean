module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Line.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Process.Gamma.Inverse

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Constants

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Projective

/-- The normalized affine inverse chart carried after an apart decision is projectively the same tail as the preceding
homogeneous residual chart. -/
theorem normalizedInverse_tail_equivalent
    (residualProcess : Approximation.Gaussian.Process) (base : residualProcess.State)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (residualProcess.ball base)) (count : Nat)
    {state : (Scale.normalizedInverseProcess residualProcess base certificate
      count).State} {tail : Canonical}
    (possible : (Scale.normalizedInverseProcess residualProcess base certificate
      count).Possible state tail) :
    ∃ residual : Canonical,
      residualProcess.Possible base residual ∧
      (Proj.affine (Power.natPow Canonical.gamma count * tail)).Equivalent
        ⟨1, Canonical.gamma * residual⟩ := by
  rcases Scale.normalizedInverse_candidate_semantics residualProcess base
      certificate count possible with
    ⟨residual, residualPossible, residualNonzero, tailEqual⟩
  refine ⟨residual, residualPossible, ?_⟩
  let power := Power.natPow Canonical.gamma count
  let product := Canonical.gamma * residual
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Canonical.gamma Inverse.gamma_ne count
  have productNonzero : product ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct Inverse.gamma_ne residualNonzero
  have powerCancellation : power * power⁻¹ = 1 :=
    Canonical.mul_inv_cancel power powerNonzero
  have scaledIdentity : power * tail = product⁻¹ := by
    rw [tailEqual]
    change power * (power⁻¹ * product⁻¹) = product⁻¹
    calc
      power * (power⁻¹ * product⁻¹) =
          (power * power⁻¹) * product⁻¹ :=
        (Data.Gaussian.Basic.mul_assoc _ _ _).symm
      _ = product⁻¹ := by
        rw [powerCancellation,
          Data.Gaussian.Basic.one_mul]
  simp only [Proj.Equivalent, Proj.affine]
  rw [scaledIdentity]
  change product⁻¹ * product = 1 * 1
  rw [Data.Gaussian.Basic.mul_one]
  exact Canonical.inv_mul_cancel
    product productNonzero

end Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Projective

end
