module

import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled
import Purelib.Data.Gaussian.Field

/-!
# Actual paid readings through an original quadratic root tower

The two candidates are rational and are not roots of the source. Both actual
original adjunctions are nevertheless read with their computed sufficient
budget, retaining a nonzero multiplication error below the requested one.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Request Realization Sources Sampled)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- The original normalized source with two distinct exact formal roots. -/
private def source : DensePolynomial Canonical := ⟨[1, 0, -1]⟩

/-- The original constructor supplies both coefficient adjunctions and their actual quotients. -/
private def tower : Tower Canonical inferInstance inferInstance source :=
  Tower.prepare source (by decide +kernel) 1 (by decide +kernel)

/-- Every original parameter layer is fixed before selecting the candidates. -/
private def parameters : Parameters tower Norm.weight 1 1 :=
  Parameters.prepare tower Norm.weight 1 1 (by decide) (by decide)

/-- The final error target determines both original sufficient stage requests. -/
private def request : Request parameters 1 := Request.prepare parameters 1 (by decide)

/-- The original unit leading coefficient supplies every same original stage's leading invariant. -/
private theorem leading : Tower.Leading tower id 1 :=
  Tower.Leading.ofSource tower id 1 (by decide +kernel) (by decide +kernel) rfl rfl (fun _ _ => rfl)

/-- One original inverse and the same backward budget determine all source targets before observations. -/
private def sourceRequests : Sources request.budget leading 1 request.tolerance :=
  Sources.prepare request.budget leading 1 request.tolerance (by decide) request.positive

/-- The cached inverse, scale, complete target count and active terminal cap have their expected values. -/
private theorem source_requests_compute : sourceRequests.coefficientInverse = 1 ∧
    sourceRequests.inverseNorm = 1 ∧ sourceRequests.scale = 1 / 2 ∧ sourceRequests.targets.length = 2 ∧
      sourceRequests.targets[1]'(by decide +kernel) = request.tolerance := by decide +kernel

/-- A strictly interior rational candidate with a small, nonzero original source residual. -/
private def candidate : Canonical := ⟨1 - 1 / (2 : Rational) ^ 64, 0⟩

/-- The same original polynomial evaluation supplies the actual first column's residual. -/
private def residual : Rational := Norm.Basic.normSq (source.eval candidate)

/-- The original source is divided once at each actual candidate in its original order. -/
private def expansion : Interpolation.Expansion source [candidate, -candidate] :=
  Interpolation.Expansion.prepare source [candidate, -candidate]

/-- The original cached schedule's scalar readback avoids unfolding its whole dependent record in later bounds. -/
private theorem source_initial : sourceRequests.schedule.val.initial = request.tolerance / 4 := by decide +kernel

/-- Two scalar payments extend to the same original ordered pair without inspecting a dependent request. -/
private theorem pair_at_bound (value : Canonical → Rational) (candidate : Canonical) (bound : Rational)
    (forward : value candidate ≤ bound) (backward : value (-candidate) ≤ bound) :
    ∀ point ∈ [candidate, -candidate], value point ≤ bound := by
  intro point member
  cases member with
  | head => exact forward
  | tail _ member =>
      cases member with
      | head => exact backward
      | tail _ member => cases member

/-- Both original samples pay the same computed initial tolerance. -/
private theorem source_samples : ∀ point ∈ [candidate, -candidate],
    Norm.Basic.normSq (source.eval point) ≤ sourceRequests.schedule.val.initial := by
  intro point member
  have bounded := pair_at_bound (fun point => Norm.Basic.normSq (source.eval point)) candidate (request.tolerance / 4)
    (by decide +kernel) (by decide +kernel) point member
  exact source_initial.symm ▸ bounded

/-- The complete schedule pays both same original synthetic quotients without a replacement division. -/
private theorem sourcePayments : expansion.Pays sourceRequests.targets :=
  expansion.pays sourceRequests.separationPositive sourceRequests.schedule.val sourceRequests.schedule.property
    (by decide +kernel) (by decide +kernel) source_samples

/-- The actual first source payment supplies its same original generator request. -/
private theorem first_generator_paid : residual ≤ request.tolerance := by
  have bounded := sourceRequests.scaled_residual_le request.positive.le sourcePayments.head_eval
  have unit : sourceRequests.inverseNorm = 1 := source_requests_compute.right.left
  rewrite [unit, mul_one] at bounded
  exact bounded

/-- The actual original source expansion automatically constructs every paid original stage and correspondence. -/
private def sampled : Sampled request.budget GaussianReading.identity rfl [candidate, -candidate]
    (request.tolerance * sourceRequests.inverseNorm) :=
  sourceRequests.realize GaussianReading.identity rfl source
    (Purelib.Polynomial.Dense.Map.map_id source).symm
    [candidate, -candidate] expansion
    (pair_at_bound Norm.Basic.normSq candidate 1 (by decide +kernel) (by decide +kernel)) sourcePayments

/-- All subsequent checks consume the same automatically assembled original endpoint. -/
private def realized : Realization request.budget GaussianReading.identity rfl := sampled.realization

/-- This actual two-stage construction has the same fixed final gain and a genuinely positive error. -/
private theorem endpoint_computes : realized.finalReading.gain = 16 ∧ 0 < realized.finalReading.error := by
  decide +kernel

/-- The pre-observation budget proves the same cached endpoint satisfies the requested strict error bound. -/
private theorem endpoint_sufficient : realized.finalReading.error < 1 :=
  realized.error_lt request.positive

/-- All original embedded Gaussian coefficients retain their initial exact readings. -/
private theorem original_coefficients (coefficient : Canonical) :
    realized.finalReading.read (tower.embed coefficient) = coefficient := realized.final_read_embed coefficient

/-- Read both actual original formal roots from their original ordered final tower blocks. -/
private theorem original_roots_compute :
    realized.finalReading.read (tower.blocks[0]'(by decide +kernel)).point = candidate ∧
      realized.finalReading.read (tower.blocks[1]'(by decide +kernel)).point = -candidate := by decide +kernel

/-- The observed candidates are not silently promoted to exact roots of the original polynomial. -/
private theorem observed_defect_nonzero : residual ≠ 0 := by decide +kernel

end TestPurelib.Polynomial.Dense.Roots.Tower.Reading
