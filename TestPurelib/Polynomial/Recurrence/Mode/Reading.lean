module

import Purelib.Polynomial.Recurrence.Mode.Reading
import Purelib.Polynomial.Recurrence.Reading
import Purelib.Algebra.Monogenic.Coordinates.Reading
import Purelib.Polynomial.Dense.Companion.Adjunction
import Purelib.Data.Gaussian.Field

/-!
# Actual finite mode readings with paid source-fixed budgets

An original quadratic coefficient algebra has zero divisors. Its retained
reading at a nonroot rational candidate has genuinely positive multiplication
error, yet pays the pre-observation finite mode request. Separate identity
readings check inside tails, startup zeroes and an empty requested horizon.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense (Companion)
open Purelib.Polynomial.Recurrence.Mode (entry window Inside)
open Purelib.Polynomial.Recurrence.Mode.Reading (Parameters Request)
open Purelib.Algebra.Monogenic (Cyclic)
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data renaming Vector → Vec
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Recurrence.Reading (values equations row_eq)

/-- The original normalized quadratic fixes its same formal root relation. -/
private def source : DensePolynomial Canonical := ⟨[1, 0, -1]⟩

/-- The actual original companion retains its unit leading coefficient. -/
private def companion := Companion.ofUnit source (by decide +kernel) 1 (by decide +kernel)

/-- The same original adjunction supplies the exact coefficient algebra and its root. -/
private def adjunction := companion.adjoin

/-- The original cyclic reading gain and radius parameters are fixed before observing a candidate. -/
private def cyclicParameters :=
  Cyclic.Element.Reading.Parameters.prepare adjunction.table Norm.weight 1 1 (by decide) (by decide)

/-- The original root and fixed gain prepare the same finite mode coefficients before observations. -/
private def parameters := Parameters.prepare (Cyclic.Element.weight adjunction.table Norm.weight)
  adjunction.root cyclicParameters.gain cyclicParameters.gain_nonnegative 0 4

/-- The positive finite mode target fixes its endpoint tolerance before observations. -/
private def request := Request.prepare parameters (1/4) (by decide +kernel)

/-- The actual retained source-fixed coefficients have independently calculated values. -/
private theorem coefficients_compute :
    parameters.coefficients ⟨0, by decide⟩ = 0 ∧ parameters.coefficients ⟨1, by decide⟩ = 8 ∧
      parameters.coefficients ⟨2, by decide⟩ = 320 ∧ parameters.coefficients ⟨3, by decide⟩ = 10752 ∧
        parameters.total = 11080 := by decide +kernel

/-- The same original coefficient algebra has actual zero divisors and is not treated as a field. -/
private theorem coefficient_zero_divisors :
    (adjunction.root - 1) * (adjunction.root + 1) = 0 ∧
      adjunction.root - 1 ≠ 0 ∧ adjunction.root + 1 ≠ 0 := by decide +kernel

/-- The observed rational is deliberately not a root of the same original source. -/
private def candidate : Canonical := ⟨1 - 1 / (2 : Rational) ^ 24, 0⟩

/-- The actual original source evaluation supplies the retained generator-column residual. -/
private def residual : Rational := Norm.Basic.normSq (source.eval candidate)

/-- The actual original cyclic constructor supplies the observed reading with a nonzero error. -/
private def reading := cyclicParameters.toReading GaussianReading.identity rfl candidate (by decide +kernel)
  residual (Norm.Basic.normSq_nonneg _) (by decide +kernel)

/-- The original formal root reads as the candidate while its exact squared relation still reads as one. -/
private theorem actual_reading :
    reading.read adjunction.root = candidate ∧ reading.read (adjunction.root ^ 2) = 1 ∧ 0 < reading.error :=
  by decide +kernel

/-- The actual observed error pays the independently precomputed original endpoint request. -/
private theorem paid : reading.error ≤ request.tolerance := by decide +kernel

/-- The retained request controls an actual original finite window coordinate at this nonmultiplicative reading. -/
private theorem actual_window :
    Norm.Basic.normSq (reading.read (window adjunction.root 0 4 ⟨3, by decide⟩) -
      window (reading.read adjunction.root) 0 4 ⟨3, by decide⟩) < 1/4 :=
  request.window_lt reading rfl paid ⟨3, by decide⟩

/-- The same actual finite mode discrepancy is genuinely nonzero. -/
private theorem actual_window_nonexact :
    reading.read (window adjunction.root 0 4 ⟨3, by decide⟩) ≠
      window (reading.read adjunction.root) 0 4 ⟨3, by decide⟩ := by decide +kernel

/-- A genuinely nonmultiplicative reading pays both errors in the same original weighted formal mode. -/
private theorem weighted_original :
    Norm.Basic.normSq (reading.read ((adjunction.root + 1) * entry adjunction.root 0 3) -
      reading.read (adjunction.root + 1) * entry (reading.read adjunction.root) 0 3) ≤
      reading.error * (2 * ((Cyclic.Element.weight adjunction.table Norm.weight).value (adjunction.root + 1) *
        (Cyclic.Element.weight adjunction.table Norm.weight).value (entry adjunction.root 0 3) +
        cyclicParameters.gain * (Cyclic.Element.weight adjunction.table Norm.weight).value (adjunction.root + 1) *
          parameters.coefficients ⟨3, by decide⟩)) :=
  parameters.weighted_entry_bound reading rfl (adjunction.root + 1) ⟨3, by decide⟩

/-- The actual weighted discrepancy is nonzero and is not silently replaced by a product of readings. -/
private theorem weighted_nonexact :
    reading.read ((adjunction.root + 1) * entry adjunction.root 0 3) ≠
      reading.read (adjunction.root + 1) * entry (reading.read adjunction.root) 0 3 := by decide +kernel

/-- A nonzero formal zero-divisor coefficient can have zero physical reading at an actual exact root. -/
private theorem formal_nonzero_physical_zero :
    adjunction.root - 1 ≠ 0 ∧
      (cyclicParameters.toReading GaussianReading.identity rfl 1 (by decide +kernel)
        0 (by decide) (by decide +kernel)).read (adjunction.root - 1) = 0 := by decide +kernel

/-- The original Gaussian source is embedded into the same actual zero-divisor coefficient algebra. -/
private def mapped := Purelib.Polynomial.Dense.Map.map (Cyclic.Element.scalar adjunction.table) source

/-- The original formal mode supplies one complete finite column in the same coefficient algebra. -/
private def originalColumn := window adjunction.root 0 6

/-- The same formal column satisfies the original source recurrence at three consecutive finite starts. -/
private theorem original_equations : Boundary.Equations mapped 3 (.cons originalColumn .nil) := by
  change ∀ (_index : Fin 3) (_column : Fin 1), _
  decide +kernel

/-- Its actual Gaussian readings retain the exact recurrence despite positive multiplication error. -/
private theorem read_equations :
    Boundary.Equations source 3 (.cons (values reading originalColumn) .nil) :=
  equations reading (Cyclic.Element.scalar_zero _) source 3 (.cons originalColumn .nil) original_equations

/-- Exact recurrence readings alternate the same two entries rather than substituting powers of the candidate. -/
private theorem read_column : values reading originalColumn =
    (.cons 1 (.cons candidate (.cons 1 (.cons candidate (.cons 1 (.cons candidate .nil)))))) := by
  apply Purelib.Data.Vector.Basic.vector_ext
  decide +kernel

/-- The original negative-power startup row also reads exactly and retains its actual nonzero input. -/
private theorem read_startup :
    reading.read (Purelib.Polynomial.Recurrence.row mapped 1 originalColumn 0) =
      Purelib.Polynomial.Recurrence.row source 1 (values reading originalColumn) 0 :=
  row_eq reading (Cyclic.Element.scalar_zero _) source 1 originalColumn 0

/-- The retained startup condition is nonzero even though all displayed tail recurrence rows vanish. -/
private theorem startup_value :
    Purelib.Polynomial.Recurrence.row source 1 (values reading originalColumn) 0 = candidate ∧
      candidate ≠ 0 := by decide +kernel

/-- The original identity reading supplies a source-fixed inside generalized-mode horizon. -/
private def insideParameters := Parameters.prepare Norm.weight (⟨1/2, 0⟩ : Canonical) 1 (by decide) 1 26

/-- The actual finite inside reading request is prepared before selecting any horizon values. -/
private def insideRequest := Request.prepare insideParameters (1/4) (by decide +kernel)

/-- The same positive discrepancy allowance supplies the computed original inside threshold. -/
private def inside := Inside.prepare (1/4) (by decide +kernel) (by decide +kernel) 1 (1/4) (by decide +kernel)

/-- The actual identity reading pays the endpoint request and the computed inside threshold for the same window. -/
private theorem inside_reading :
    Norm.Basic.normSq (GaussianReading.identity.read
      (window (⟨1/2, 0⟩ : Canonical) 1 26 ⟨24, by decide⟩)) < 1 :=
  insideRequest.inside_window_lt inside GaussianReading.identity rfl insideRequest.tolerance_positive.le
    (by decide +kernel) ⟨24, by decide⟩ (by decide +kernel)

/-- An original horizon entirely before startup retains zero mode-error coefficients. -/
private def beforeParameters := Parameters.prepare Norm.weight (⟨1/2, 0⟩ : Canonical) 1 (by decide) 7 3

/-- Before startup the same actual finite coefficient total is exactly zero. -/
private theorem before_total : beforeParameters.total = 0 := by decide +kernel

/-- The original empty finite horizon has no mode coefficients but still accepts a positive endpoint request. -/
private def emptyParameters := Parameters.prepare Norm.weight (⟨1/2, 0⟩ : Canonical) 1 (by decide) 0 0

/-- The original sufficient-width constructor handles the exact empty coefficient total. -/
private theorem empty_request :
    emptyParameters.total = 0 ∧ (Request.prepare emptyParameters 1 (by decide)).tolerance = 1/4 :=
  by decide +kernel

end TestPurelib.Polynomial.Recurrence.Mode.Reading
