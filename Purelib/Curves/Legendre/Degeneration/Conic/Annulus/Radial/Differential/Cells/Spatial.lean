module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Bounds
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry
import Purelib.Tactic.Ring

/-! # A retained scalar spatial coefficient of the SAME old curved cell

The original source, cofactor observation, residual request, selected state
and center remain indices. The uncancelled scalar coefficient is computed
once from that actual old reading, then cached for tangent/chord weighting.
No root or ordinary arithmetic-process observation is selected or relabelled.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {source : Transport.Reading actual span.lower inside}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential} {accuracy : AccuracyRequest}

/-- One scalar spatial coefficient computed from the SAME original old cell's retained cofactor observation. -/
@[expose] def Spatial (model : Model data source accuracy) : Type :=
  { value : Canonical // value = Primitive.reading (site := site) differential quarter span.lower model.sample.reading }

namespace Spatial

/-- Compute the scalar coefficient once without rerunning any root, source or arithmetic observation. -/
def build (model : Model data source accuracy) : Spatial model :=
  let value := Primitive.reading (site := site) differential quarter span.lower model.sample.reading
  ⟨value, rfl⟩

variable {model : Model data source accuracy}

/-- Read the SAME stored ordinary scalar coefficient of this original old cofactor observation. -/
@[expose] def value (retained : Spatial model) : Canonical := retained.val

/-- The entire scalar cache belongs to the original differential, point, ordinate and unchanged actual old reading. -/
theorem value_eq (retained : Spatial model) : retained.value =
    Primitive.reading (site := site) differential quarter span.lower model.sample.reading := retained.property

/-- The original independent denominator floors pay the actual cached coefficient's uniform magnitude. -/
theorem normSq_le (retained : Spatial model) : Norm.Basic.normSq retained.value ≤ Primitive.Bounds.magnitude data := by
  rewrite [retained.value_eq]
  exact Primitive.Bounds.reading_normSq_le data quarter model.regular actual.data.bound span.lower model.residual

/-- The SAME old chart center is its retained spatial scalar coefficient times the actual original oriented tangent. -/
theorem center_eq (retained : Spatial model) : model.center =
    retained.value * Tangent.baseVelocity site parameter 2 quarter span.lower := by
  rewrite [model.center_eq, retained.value_eq]
  exact (Primitive.reading_mul_velocity site parameter quarter span.lower differential model.sample.reading
    model.regular).symm

/-- The SAME original chart-cell sample is its original tangent-weighted retained spatial scalar coefficient. -/
theorem integralSample_eq (retained : Spatial model) : model.cell.integralSample =
    (Stereographic.Tangent.increment span.width *
      Tangent.baseVelocity site parameter 2 quarter span.lower) * retained.value := by
  rewrite [model.integralSample, retained.center_eq]
  change (⟨span.upper - span.lower, 0⟩ : Canonical) *
      (retained.value * Tangent.baseVelocity site parameter 2 quarter span.lower) =
    ((⟨span.upper - span.lower, 0⟩ : Canonical) *
      Tangent.baseVelocity site parameter 2 quarter span.lower) * retained.value
  ring1

/-- The unchanged ordinary evaluator Entry pays its distance from this SAME old scalar coefficient.

The Entry is an actual original full-sheet preparation, interpretation,
evaluator and factored arithmetic comparison on the identical source and
cofactor observation. Its existing finite comparison bound uses its own
arithmetic request. No old observation is reselected or assigned a smaller
radius, and the cached scalar coefficient is not used as an evaluator witness.
-/
theorem arithmetic_error_lt (retained : Spatial model) {arithmeticAccuracy : AccuracyRequest}
    (entry : Primitive.Observation.Entry differential source model.regular model.sample arithmeticAccuracy) :
    Norm.Basic.normSq (entry.value - retained.value) <
      OddPower.Observation.Factorization.errorBound differential
        (point site parameter 2 (Waist.direction quarter span.lower) positive).base
        (point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate
        (point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate⁻¹
        (1 / 16) model.sample.observation arithmeticAccuracy := by
  have paid := entry.selected.reading_close
  rewrite [Primitive.Observation.primitive_scalar_eq (site := site) (quarter := quarter) (time := span.lower)
    (positive := positive) differential model.sample.observation] at paid
  rewrite [retained.value_eq]
  exact paid

end Spatial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model
