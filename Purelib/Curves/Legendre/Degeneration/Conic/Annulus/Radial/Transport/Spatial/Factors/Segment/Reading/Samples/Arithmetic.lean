module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Candidate
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual uniform polynomials compared with old curved scalar caches

One new original coefficient request starts from the same-state full-cubic
preparation of both old factor observations. The old uniform query is an
independent input. Signed agreement at the identical physical point links
their original coefficient processes; every displayed numerical payment
comes from actual retained observations or the original model allowance.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Reading completed time inside}
variable {unitAccuracy normalAccuracy : AccuracyRequest}
variable {samples : Samples reading unitAccuracy normalAccuracy}
variable {retained : Root samples}

/-- One original paid root observation, coefficient evaluator and arithmetic request on the same retained full root. -/
@[expose] def Arithmetic (retained : Root samples)
    (differential : OddPowerDifferential (Paths.polynomial parameter)) (accuracy : AccuracyRequest) : Type 1 :=
  Σ rootSample : { sample : CertifiedSquareRoot.Sampling.ResidualObservation retained.certificate accuracy //
      sample = CertifiedSquareRoot.Sampling.request retained.certificate accuracy },
    Σ coefficient : { value : CoherentNamed // value = differential.value (segment.pointAt time)
        retained.certificate.value retained.certificate.apart },
      Observation.Cache.Reading differential (segment.pointAt time) retained.certificate.value
        retained.certificate.apart rootSample.val.state rootSample.val.observation accuracy coefficient.val
          (anchor.seed.separation.radius ^ 2 / 4)

namespace Arithmetic

variable {differential : OddPowerDifferential (Paths.polynomial parameter)} {accuracy : AccuracyRequest}

/-- Request the new full-root and original arithmetic observations once, retaining both complete original caches. -/
def build (retained : Root samples) (differential : OddPowerDifferential (Paths.polynomial parameter))
    (accuracy : AccuracyRequest) : Arithmetic retained differential accuracy := by
  let rootSample := CertifiedSquareRoot.Sampling.request retained.certificate accuracy
  let coefficient := differential.value (segment.pointAt time) retained.certificate.value retained.certificate.apart
  have lower : ∀ {candidate : Canonical}, rootSample.observation.Possible candidate →
      anchor.seed.separation.radius ^ 2 / 4 ≤ Norm.Basic.normSq candidate := by
    intro candidate possible
    have original : retained.certificate.value.name.process.Possible rootSample.state candidate := by
      change (retained.certificate.value.name.process.observation rootSample.state).Possible candidate
      exact Eq.mp (congrArg (fun observation => observation.Possible candidate) rootSample.observation_eq) possible
    exact retained.candidate_lower original
  let numeric := Observation.Cache.request differential (segment.pointAt time) retained.certificate.value
    retained.certificate.apart rootSample.state rootSample.observation rootSample.observation_eq
    accuracy coefficient rfl (anchor.seed.separation.radius ^ 2 / 4) productFloor_positive lower
  exact ⟨⟨rootSample, rfl⟩, ⟨⟨coefficient, rfl⟩, numeric⟩⟩

variable (cached : Arithmetic retained differential accuracy)

/-- Read the identical new root-observation cache, whose candidates retain the two old factor states. -/
@[expose] def rootSample := cached.1.val

/-- Read the one original numerical coefficient evaluator retained before its request. -/
@[expose] def coefficient := cached.2.1.val

/-- Read the same actual fixed-floor arithmetic request, including its original coefficient and observation caches. -/
@[expose] def numeric := cached.2.2

/-- The new root observation is the original request on that same retained full-cubic certificate. -/
theorem rootSample_eq : cached.rootSample = CertifiedSquareRoot.Sampling.request retained.certificate accuracy :=
  cached.1.property

/-- The retained coefficient is the unchanged original productive odd-power evaluator. -/
theorem coefficient_eq : cached.coefficient = differential.value (segment.pointAt time)
    retained.certificate.value retained.certificate.apart := cached.2.1.property

variable {frame : Paths.Frame parameter} {liftedStart liftedFinish : LiftedPoint 2}
variable {lifted : LiftedCell liftedStart liftedFinish} {cell : CellModel} {fraction : Fraction.Rational}
variable (uniform : UniformObservation (Fibre.frameCurve frame) differential lifted cell fraction)
variable (samePoint : segment.pointAt time = uniform.algebraic.point)
variable (roots : NamedEquivalent retained.certificate.value.name uniform.algebraic.sheetValue.value.name)

/-- The original full-cubic square is the same finite-power identity consumed by the coefficient interpretation. -/
def identity (_cached : Arithmetic retained differential accuracy) :
    Provenance.Power.PowerIdentity retained.certificate.value 2
      ((Paths.polynomial parameter).eval (segment.pointAt time)) :=
  Provenance.Power.PowerIdentity.ofSquare retained.certificate.square

/-- Compare the SAME old uniform observation with the cached original arithmetic request at its identical point. -/
def compare :
    UniformObservation.ArithmeticComparison uniform cached.numeric.original cached.identity :=
  UniformObservation.ArithmeticComparison.build uniform cached.numeric.original cached.identity samePoint roots

variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable (bounds : Coefficient.Bounds data anchor)
variable {sourceAccuracy : AccuracyRequest}
variable (old : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot sourceAccuracy)

/-- The actual spatial, old-state-radius, new arithmetic and original model-allowance payments remain separate. -/
@[expose] def polynomialBound : Fraction.Rational :=
  2 * (2 * (Coefficient.preparedBound (sourceAccuracy := sourceAccuracy) bounds samples +
    Observation.Cache.errorBound differential (segment.pointAt time) (anchor.seed.separation.radius ^ 2 / 4)
      cached.rootSample.observation accuracy) +
    (16 * cached.numeric.original.asObservation.radius +
      4 * (Observation.comparisonRequest accuracy).tolerance + 2 * cell.localAllowance))

/-- The actual old curved scalar and original physical polynomial have an internally derived pointwise discrepancy.

The root witness of the cached new arithmetic request factors through the
identical OLD paired state. Existing scalar variation and fixed-floor
arithmetic bounds pay the first two terms. The original uniform comparison
pays the polynomial term, with its unchanged model allowance and readings.
-/
theorem polynomial_error_le
    (compared : UniformObservation.ArithmeticComparison uniform cached.numeric.original cached.identity) :
    Norm.Basic.normSq (Primitive.reading (site := site) differential quarter reference old.reading -
      Evaluation.eval cell.polynomial ⟨fraction, 0⟩) ≤
      cached.polynomialBound (sourceAccuracy := sourceAccuracy) (cell := cell) bounds := by
  have spatial := Coefficient.prepared_close bounds old samples retained cached.rootSample.reading_possible
  have arithmetic := cached.numeric.reading_close
  rewrite [Norm.Bounds.normSq_sub_symm] at arithmetic
  have first := (Norm.Bounds.normSq_sub_le_via _
    (Observation.scalarReading differential (segment.pointAt time) cached.rootSample.observation) _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct spatial arithmetic.le)
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
  exact (Norm.Bounds.normSq_sub_le_via _ cached.numeric.reading _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct first compared.polynomial_error_le)
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))

end Arithmetic

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Samples

end
