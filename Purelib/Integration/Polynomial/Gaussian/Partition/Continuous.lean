module
public import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
public import Purelib.Integration.Polynomial.Rational.Continuous
public import Purelib.Integration.Polynomial.Gaussian.Continuous
public import Purelib.Polynomial.Ascending.Gaussian.RealProjection
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Constants

/-!
# Source enclosures for original compiled Gaussian polynomial segments

The original oriented displacement scales its retained Gaussian polynomial.
Its real coefficient projection supplies the finite rational source and
modulus. An existing compiled segment's original cached sample is admitted
by the computed source enclosure for the same nominal source.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Continuous

open Purelib.Approximation
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic

/-- Scale the original Gaussian coefficient table by its exact oriented segment displacement. -/
@[expose] def displaced (source : PolynomialSegment) : Ascending.Gaussian.CoefficientPolynomial :=
  Ascending.Gaussian.Arithmetic.scale source.displacement source.polynomial

/-- The exact rational real-axis source associated with the original oriented segment. -/
@[expose] def projected (source : PolynomialSegment) : Dense.Rational.Basic.CoordinatePolynomial :=
  RealProjection.dense (displaced source)

/-- Build the original finite rational source enclosure for the retained Gaussian segment. -/
@[expose] def integrate (source : PolynomialSegment) (request : AccuracyRequest) :
    SourceFrontier.Continuous.Result (Dense.Rational.Bounds.Uniform.modulus (projected source)) :=
  Rational.Continuous.integrate (projected source) request

/-- Project the imaginary coordinate of the original oriented segment through multiplication by minus i. -/
@[expose] def projectedIm (source : PolynomialSegment) : Dense.Rational.Basic.CoordinatePolynomial :=
  RealProjection.dense
    (Ascending.Gaussian.Arithmetic.scale Constants.negativeImaginaryUnit (displaced source))

/-- Construct the finite source enclosure for the original segment's imaginary integral coordinate. -/
@[expose] def integrateIm (source : PolynomialSegment) (request : AccuracyRequest) :
    SourceFrontier.Continuous.Result (Dense.Rational.Bounds.Uniform.modulus (projectedIm source)) :=
  Rational.Continuous.integrate (projectedIm source) request

/-- The original unit cell of the displaced polynomial has the original segment's exact integral sample. -/
theorem model_sample (source : PolynomialSegment) :
    (Gaussian.Continuous.model (displaced source)).integralSample = source.integralSample := by
  rw [Gaussian.Continuous.model, Cell.Basic.CellModel.exact_integralSample]
  have unit : (1 : Basic.Canonical) - 0 = 1 := by rw [Basic.sub_zero]
  rw [unit, Basic.one_mul]
  unfold displaced PolynomialSegment.integralSample
  rw [Ascending.Gaussian.Integral.definiteIntegral_scale]

/-- The rotated unit-cell sample is the imaginary coordinate of the same original segment sample. -/
theorem imaginary_model_sample (source : PolynomialSegment) :
    (Gaussian.Continuous.model
      (Ascending.Gaussian.Arithmetic.scale Constants.negativeImaginaryUnit (displaced source))).integralSample.re =
        source.integralSample.im := by
  rw [Gaussian.Continuous.model_sample_scale, model_sample, Constants.negativeImaginaryUnit_mul_re]

/-- Every original compiled segment sample's imaginary coordinate belongs to its computed source enclosure. -/
theorem compiled_im_sample_contains {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (request : AccuracyRequest) :
    (integralBound (integrateIm source request).frontier.cells).Contains compiled.sample.im := by
  let rotated := Ascending.Gaussian.Arithmetic.scale Constants.negativeImaginaryUnit (displaced source)
  have inside := Gaussian.Continuous.model_sample_contains_of_eq rotated (integrateIm source request).frontier
    (fun point _ _ => RealProjection.eval rotated point)
  rw [imaginary_model_sample, ← compiled.sample_source] at inside
  exact inside

/-- Every saved imaginary-source state contains the same original compiled segment sample's imaginary coordinate. -/
theorem compiled_im_state_contains {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (state : (Rational.Continuous.boundProcess (projectedIm source)).State) :
    ((Rational.Continuous.boundProcess (projectedIm source)).bound state).Contains compiled.sample.im := by
  let retained : SourceFrontier (projectedIm source).eval := state.1
  let rotated := Ascending.Gaussian.Arithmetic.scale Constants.negativeImaginaryUnit (displaced source)
  have inside := Gaussian.Continuous.model_sample_contains_of_eq rotated retained
    (fun point _ _ => RealProjection.eval rotated point)
  rw [imaginary_model_sample, ← compiled.sample_source] at inside
  exact inside

/-- Every original compiled segment sample belongs to the computed source enclosure of the same segment.

The supplied compilation retains its original partition, child models and
cached sample. Exact sample readback and the finite polynomial primitive
comparison relate that same sample to the source-derived enclosure. -/
theorem compiled_sample_contains {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (request : AccuracyRequest) :
    (integralBound (integrate source request).frontier.cells).Contains compiled.sample.re := by
  have inside := Gaussian.Continuous.model_sample_contains_of_eq (displaced source) (integrate source request).frontier
    (fun point _ _ => RealProjection.eval (displaced source) point)
  rw [model_sample, ← compiled.sample_source] at inside
  exact inside

/-- Every saved persistent source state contains the same original compiled segment sample. -/
theorem compiled_state_contains {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (state : (Rational.Continuous.boundProcess (projected source)).State) :
    ((Rational.Continuous.boundProcess (projected source)).bound state).Contains compiled.sample.re := by
  let retained : SourceFrontier (projected source).eval := state.1
  have inside := Gaussian.Continuous.model_sample_contains_of_eq (displaced source) retained
    (fun point _ _ => RealProjection.eval (displaced source) point)
  rw [model_sample, ← compiled.sample_source] at inside
  exact inside

/-- Independent compilations of one original segment compare through their actual source-linked enclosures. -/
theorem compiled_samples_difference_le {source : PolynomialSegment} (left right : Segment.CompiledSegment source)
    (leftRequest rightRequest : AccuracyRequest) :
    Purelib.Data.Rat.Fraction.abs (left.sample.re - right.sample.re) ≤
      (integralBound (integrate source leftRequest).frontier.cells).width +
        (integralBound (integrate source rightRequest).frontier.cells).width :=
  (SourceFrontier.commonReadings (integrate source leftRequest).frontier
    (integrate source rightRequest).frontier).answers_difference_le_of_same left.sample.re right.sample.re
      (compiled_sample_contains left leftRequest) (compiled_sample_contains right rightRequest) (fun _ _ _ => rfl)

end Purelib.Integration.Polynomial.Gaussian.Partition.Continuous

end
