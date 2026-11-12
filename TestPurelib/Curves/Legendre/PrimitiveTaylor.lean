module

public import TestPurelib.Curves.Legendre.PeriodVariation.Sampling
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Operational
public import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.Operational
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor
import Purelib.Curves.Legendre.Paths
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Cast

/-! # Uniform spatial expansions of the original Legendre primitives

At parameter three halves the fixed spatial points two and fifteen eighths
have radicands one and 315/512. The exact original source certificate and
selected observation are reused from the paid variation fixture. One original
positive target track supplies its independently paid nonsquare observation.
Both connection primitives and the scalar residual primitive consume these
same retained readings and fixed spatial/inverse boxes.

The assertions establish primitive Taylor expansions and their quantified
remainders; a derivative-name comparison and primitive edge integral remain
separate constructions.
-/

namespace TestPurelib.Curves.Legendre.PrimitiveTaylor

open Purelib
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

/-- The original fixed parameter is reused unchanged from the paid source fixture. -/
@[expose] public def parameter : Canonical := PeriodVariation.Sampling.parameter

/-- The spatial source is the original point of that retained source certificate. -/
@[expose] public def first : Canonical := 2

/-- The distinct spatial target stays on the same positive sheet at the identical fixed parameter. -/
@[expose] public def last : Canonical := ⟨15 / 8, 0⟩

/-- The original defining Legendre polynomial retains that fixed parameter. -/
@[expose] public def polynomial := Paths.polynomial parameter

/-- The original two-point hull is the fixed spatial enclosure shared by all primitive expansions. -/
@[expose] public def box : Box := Quadratic.Polynomial.readingBox first last

/-- The fixed inverse-sheet square contains the reciprocals of both signed-window readings. -/
@[expose] public def inverseBox : Box := Box.Square.Centered.BoxTransport.centeredBox 0 3 (by decide +kernel)

/-- The original source certificate is reused as a complete cache on its unchanged scalar radicand. -/
@[expose] public def source : CertifiedSquareRoot.Certificate (polynomial.eval first) := PeriodVariation.Sampling.source

/-- The target radicand uses the original direct integer embeddings for both large closed coefficients. -/
private def targetRadicand : Canonical :=
  ⟨Fraction.Cast.fromInt 315 / Fraction.Cast.fromInt 512, 0⟩

/-- The original Legendre polynomial at the retained target has exactly that same displayed scalar radicand. -/
private theorem target_radicand : polynomial.eval last = targetRadicand := by
  unfold polynomial
  rewrite [Paths.polynomial_eval]
  decide +kernel

/-- The spatial target's original positive track is constructed by the retained cofactor-root owner. -/
public def targetOwner : SquareRootContinuationChain.Owner (polynomial.eval last) := by
  rewrite [target_radicand]
  change SquareRootContinuationChain.Owner ((Degeneration.unitPolynomial 1).eval targetRadicand)
  exact Degeneration.UnitRoot.owner 1 targetRadicand (by decide +kernel)

/-- The full certificate of that identical retained target owner is cached once. -/
@[expose] public def target : CertifiedSquareRoot.Certificate (polynomial.eval last) :=
  targetOwner.certificate targetOwner.parameterNonzero

/-- The original source accuracy and actual selected observation are reused without another process request. -/
@[expose] public def sourceSample :
    CertifiedSquareRoot.Sampling.ResidualObservation source PeriodVariation.Sampling.jet.accuracy :=
  PeriodVariation.Sampling.jet.sourceSample

/-- Request the distinct original target process once at that same actual retained accuracy. -/
@[expose] public def targetSample :
    CertifiedSquareRoot.Sampling.ResidualObservation target PeriodVariation.Sampling.jet.accuracy :=
  CertifiedSquareRoot.Sampling.request target PeriodVariation.Sampling.jet.accuracy

/-- The actual target track's initial box is the unchanged positive signed window of the source fixture. -/
public theorem target_box : targetOwner.track.initial.box = PeriodVariation.Sampling.window :=
  Degeneration.UnitRoot.owner_initial_box 1 targetRadicand (by decide +kernel)

attribute [local irreducible] source targetOwner target sourceSample targetSample

/-- The same request is exactly the fourth-order scale of the actual spatial displacement. -/
private theorem accuracy_eq : PeriodVariation.Sampling.jet.accuracy.tolerance = Norm.Basic.normSq (last - first) ^ 2 :=
  PeriodVariation.Sampling.jet.accuracy_eq.trans
    (congrArg (fun value : Fraction.Rational => value ^ 2)
      (by decide +kernel : Norm.Basic.normSq PeriodVariation.Sampling.increment = Norm.Basic.normSq (last - first)))

/-- The actual selected source reading remains inside its original signed window. -/
private theorem source_inside : PeriodVariation.Sampling.window.Contains sourceSample.reading := by
  unfold sourceSample
  exact PeriodVariation.Sampling.windowJet.sourceInside

/-- The independently selected target reading remains in its actual original tracked box. -/
private theorem target_inside : PeriodVariation.Sampling.window.Contains targetSample.reading := by
  have inside := targetSample.reading_in_initial_box targetOwner (by unfold target; rfl)
  rewrite [target_box] at inside
  exact inside

/-- Every actual reading in the retained positive window has its inverse inside the fixed inverse-sheet square. -/
public theorem inverse_inside {reading : Canonical} (inside : PeriodVariation.Sampling.window.Contains reading) :
    inverseBox.Contains reading⁻¹ := by
  have lower := PeriodVariation.Sampling.side.margin_le_normSq_sub inside
  rewrite [Gaussian.Basic.sub_zero,
    show PeriodVariation.Sampling.side.margin = (1 / 4 : Fraction.Rational) from by decide +kernel] at lower
  have inverseBound := Norm.Reciprocal.normSq_le (by decide +kernel : (0 : Fraction.Rational) < 1 / 4) lower
  apply Box.Square.Centered.centeredBox_contains_of_normSq_sub_le (by decide +kernel)
  rewrite [Gaussian.Basic.sub_zero]
  exact inverseBound.trans (by decide +kernel : (1 / 4 : Fraction.Rational)⁻¹ ≤ 3 ^ 2)

/-- The original spatial increment is in the unit-quadrance range of all three primitive expansions. -/
public theorem unit : Norm.Basic.normSq (last - first) ≤ 1 := by decide +kernel

/-- Both original connection primitives consume the same retained source/target observations and fixed boxes. -/
public def connection (coordinate : Fin 2) :=
  OddPower.Derivative.Taylor.build polynomial (Jets.Connection.Operational.primitiveForm parameter coordinate)
    box inverseBox PeriodVariation.Sampling.window PeriodVariation.Sampling.side first last source target
    PeriodVariation.Sampling.jet.accuracy sourceSample targetSample accuracy_eq
    (Quadratic.Polynomial.readingBox_first first last) (Quadratic.Polynomial.readingBox_last first last)
    source_inside target_inside (inverse_inside source_inside) (inverse_inside target_inside) unit

/-- The original scalar residual primitive reuses those same actual observations and enclosures. -/
public def residual :=
  OddPower.Derivative.Taylor.build polynomial (Jets.PicardFuchs.Operational.primitiveForm parameter)
    box inverseBox PeriodVariation.Sampling.window PeriodVariation.Sampling.side first last source target
    PeriodVariation.Sampling.jet.accuracy sourceSample targetSample accuracy_eq
    (Quadratic.Polynomial.readingBox_first first last) (Quadratic.Polynomial.readingBox_last first last)
    source_inside target_inside (inverse_inside source_inside) (inverse_inside target_inside) unit

attribute [local irreducible] connection residual

/-- Both connection primitive expansions retain the actual original source reading and their complete coefficients. -/
theorem connection_base (coordinate : Fin 2) : (connection coordinate).certificate.base =
    (Jets.Connection.Operational.primitiveForm parameter coordinate).scale *
      (Jets.Connection.Operational.primitiveForm parameter coordinate).numerator.eval first *
        sourceSample.reading⁻¹ ^ (Jets.Connection.Operational.primitiveForm parameter coordinate).denominatorExponent :=
  (connection coordinate).base_eq

/-- The scalar primitive expansion retains the distinct actual target reading and its original cube denominator. -/
theorem residual_output : residual.certificate.output =
    (Jets.PicardFuchs.Operational.primitiveForm parameter).scale *
      (Jets.PicardFuchs.Operational.primitiveForm parameter).numerator.eval last *
        targetSample.reading⁻¹ ^ (Jets.PicardFuchs.Operational.primitiveForm parameter).denominatorExponent :=
  residual.output_eq

/-- Both original connection primitives have fixed-box fourth-order bounds on their actual finite expansions. -/
theorem connection_remainder (coordinate : Fin 2) :
    Canonical.normSq ((connection coordinate).certificate.output - (connection coordinate).certificate.base -
      (last - first) * (connection coordinate).certificate.slope) ≤
        OddPower.Derivative.Taylor.ceiling polynomial (Jets.Connection.Operational.primitiveForm parameter coordinate)
          box inverseBox PeriodVariation.Sampling.side.margin * Canonical.normSq (last - first) ^ 2 :=
  (connection coordinate).remainder_le

/-- The original scalar residual primitive has its independently computed fixed-box finite remainder bound. -/
theorem residual_remainder :
    Canonical.normSq (residual.certificate.output - residual.certificate.base -
      (last - first) * residual.certificate.slope) ≤
        OddPower.Derivative.Taylor.ceiling polynomial (Jets.PicardFuchs.Operational.primitiveForm parameter)
          box inverseBox PeriodVariation.Sampling.side.margin * Canonical.normSq (last - first) ^ 2 :=
  residual.remainder_le

end TestPurelib.Curves.Legendre.PrimitiveTaylor
