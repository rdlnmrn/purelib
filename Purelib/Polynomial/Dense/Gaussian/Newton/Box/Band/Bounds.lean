module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Band.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

section

namespace Purelib.Geometry.Rational.Box.Band.Basic.BandBox

/-- A band point and an `r²` Newton displacement are together within
`18r²` of the source anchor. -/
theorem normSq_sub_anchor_le
    {p : CoefficientPolynomial} {source : Box} {r :
      Fraction.Rational}
    (band : Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r)
    (displacementSmall : Data.Gaussian.Norm.Basic.normSq
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical} (inside : band.box.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ≤ 18 * r ^ 2 := by
  have radial := band.radial_upper inside
  have decomposition : z - source.anchor =
      (z - Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) +
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
      ring1
  rw [decomposition]
  have sumBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (z - Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
  calc
    Data.Gaussian.Norm.Basic.normSq ((z - Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) +
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (z - Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) +
          Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source -
            source.anchor)) := sumBound
    _ ≤ 2 * (8 * r ^ 2 + r ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add radial displacementSmall) (by decide)
    _ = 18 * r ^ 2 := by ring1

end Purelib.Geometry.Rational.Box.Band.Basic.BandBox

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Bounds

/-- Coarse finite Taylor budget on a radius-two Newton band. -/
def bandErrorBudget (p :
  CoefficientPolynomial) (ambient : Box)
    (r : Fraction.Rational) : Fraction.Rational :=
  Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
    Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
    (r ^ 2) ^ 2

/-- Bound the Newton error on the selected band boundary by its finite Taylor budget.

The source and target lie in the same ambient box, and the squared Newton displacement is at most the squared band
radius. -/
theorem newtonError_le_bandBudget
    {p : CoefficientPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate
      p ambient source squarefree)
    (sourceRefines : source.Refines ambient) {r : Fraction.Rational}
    (band : Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r)
    (targetRefines : band.box.Refines ambient)
    (displacementSmall : Data.Gaussian.Norm.Basic.normSq
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian.Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary band.box z) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) ≤
      bandErrorBudget p ambient r := by
  have insideAmbient := targetRefines.contains boundary.1
  have distance := band.normSq_sub_anchor_le displacementSmall boundary.1
  have distanceSquared : Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 ≤
      (18 * r ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Gaussian.Norm.Basic.normSq_nonneg (z - source.anchor)) distance 2
  have rawError := Dense.Gaussian.Newton.Box.Taylor.normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonError p source).eval z) ≤
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
          Data.Gaussian.Norm.Basic.normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * (18 * r ^ 2) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        distanceSquared (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient).le
    _ = bandErrorBudget p ambient r := by
      unfold bandErrorBudget
        Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient
      ring1

/-- The affine Newton term has the derivative-margin lower bound on the band boundary.

For a nonnegative band radius, the squared norm is at least the derivative margin times the squared radius. -/
theorem newtonLinearization_band_boundary_lower
    {p : CoefficientPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate
      p ambient source squarefree)
    {r : Fraction.Rational}
    (band : Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) r)
    (radiusNonnegative : 0 ≤ r) {z : Gaussian.Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary band.box z) :
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient * r ^ 2 ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval
        z) := by
  have radial := band.radial_lower radiusNonnegative boundary
  have productLower := Fraction.Order.Arithmetic.mul_le_mul_direct
    newton.derivativeLower radial
    (Fraction.Order.Arithmetic.sq_nonneg_direct r)
    (Gaussian.Norm.Basic.normSq_nonneg
      ((Dense.Gaussian.GCD.derivative p).eval source.anchor))
  calc
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient * r ^ 2 ≤
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval source.anchor) *
          Data.Gaussian.Norm.Basic.normSq (z - Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) :=
            productLower
    _ = Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p source).eval
      z) := by
      rw [Dense.Gaussian.Newton.Box.Linearization.newtonLinearization,
        Dense.Gaussian.Linear.Affine.affineCoordinate_eval, Gaussian.Norm.Basic.normSq_mul]

/-- Positive norm gap left after the complete band Taylor budget. -/
def bandDominanceMargin {p :
  CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box)
    (r : Fraction.Rational) : Fraction.Rational :=
  Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient * r ^ 2 -
    bandErrorBudget p ambient r

/-- The band dominance margin is positive when the doubled Taylor coefficient fits below the derivative margin.

The radius must be strictly positive; the margin subtracts the complete band error budget. -/
theorem bandDominanceMargin_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p) {r : Fraction.Rational}
    (positive : 0 < r)
    (taylorSmall :
      2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
          Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient) :
    0 < bandDominanceMargin squarefree ambient r := by
  let base := Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
    Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2
  have radiusSquarePositive :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  have basePositive : 0 < base :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct
        Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient_pos
        (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient))
      radiusSquarePositive
  have baseStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have baseBelowMargin : base < Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient :=
    baseStrict.trans_le taylorSmall
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    baseBelowMargin radiusSquarePositive
  apply Fraction.Order.Arithmetic.sub_pos_direct
  calc
    bandErrorBudget p ambient r = base * r ^ 2 := by
      dsimp only [bandErrorBudget, base]
      ring1
    _ < Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree ambient * r ^ 2 := scaled

end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Bounds

end

end
