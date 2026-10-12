module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.State.Raw

import Purelib.Riemann.RootContinuation.ScaledRootBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Sequence
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

public section

/-!
# Quantitative differential bounds on extracted Newton bands

The derivative margin and Taylor coefficient are fixed before a radius is
requested. The canonical Newton-band extractor supplies the required Taylor
inequality without an additional successful-check premise. The resulting
radicand lower bound retains the square of the radius, and finite square-root
readings retain its linear scale.

These are estimates on the actual extracted band, not on an arbitrary thin
grid cell contained in that band. Transport to such a cell requires a separate
boundary comparison.
-/

namespace Purelib.Riemann.RootContinuation.NewtonBandBounds

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree (derivativeMargin derivativeMargin_pos)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization (newtonError newtonLinearization)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters (extractionBandTaylorCoefficient)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree (extractionRadius_taylor extractionRadius_le_eighth)
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor (denseTaylorRemainderBound)
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)

open Purelib.Data.Gaussian in
/-- Twice the squared norm of a Gaussian difference is bounded by six times the first norm plus three times the second.
-/
private theorem two_normSq_sub_le (first second : Basic.Canonical) :
    2 * normSq (first - second) ≤ 6 * normSq first + 3 * normSq second := by
  have nonnegative := Basic.Canonical.normSq_nonneg (first + first + second)
  calc
    2 * normSq (first - second) ≤
        2 * normSq (first - second) + normSq (first + first + second) :=
      le_add_of_nonneg_right nonnegative
    _ = 6 * normSq first + 3 * normSq second := by
      simp only [-eq_self, -iff_self, normSq, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im]
      ring1

/-- The exact polynomial identity expressing the retained lower-bound deficit as three weighted scalar deficits. -/
private theorem half_error_identity {R : Type*} [CommRing R] (lower linear error total : R) :
    12 * total - lower = 4 * (linear - lower) +
      2 * (6 * total + 3 * error - 2 * linear) + 3 * (lower - 2 * error) := by ring1

open Purelib.Data.Rat in
/-- A linear lower bound and half-size error bound imply the retained lower bound is at most twelve times the total norm
bound. -/
private theorem half_error_paid {lower linear error total : Fraction.Rational}
    (linearLower : lower ≤ linear) (errorUpper : 2 * error ≤ lower)
    (triangle : 2 * linear ≤ 6 * total + 3 * error) : lower ≤ 12 * total := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [half_error_identity lower linear error total]
  exact add_nonneg (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sub_nonneg_direct linearLower))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sub_nonneg_direct triangle)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sub_nonneg_direct errorUpper))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An original Gaussian linear term with a half-size error retains a twelfth of its squared-norm lower bound after
addition. -/
theorem normSq_lower_of_half_error {lower : Fraction.Rational} {linear error : Basic.Canonical}
    (linearLower : lower ≤ normSq linear) (errorUpper : 2 * normSq error ≤ lower) :
    lower ≤ 12 * normSq (linear + error) := by
  have identity : (linear + error) - error = linear := by
    apply Basic.ext <;>
      simp only [-eq_self, -iff_self, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
  have triangle := two_normSq_sub_le (linear + error) error
  rw [identity] at triangle
  exact half_error_paid linearLower errorUpper triangle

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached derivative margin, Taylor coefficient and positive scale for the original squarefree polynomial on its
retained box.

The exact scalar equations retain the original derivative and remainder owners, and the scale certificate bounds sixteen
times its square by the margin. -/
structure Profile {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
  Squarefree.Basic.SquarefreeCertificate p)
    (current : Box) where
  /-- The cached original derivative-separation margin. -/ margin : Fraction.Rational
  /-- The margin equals the original squarefree derivative bound on the retained box. -/ margin_eq : margin =
    Derivative.Separation.Squarefree.derivativeMargin squarefree current
  /-- The cached original Newton-band Taylor remainder coefficient. -/ taylor : Fraction.Rational
  /-- The cache equals the exact extraction coefficient times the original dense remainder bound. -/ taylor_eq : taylor
    = Newton.Box.Band.Parameters.extractionBandTaylorCoefficient * Bounds.Box.Taylor.denseTaylorRemainderBound p current
  /-- The retained positive scalar root-bound scale. -/ scale : Fraction.Rational
  /-- The retained scale is strictly positive. -/ scalePositive : 0 < scale
  /-- Sixteen times the retained scale squared is at most the original derivative margin. -/ squareBound : 16 * scale ^
    2 ≤ margin

constructive_injectivity Profile

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Build a positive retained scale from the original derivative margin and cache the exact Taylor bound.

The scale is one quarter of the minimum of one and the original margin, preserving its direct square-bound certificate.
-/
@[expose] def Profile.build {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (squarefree : Squarefree.Basic.SquarefreeCertificate
  p)
    (current : Box) : Profile squarefree current := by
  let margin := Derivative.Separation.Squarefree.derivativeMargin squarefree current
  let small := min 1 margin
  let scale := small / 4
  have smallPositive : 0 < small :=
    Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide) (Derivative.Separation.Squarefree.derivativeMargin_pos
      squarefree current)
  have cancel : scale * 4 = small :=
    Fraction.Field.div_mul_cancel_of_ne small 4 (by decide)
  have squareBound : 16 * scale ^ 2 ≤ margin := by
    calc
      16 * scale ^ 2 = (scale * 4) ^ 2 := by ring1
      _ = small ^ 2 := congrArg (· ^ 2) cancel
      _ = small * small := by ring1
      _ ≤ 1 * small := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _) smallPositive.le
      _ = small := _root_.one_mul _
      _ ≤ margin := Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _
  exact
    { margin := margin
      margin_eq := rfl
      taylor := Newton.Box.Band.Parameters.extractionBandTaylorCoefficient * Bounds.Box.Taylor.denseTaylorRemainderBound
        p current
      taylor_eq := rfl
      scale := scale
      scalePositive := Fraction.Order.Field.div_pos_direct smallPositive (by decide)
      squareBound := squareBound }

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- An original extracted Newton band with retained Taylor smallness and radius allowance.

The exact squarefree profile and winding-state owner index the extraction output and both scalar certificates. -/
structure Sample {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    (profile : Profile squarefree current.box) (epsilon : Fraction.Rational) where
  /-- The original Newton-band extraction output at the retained requested size. -/ output : Newton.Band.Basic.Output
    squarefree current epsilon
  /-- Twice the retained Taylor-radius error is at most the original derivative margin. -/ taylorSmall : 2 *
    (profile.taylor * output.radius ^ 2) ≤ profile.margin
  /-- The extracted radius is at most one eighth of the original requested size. -/ radius_le : output.radius ≤ (1 / 8 :
    Fraction.Rational) * epsilon

constructive_injectivity Sample

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Extract the original Newton band at a positive requested size and retain its profile-specific Taylor and radius
bounds. -/
@[expose] def Profile.request {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    (profile : Profile squarefree current.box) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) {epsilon :
      Fraction.Rational}
    (epsilonPositive : 0 < epsilon) : Sample profile epsilon := by
  let output := Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current epsilonPositive
  exact
    { output := output
      taylorSmall := by
        rw [profile.taylor_eq, profile.margin_eq]
        exact Newton.Box.Budget.Squarefree.extractionRadius_taylor squarefree current.clearance current.proper
          epsilonPositive
      radius_le := Newton.Box.Budget.Squarefree.extractionRadius_le_eighth squarefree current.box current.clearance
        epsilon }

namespace Sample

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient} {profile : Profile squarefree current.box}
  {epsilon : Purelib.Data.Rat.Fraction.Rational} (sample : Sample profile epsilon)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- On the original band boundary, the derivative margin times radius squared is at most twelve times the polynomial
norm.

The exact Newton linearization and Taylor error satisfy the retained half-error estimate at the same boundary point. -/
theorem margin_mul_radius_sq_le {z : Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box z) :
    profile.margin * sample.output.radius ^ 2 ≤ 12 * normSq (p.eval z) := by
  have linearLower := Newton.Box.Band.Bounds.newtonLinearization_band_boundary_lower sample.output.newton
    sample.output.band sample.output.radiusPositive.le boundary
  rw [← profile.margin_eq] at linearLower
  rw [Norm.Basic.normSq_eq_canonical] at linearLower
  have errorBound := Newton.Box.Band.Bounds.newtonError_le_bandBudget sample.output.newton
    sample.output.source.refinesAmbient sample.output.band (Geometry.Rational.Box.Refinement.StrictInterior.refines
      sample.output.strictCurrent)
    (by simpa only [-eq_self, -iff_self, Norm.Basic.normSq_eq_canonical] using sample.output.displacementSmall) boundary
  rw [Norm.Basic.normSq_eq_canonical] at errorBound
  have errorUpper : 2 * normSq ((Newton.Box.Linearization.newtonError p sample.output.source.box).eval z) ≤
      profile.margin * sample.output.radius ^ 2 := by
    calc
      _ ≤ 2 * Newton.Box.Band.Bounds.bandErrorBudget p current.box sample.output.radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorBound (by decide)
      _ = (2 * (profile.taylor * sample.output.radius ^ 2)) * sample.output.radius ^ 2 := by
        rw [profile.taylor_eq]
        unfold Newton.Box.Band.Bounds.bandErrorBudget
        ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        sample.taylorSmall (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have estimate := normSq_lower_of_half_error linearLower errorUpper
  have identity : (Newton.Box.Linearization.newtonLinearization p sample.output.source.box).eval z +
      (Newton.Box.Linearization.newtonError p sample.output.source.box).eval z = p.eval z := by
    rw [Newton.Box.Linearization.newtonError, Dense.Basic.DensePolynomial.eval_sub,
      Dense.Basic.DensePolynomial.eval_normalize]
    apply Basic.ext <;>
      simp only [-eq_self, -iff_self, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
  rw [identity] at estimate
  exact estimate

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
/-- The original scaled band radius squared is bounded by the polynomial norm at every retained boundary point. -/
theorem radicand_lower {z : Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary sample.output.box z) :
    (profile.scale * sample.output.radius) ^ 2 ≤ normSq (p.eval z) := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    profile.squareBound (Fraction.Order.Arithmetic.sq_nonneg_direct sample.output.radius)
  have estimate : 16 * (profile.scale * sample.output.radius) ^ 2 ≤ 16 * normSq (p.eval z) := by
    calc
      _ = (16 * profile.scale ^ 2) * sample.output.radius ^ 2 := by ring1
      _ ≤ profile.margin * sample.output.radius ^ 2 := scaled
      _ ≤ 12 * normSq (p.eval z) := sample.margin_mul_radius_sq_le boundary
      _ ≤ 16 * normSq (p.eval z) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide +kernel) (Basic.Canonical.normSq_nonneg _)
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 16)
    (by simpa only [-eq_self, -iff_self, Fraction.Field.mul_comm] using estimate) (by decide +kernel)

/-- The polynomial is nonzero at every original extracted-band boundary point. -/
theorem radicand_nonzero {z : Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary sample.output.box z) :
    p.eval z ≠ 0 := by
  have positive := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive) 2
  intro zero
  have lower := sample.radicand_lower boundary
  rw [zero, Basic.Canonical.normSq_zero] at lower
  exact (not_lt_of_ge lower) positive

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every retained sheet sample at an original band boundary point satisfies the scaled root-norm lower bound. -/
theorem root_sample_lower {z : Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary sample.output.box z)
    (sheet : Fin 2) (stage : Nat) :
    profile.scale * sample.output.radius ≤
      4 * normSq ((SquareRootSheets.approximation (sample.radicand_nonzero boundary) sheet).sample stage) :=
  ScaledRootBounds.scale_le_four_normSq (sample.radicand_lower boundary)
    (SquareRootSheets.sample_norm_lower (sample.radicand_nonzero boundary) sheet stage)

end Sample

end Purelib.Riemann.RootContinuation.NewtonBandBounds
