module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.ScaledRootBounds
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Sequence
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Requested small differential readings on Newton bands

For the differential `z^k dz / y`, the squared edge displacement supplies
two powers of the radius, while the finite root denominator costs only one.
The remaining linear rate is uniform in the sheet, reading stage and points
on the chosen boundary. Its coefficient is cached before the radius request.

This module does not identify these readings with an integrated period or
with the boundary of an arbitrary contained grid cell.
-/

namespace Purelib.Riemann.RootContinuation.NewtonBandDifferentials

open Purelib.Riemann.RootContinuation.NewtonBandBounds

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)

open Purelib.Data.Rat in
/-- Cancel the positive original radius from the retained scaled differential inequality. -/
private theorem cancel_radius_bound {radius scale magnitude rate : Fraction.Rational}
    (positive : 0 < radius) (bound : (scale * radius) * magnitude ≤ rate * radius ^ 2) :
    scale * magnitude ≤ rate * radius := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := radius) _ positive
  calc
    (scale * magnitude) * radius = (scale * radius) * magnitude := by ring1
    _ ≤ rate * radius ^ 2 := bound
    _ = (rate * radius) * radius := by ring1

namespace Sample

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient} {profile : Profile squarefree current.box}
  {epsilon : Purelib.Data.Rat.Fraction.Rational} (sample : Sample profile epsilon)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- The retained scale bounds a boundary differential reading by the original box power bound times band radius.

Original endpoint containment controls displacement, the same boundary point controls its polynomial power, and the
retained root lower bound controls the quotient. -/
theorem scaled_differential_bound (exponent : Nat) {start finish z value : Basic.Canonical}
    (startInside : sample.output.box.Contains start) (finishInside : sample.output.box.Contains finish)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box z)
    (rootLower : profile.scale * sample.output.radius ≤ 4 * normSq value) :
    profile.scale * normSq (((finish - start) * z ^ exponent) / value) ≤
      (128 * current.box.normSqBound ^ exponent) * sample.output.radius := by
  have displacement := (sample.output.box.normSq_sub_le_diagonalSq finishInside startInside).trans
    (sample.output.band.diagonalSq_le sample.output.radiusPositive)
  rw [Norm.Basic.normSq_eq_canonical] at displacement
  have pointBound := Box.normSq_le_normSqBound ((Geometry.Rational.Box.Refinement.StrictInterior.refines
    sample.output.strictCurrent).contains boundary.1)
  rw [Norm.Basic.normSq_eq_canonical] at pointBound
  have numeratorBound := Fraction.Order.Arithmetic.pow_le_pow_direct (Basic.Canonical.normSq_nonneg z) pointBound
    exponent
  have powerNorm := Power.normSq_pow z exponent
  simp only [Norm.Basic.normSq_eq_canonical] at powerNorm
  have productBound := Fraction.Order.Arithmetic.mul_le_mul_direct displacement numeratorBound
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Basic.Canonical.normSq_nonneg z) exponent)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct sample.output.radius))
  have quotient := ScaledRootBounds.scaled_quotient_bound
    (Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive)
    rootLower ((finish - start) * z ^ exponent)
  apply cancel_radius_bound sample.output.radiusPositive
  calc
    _ ≤ 4 * normSq ((finish - start) * z ^ exponent) := quotient
    _ = 4 * (normSq (finish - start) * normSq z ^ exponent) := by rw [Basic.Canonical.normSq_mul, powerNorm]
    _ ≤ 4 * ((32 * sample.output.radius ^ 2) * current.box.normSqBound ^ exponent) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound (by decide)
    _ = (128 * current.box.normSqBound ^ exponent) * sample.output.radius ^ 2 := by ring1

end Sample

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached numerator and rate bounds for an exponent over the original Newton-band profile.

The numerator is the original box norm bound raised to that exponent; the rate retains the exact quotient by the
original positive scale. -/
structure DifferentialProfile {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {squarefree :
  Squarefree.Basic.SquarefreeCertificate p}
    {current : Box} (profile : Profile squarefree current) (exponent : Nat) where
  /-- The cached original box norm bound raised to the retained exponent. -/ numerator : Fraction.Rational
  /-- The numerator cache equals that exact original power bound. -/ numerator_eq : numerator = current.normSqBound ^
    exponent
  /-- The retained scalar rate controlling differential readings. -/ rate : Fraction.Rational
  /-- The rate equals 128 times the original numerator cache divided by its retained scale. -/ rate_eq : rate = (128 *
    numerator) / profile.scale

constructive_injectivity DifferentialProfile

open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cache the original exponent numerator bound and its exact scale-normalized differential rate. -/
def Profile.differential {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {squarefree
  : Squarefree.Basic.SquarefreeCertificate p}
    {current : Box} (profile : Profile squarefree current) (exponent : Nat) :
    DifferentialProfile profile exponent :=
  let numerator := current.normSqBound ^ exponent
  { numerator := numerator
    numerator_eq := rfl
    rate := (128 * numerator) / profile.scale
    rate_eq := rfl }

namespace DifferentialProfile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.Geometry.Rational.Box} {profile : Profile squarefree current} {exponent : Nat}
  (fixed : DifferentialProfile profile exponent)

open Purelib.Data.Rat
/-- The retained differential numerator bound is nonnegative. -/
theorem numerator_nonnegative : 0 ≤ fixed.numerator := by
  rw [fixed.numerator_eq]
  exact Fraction.Order.Arithmetic.pow_nonneg_direct current.normSqBound_nonneg exponent

/-- The retained differential rate is nonnegative. -/
theorem rate_nonnegative : 0 ≤ fixed.rate := by
  rw [fixed.rate_eq]
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) fixed.numerator_nonnegative)
    profile.scalePositive.le

/-- Multiplying the retained rate by the original scale gives exactly 128 times its numerator cache. -/
theorem rate_mul_scale : fixed.rate * profile.scale = 128 * fixed.numerator := by
  rw [fixed.rate_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ profile.scalePositive.ne'

end DifferentialProfile

namespace Sample

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient} {profile : Profile squarefree current.box}
  {epsilon : Purelib.Data.Rat.Fraction.Rational} (sample : Sample profile epsilon)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- A boundary quotient coefficient is bounded by the original numerator cache and positive scaled band radius. -/
theorem coefficient_bound {exponent : Nat} (fixed : DifferentialProfile profile exponent)
    {z value : Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary sample.output.box z)
    (rootLower : profile.scale * sample.output.radius ≤ 4 * normSq value) :
    normSq (z ^ exponent / value) ≤ (4 * fixed.numerator) / (profile.scale * sample.output.radius) := by
  have positive := Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive
  have quotient := ScaledRootBounds.scaled_quotient_bound positive rootLower (z ^ exponent)
  have pointBound := Box.normSq_le_normSqBound ((Geometry.Rational.Box.Refinement.StrictInterior.refines
    sample.output.strictCurrent).contains boundary.1)
  rw [Norm.Basic.normSq_eq_canonical] at pointBound
  have numeratorBound := Fraction.Order.Arithmetic.pow_le_pow_direct (Basic.Canonical.normSq_nonneg z) pointBound
    exponent
  have powerNorm := Power.normSq_pow z exponent
  simp only [Norm.Basic.normSq_eq_canonical] at powerNorm
  rw [← fixed.numerator_eq] at numeratorBound
  apply (Fraction.Order.Field.le_div_iff_pos positive).mpr
  calc
    _ = (profile.scale * sample.output.radius) * normSq (z ^ exponent / value) :=
      Fraction.Field.mul_comm _ _
    _ ≤ 4 * normSq (z ^ exponent) := quotient
    _ = 4 * normSq z ^ exponent := by rw [powerNorm]
    _ ≤ 4 * fixed.numerator :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct numeratorBound (by decide)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- The original displacement-weighted differential has norm at most the retained rate times band radius. -/
theorem differential_bound {exponent : Nat} (fixed : DifferentialProfile profile exponent)
    {start finish z value : Basic.Canonical}
    (startInside : sample.output.box.Contains start) (finishInside : sample.output.box.Contains finish)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box z)
    (rootLower : profile.scale * sample.output.radius ≤ 4 * normSq value) :
    normSq (((finish - start) * z ^ exponent) / value) ≤ fixed.rate * sample.output.radius := by
  have bound := scaled_differential_bound sample exponent startInside finishInside boundary rootLower
  rw [← fixed.numerator_eq] at bound
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := profile.scale) _ profile.scalePositive
  calc
    _ = profile.scale * normSq (((finish - start) * z ^ exponent) / value) :=
      Fraction.Field.mul_comm _ _
    _ ≤ (128 * fixed.numerator) * sample.output.radius := bound
    _ = (fixed.rate * profile.scale) * sample.output.radius := by rw [fixed.rate_mul_scale]
    _ = (fixed.rate * sample.output.radius) * profile.scale := by ring1

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
/-- The exact differential quotient using the original boundary point, displacement, sheet and root-sample stage. -/
def differentialReading (exponent : Nat) (start finish : Basic.Canonical) {z : Basic.Canonical}
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box z) (sheet : Fin 2) (stage : Nat) : Basic.Canonical :=
  ((finish - start) * z ^ exponent) /
    (SquareRootSheets.approximation (sample.radicand_nonzero boundary) sheet).sample stage

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- The retained original differential reading satisfies the profile rate-times-radius bound. -/
theorem differentialReading_bound {exponent : Nat} (fixed : DifferentialProfile profile exponent)
    {start finish z : Basic.Canonical}
    (startInside : sample.output.box.Contains start) (finishInside : sample.output.box.Contains finish)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box z) (sheet : Fin 2) (stage : Nat) :
    normSq (differentialReading sample exponent start finish boundary sheet stage) ≤ fixed.rate * sample.output.radius
      :=
  differential_bound sample fixed startInside finishInside boundary (sample.root_sample_lower boundary sheet stage)

end Sample

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A retained Newton-band request with a positive size and exact payment of the original differential target.

The sample retains the original profile, and the payment bounds its actual extracted radius by the same stored rate. -/
structure SmallDifferentialBand {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {exponent : Nat}
    (fixed : DifferentialProfile profile exponent) (target : Fraction.Rational) where
  /-- The positive size requested of the original Newton-band profile. -/ requestSize : Fraction.Rational
  /-- The retained requested size is strictly positive. -/ requestPositive : 0 < requestSize
  /-- The exact original extracted Newton-band sample for this request. -/ sample : Sample profile requestSize
  /-- The retained rate times actual extracted radius is at most the original target. -/ paid : fixed.rate *
    sample.output.radius ≤ target

constructive_injectivity SmallDifferentialBand

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Choose a positive band request paying the original differential target through the retained weighted allowance.

The exact extracted sample and radius bound transfer the allowance certificate to the stored rate-times-radius payment.
-/
def DifferentialProfile.request {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {exponent : Nat}
    (fixed : DifferentialProfile profile exponent) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) {target :
      Fraction.Rational}
    (positive : 0 < target) : SmallDifferentialBand fixed target := by
  let requestSize := Budget.Weighted.allowance target fixed.rate
  have requestPositive := Budget.Weighted.allowance_positive positive fixed.rate_nonnegative
  let sample := profile.request degreeAtLeastTwo elimination requestPositive
  have radiusBound : sample.output.radius ≤ requestSize :=
    sample.radius_le.trans (by
      calc
        (1 / 8 : Fraction.Rational) * requestSize ≤ 1 * requestSize :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) requestPositive.le
        _ = requestSize := _root_.one_mul _)
  exact
    { requestSize := requestSize
      requestPositive := requestPositive
      sample := sample
      paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusBound fixed.rate_nonnegative).trans
        (Budget.Weighted.mul_allowance_le positive.le fixed.rate_nonnegative) }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Every original reading in the retained small differential band satisfies its exact target. -/
theorem SmallDifferentialBand.bound {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {exponent : Nat}
    {fixed : DifferentialProfile profile exponent} {target : Fraction.Rational}
    (small : SmallDifferentialBand fixed target) {start finish z : Basic.Canonical}
    (startInside : small.sample.output.box.Contains start) (finishInside : small.sample.output.box.Contains finish)
    (boundary : Box.Boundary.OnBoxBoundary small.sample.output.box z) (sheet : Fin 2) (stage : Nat) :
    normSq (Sample.differentialReading small.sample exponent start finish boundary sheet stage) ≤ target :=
  (Sample.differentialReading_bound small.sample fixed startInside finishInside boundary sheet stage).trans small.paid

end Purelib.Riemann.RootContinuation.NewtonBandDifferentials
