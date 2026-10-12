module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Geometry.Rational.Box.Square

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Uniform refinement error along actual root-coordinate chords

The coefficient bound comes from the fixed padded preparation and holds
at every later cap-polynomial stage. It can therefore select the original
chart mesh without depending on the polynomial selected by that mesh.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data box)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {sampleBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index sampleBox}

/-- The affine line parametrization equals the original rational root-coordinate chord. -/
private theorem chord_line (first last : InverseRootPolynomial.Gaussian) (parameter : InverseRootPolynomial.Coordinate)
  :
    Affine.line first (last - first) parameter = RootRadialGeometry.chord first last parameter := by
  apply Data.Gaussian.Basic.ext <;> simp only [Affine.line, Data.Gaussian.Cast.ofCoordinate_re,
    Data.Gaussian.Cast.ofCoordinate_im,
    RootRadialGeometry.chord, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
      Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im] <;> ring1

/-- The temporary reboxing certificate is proof data; execution continues using the retained primitive and coefficient
polynomials. -/
theorem chord_increment (bounds : ReciprocalPaddedInverse.UniformBounds data) (sample : Primitives.Sample cap
  differential index sampleBox)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last))
    {left right : InverseRootPolynomial.Coordinate} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤ right ∧ right ≤ 1)
      :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval (RootRadialGeometry.chord first last right) -
      sample.primitive.value.eval (RootRadialGeometry.chord first last left)) ≤
        (2 * bounds.coefficientUpper differential * Data.Gaussian.Norm.Basic.normSq (last - first)) * (right -
          left) ^ 2 := by
  let primitive : Certificate.DensePrimitive sample.coefficient box :=
    { value := sample.primitive.value
      derivative_eq := sample.primitive.derivative_eq
      remainderBound := Taylor.denseTaylorRemainderBound sample.primitive.value ReciprocalPaddedDisk.box
      remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun startInside finishInside => by
        have estimate := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
          sample.primitive.value finishInside startInside
        rw [sample.primitive.derivative_eq] at estimate
        exact estimate }
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : InverseRootPolynomial.Coordinate) (unit : interval.Contains parameter) :
      ReciprocalPaddedDisk.box.Contains (Affine.line first (last - first) parameter) := by
    rw [Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds.chord_line]
    apply Centered.centeredBox_contains_of_normSq_sub_le
    rw [Data.Gaussian.Basic.sub_zero]
    have scalar := data.root_norm_le (data.chord_square firstInside lastInside unit)
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans (by decide : (2 : InverseRootPolynomial.Coordinate) ≤ 2 ^ 2)
  have coefficient (parameter : InverseRootPolynomial.Coordinate) (unit : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval (Affine.line first (last - first) parameter)) ≤
        bounds.coefficientUpper differential := by
    rw [Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds.chord_line]
    exact bounds.coefficient_bound sample branch (data.chord_square firstInside lastInside unit)
  have estimate := DensePrimitive.segment_increment_le primitive first (last - first) interval inside
    (bounds.coefficientUpper differential) coefficient rightUnit leftUnit
  rw [Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds.chord_line,
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds.chord_line] at estimate
  exact estimate

/-- The original cap primitive's dyadic chord-area refinement differs from its endpoint chord by the fixed padded
coefficient ceiling and fourth-order endpoint separation. -/
theorem arc_refinement (bounds : ReciprocalPaddedInverse.UniformBounds data) (sample : Primitives.Sample cap
  differential index sampleBox)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootRadialGeometry.arcArea sample.primitive.value.eval depth first last -
      BoundaryRibbon.area (sample.primitive.value.eval first) (sample.primitive.value.eval last)) ≤
        16 * bounds.coefficientUpper differential ^ 2 * Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 :=
          by
  let slope := 2 * bounds.coefficientUpper differential * Data.Gaussian.Norm.Basic.normSq (last - first)
  have nonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (bounds.coefficientUpper_nonnegative differential))
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  have estimate := DyadicAreaRefinement.dyadicArea_chord_bound
    (fun parameter => sample.primitive.value.eval (RootRadialGeometry.chord first last parameter)) (lower := 0) (upper
      := 1) nonnegative
    (fun _ _ leftUnit rightUnit => bounds.chord_increment sample branch firstInside lastInside leftUnit rightUnit)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord first last 0 = first := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im, Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im] <;> ring1
  have atOne : RootRadialGeometry.chord first last 1 = last := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im, Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im] <;> ring1
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    simp only [slope,
      show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 by decide, one_pow]
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds
