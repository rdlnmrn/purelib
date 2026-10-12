module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
import Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement
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
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.RootContinuation.RootRadialPairedArcs

open Purelib.Topology.Polygon

public section

/-! Uniform two-differential chord refinement on the padded root disk. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedArcArea
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Riemann.RootContinuation
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {index otherIndex : Nat} {box otherBox : Purelib.Geometry.Rational.Box}

/-- Bound the finite dyadic paired primitive area by the retained coefficient ceilings and fourth-order endpoint
separation.

Both original differential samples are evaluated on the same reciprocal chord, whose squared endpoints lie in the
original padded disk. -/
theorem paired_arc_refinement (bounds : ReciprocalPaddedInverse.UniformBounds data)
    (sample : Primitives.Sample cap differential index box)
    (otherSample : Primitives.Sample cap other otherIndex otherBox)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    let values := fun point => (⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩ :
      Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (Bilinear.arcArea values depth first last - Stokes.edgeArea (values first)
      (values last)) ≤
      16 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other))^2 *
        Data.Gaussian.Norm.Basic.normSq (last - first)^2 := by
  intro values
  let coefficient := max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)
  let slope := 2 * coefficient * Data.Gaussian.Norm.Basic.normSq (last - first)
  have nonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) ((bounds.coefficientUpper_nonnegative differential).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)))
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  have increment {d : Differentials.Basic.Differential genus} {n : Nat} {b : Rational.Box}
      (s : Primitives.Sample cap d n b) (ceiling : bounds.coefficientUpper d ≤ coefficient)
      {a b : InverseRootPolynomial.Coordinate} (aUnit : 0 ≤ a ∧ a ≤ 1) (bUnit : 0 ≤ b ∧ b ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq (s.primitive.value.eval (RootRadialGeometry.chord first last b) -
        s.primitive.value.eval (RootRadialGeometry.chord first last a)) ≤ slope * (b - a)^2 :=
    (bounds.chord_increment s branch firstInside lastInside aUnit bUnit).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ceiling (by decide))
            (Data.Gaussian.Norm.Basic.normSq_nonneg _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have estimate := DyadicPairedAreaRefinement.dyadicArea_chord_bound
    (fun parameter => values (RootRadialGeometry.chord first last parameter)) nonnegative
    (fun _ _ aUnit bUnit => by
      have firstScalar := increment sample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _) aUnit bUnit
      have secondScalar := increment otherSample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) aUnit bUnit
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord first last 0 = first := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im] <;> ring1
  have atOne : RootRadialGeometry.chord first last 1 = last := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im] <;> ring1
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    rw [show ((1 : InverseRootPolynomial.Coordinate) - 0)^4 = 1 by decide]
    dsimp only [-eq_self, -iff_self, slope, coefficient]
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedArcArea
