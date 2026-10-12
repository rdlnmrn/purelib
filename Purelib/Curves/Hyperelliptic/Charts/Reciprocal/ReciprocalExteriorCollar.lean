module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Symmetric.Norm
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
public import Purelib.Riemann.Paths.PreparedBoundarySegments
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

public section

/-!
# A finite clear collar on the actual inverted outer boundary

Scaled conjugation maps each original square side to a straight side of a
smaller reciprocal square. Its radial interpolation with actual inversion
stays in the coefficient-certified reciprocal disk and away from the origin.
The construction applies pointwise to the retained prepared parents, with
their original parameters and either orientation; it does not replace the
inverse of a subsegment by its endpoint chord.

Root-owner transport and primitive-integral comparison are separate from
this geometric clearance certificate.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Square

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary SameSide)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)

variable {genus : Nat} (curve : HyperellipticCurve genus)

/-- The original coefficient-derived outer square radius of the curve polynomial. -/
@[expose] def radius : Fraction.Rational := RootRadius.denseLargeSquareRadius curve.polynomial

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
/-- Cached by each `Data` consumer; this scalar is independent of the boundary point, subdivision depth and
differential. -/
@[expose] def squareScale : Fraction.Rational := (2 * radius curve ^ 2)⁻¹

/-- The coefficient-derived outer radius is strictly positive. -/
theorem radius_positive : 0 < radius curve := RootRadius.denseLargeSquareRadius_pos _

/-- The original outer radius has strictly positive square. -/
theorem radius_square_positive : 0 < radius curve ^ 2 :=
  Fraction.Order.Arithmetic.pow_pos_direct
    (radius_positive curve) 2

/-- Twice the original outer radius squared is strictly positive. -/
theorem denominator_positive : 0 < 2 * radius curve ^ 2 :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (radius_square_positive curve)

end

/-- The reciprocal square scale is strictly positive. -/
theorem squareScale_positive : 0 < squareScale curve :=
  Fraction.Order.Field.inv_pos_direct
    (denominator_positive curve)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
/-- The retained reciprocal scale cancels twice the original outer radius squared. -/
theorem scale_cancel : (2 * radius curve ^ 2) *
  squareScale curve = 1 :=
  Algebra.Field.ExplicitField.mul_inv_cancel _
    (denominator_positive curve).ne'

/-- The outer radius squared times the retained scale is exactly one half. -/
theorem radius_scale : radius curve ^ 2 * squareScale
  curve = 1 / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  calc
    _ = (2 * radius curve ^ 2) * squareScale curve := by
      ring1
    _ = 1 := scale_cancel curve
    _ = _ := by decide

end

/-- The original source squared norm multiplied by the curve-dependent reciprocal square scale. -/
@[expose] def ratio (source : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq source *
  squareScale curve

/-- The affine interpolation weight from one to the source-dependent reciprocal ratio. -/
@[expose] def weight (source : Data.Gaussian.Basic.Canonical) (stage : Fraction.Rational) : Fraction.Rational :=
  1 - stage + stage * ratio curve source

/-- Scale the original source conjugate by the curve-dependent reciprocal square scale. -/
@[expose] def chord (source : Data.Gaussian.Basic.Canonical) : Gaussian := Scale.scale
  (squareScale curve) (Data.Gaussian.Basic.conj
  source)

/-- A rational homotopy, not an assertion that the inverted side is affine. -/
@[expose] def deform (source : Data.Gaussian.Basic.Canonical) (stage : Fraction.Rational) : Gaussian :=
  Scale.scale (weight curve source stage) source⁻¹

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- An original outer-boundary point has squared norm between one and two times the outer radius squared. -/
theorem boundary_norm_bounds {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient
  curve) source) :
    radius curve ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq source ∧ Data.Gaussian.Norm.Basic.normSq source
      ≤ 2 * radius curve ^ 2 :=
  Symmetric.Norm.symmetric_boundary_norm_bounds
    (radius_positive curve).le boundary

/-- The reciprocal ratio of an original outer-boundary point lies between one half and one. -/
theorem ratio_bounds {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source) :
    1 / 2 ≤ ratio curve source ∧
      ratio curve source ≤ 1 := by
  have bounds := boundary_norm_bounds curve boundary
  constructor
  · rw [← radius_scale curve]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounds.1
      (squareScale_positive curve).le
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounds.2
      (squareScale_positive curve).le).trans_eq
        (scale_cancel curve)

/-- Interpolating between one and a value in the half-to-one interval stays in that interval.

Both endpoints and the interpolation parameter retain their weak bounds.
Direct rational translation and multiplication preserve the same two bounds. -/
private theorem affine_weight_bounds {value stage : Fraction.Rational}
    (bounds : 1 / 2 ≤ value ∧ value ≤ 1) (inside : 0 ≤ stage ∧ stage ≤ 1) :
    1 / 2 ≤ 1 - stage + stage * value ∧ 1 - stage + stage * value ≤ 1 := by
  have half : stage * (1 / 2 : Fraction.Rational) ≤ 1 / 2 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inside.2 (by decide)).trans_eq (by ring1)
  constructor
  · calc
      _ ≤ 1 - stage * (1 / 2 : Fraction.Rational) := by
        have bound := Fraction.Order.Arithmetic.sub_le_sub_left_direct half (1 : Fraction.Rational)
        exact (show (1 / 2 : Fraction.Rational) = 1 - 1 / 2 by decide).trans_le bound
      _ = 1 - stage * ((1 / 2 : Fraction.Rational) + 1 / 2) + stage * (1 / 2 : Fraction.Rational) := by ring1
      _ = 1 - stage + stage * (1 / 2 : Fraction.Rational) := by
        rw [show (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide];
        ring1
      _ ≤ _ := add_le_add (le_refl _)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounds.1 inside.1)
  · calc
      _ ≤ 1 - stage + stage * 1 := add_le_add (le_refl _)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounds.2 inside.1)
      _ = _ := by ring1

/-- Every unit-interval deformation stage retains weight between one half and one. -/
theorem weight_bounds {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    1 / 2 ≤ weight curve source stage ∧
      weight curve source stage ≤ 1 :=
  affine_weight_bounds
    (ratio_bounds curve boundary) inside

/-- A nonzero Gaussian inverse scaled by the original squared norm equals its conjugate. -/
private theorem scaled_inverse (source : Data.Gaussian.Basic.Canonical) (nonzero : source ≠ 0) :
    Scale.scale (Data.Gaussian.Norm.Basic.normSq source) source⁻¹ = Data.Gaussian.Basic.conj source :=
      by
  have positive := Data.Gaussian.Norm.Basic.normSq_pos nonzero
  rw [Data.Gaussian.Field.inv_eq]
  apply Data.Gaussian.Basic.ext
  · change Data.Gaussian.Norm.Basic.normSq source * (source.re / Data.Gaussian.Norm.Basic.normSq
      source) = source.re
    rw [_root_.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
  · change Data.Gaussian.Norm.Basic.normSq source * (-source.im / Data.Gaussian.Norm.Basic.normSq
      source) = -source.im
    rw [_root_.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- The straight reciprocal side point equals the inverse scaled by the original reciprocal ratio. -/
theorem chord_eq_scaled_inverse {source : Data.Gaussian.Basic.Canonical} (nonzero : source ≠ 0) :
    chord curve source = Scale.scale
      (ratio curve source) source⁻¹ := by
  rw [chord, ←
    scaled_inverse source nonzero]
  apply Data.Gaussian.Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im,
    ratio] <;> ring1

/-- Stage zero retains the exact original inverse point. -/
theorem deform_zero (source : Data.Gaussian.Basic.Canonical) :
  deform curve source 0 = source⁻¹ := by
  apply Data.Gaussian.Basic.ext <;> simp only [deform,
    weight, Scale.scale_re, Scale.scale_im] <;> ring1

/-- Stage one reaches the straight scaled-conjugate side point. -/
theorem deform_one {source : Data.Gaussian.Basic.Canonical} (nonzero : source ≠ 0) :
  deform curve source 1 =
  chord curve source := by
  rw [chord_eq_scaled_inverse curve nonzero]
  apply Data.Gaussian.Basic.ext <;> simp only [deform,
    weight, Scale.scale_re, Scale.scale_im] <;> ring1

/-- The displayed homotopy really interpolates between the inverse point and the scaled-conjugate side, with the
original stage parameter. -/
theorem deform_affine {source : Data.Gaussian.Basic.Canonical} (nonzero : source ≠ 0) (stage : Fraction.Rational) :
    deform curve source stage = source⁻¹ + Scale.scale
      stage (chord curve source - source⁻¹) := by
  rw [chord_eq_scaled_inverse curve nonzero]
  apply Data.Gaussian.Basic.ext <;>
    simp only [deform,
      weight, Scale.scale_re, Scale.scale_im,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1

/-- Scaled conjugation preserves the original affine segment parameter. -/
theorem chord_affine (first last : Data.Gaussian.Basic.Canonical) (parameter : Fraction.Rational) :
    chord curve (first + Scale.scale parameter (last -
      first)) =
      chord curve first + Scale.scale parameter
        (chord curve last -
        chord curve first) := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [chord, Data.Gaussian.Basic.conj,
      Scale.scale_re, Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- A corner-norm source remains fixed at its inverse throughout the deformation. -/
theorem corner_fixed {source : Data.Gaussian.Basic.Canonical} (corner : Data.Gaussian.Norm.Basic.normSq source
  = 2 * radius curve ^ 2) (stage : Fraction.Rational) :
    deform curve source stage = source⁻¹ := by
  have ratioOne : ratio curve source = 1 := by rw
    [ratio, corner,
    scale_cancel]
  apply Data.Gaussian.Basic.ext <;> simp only [deform,
    weight, ratioOne, Scale.scale_re, Scale.scale_im]
    <;> ring1

/-- The squared norm of an outer-boundary inverse is the reciprocal of the original squared norm. -/
theorem inverse_norm {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source) :
    Data.Gaussian.Norm.Basic.normSq source⁻¹ = (Data.Gaussian.Norm.Basic.normSq source)⁻¹ := by
  rw [Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.normSq_inv source (PreparedExteriorReciprocal.boundary_nonzero
    boundary)]

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- The inverse of every original outer-boundary point lies in the coefficient-certified reciprocal disk. -/
theorem inverse_inDisk {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source) :
    Reciprocal.Bounds.InDisk curve.polynomial source⁻¹ := by
  have nonzero := PreparedExteriorReciprocal.boundary_nonzero boundary
  change radius curve ^ 2 * Data.Gaussian.Norm.Basic.normSq source⁻¹ ≤ 1
  rw [inverse_norm curve boundary]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (boundary_norm_bounds curve boundary).1
      (Fraction.Order.Field.inv_pos_direct (Data.Gaussian.Norm.Basic.normSq_pos nonzero)).le).trans_eq
      (Algebra.Field.ExplicitField.mul_inv_cancel _ (Data.Gaussian.Norm.Basic.normSq_pos nonzero).ne')

/-- Every unit-interval deformation stage remains inside the original certified reciprocal disk. -/
theorem deform_inDisk {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    Reciprocal.Bounds.InDisk curve.polynomial (deform
      curve source stage) := by
  have weights := weight_bounds curve boundary inside
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct
    ((by decide : (0 : Fraction.Rational) ≤ 1 / 2).trans weights.1) weights.2 2
  rw [one_pow] at square
  have shrink : Data.Gaussian.Norm.Basic.normSq
    (deform curve source stage) ≤
    Data.Gaussian.Norm.Basic.normSq source⁻¹ := by
    rw [deform, Scale.normSq_scale]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square (Data.Gaussian.Norm.Basic.normSq_nonneg
      _)).trans_eq (by ring1)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shrink
    (radius_square_positive curve).le).trans
      (inverse_inDisk curve boundary)

/-- One quarter of the reciprocal square scale, retained as a uniform coordinate squared-norm floor. -/
@[expose] def coordinateLower : Fraction.Rational := (1 / 4 : Fraction.Rational) *
  squareScale curve

/-- The retained coordinate squared-norm floor is strictly positive. -/
theorem coordinateLower_positive : 0 < coordinateLower
  curve :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (squareScale_positive curve)

/-- The original coordinate floor bounds every unit-interval deformation stage away from zero. -/
theorem deform_norm_lower {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient
  curve) source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    coordinateLower curve ≤
      Data.Gaussian.Norm.Basic.normSq (deform
      curve source stage) := by
  have lowerInverse : squareScale curve ≤
    Data.Gaussian.Norm.Basic.normSq source⁻¹ := by
    rw [inverse_norm curve boundary]
    exact Fraction.Order.Field.inv_le_inv_of_pos_direct
      (Data.Gaussian.Norm.Basic.normSq_pos (PreparedExteriorReciprocal.boundary_nonzero boundary))
        (boundary_norm_bounds curve boundary).2
  have lowerSquare := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
    (weight_bounds curve boundary inside).1 2
  rw [show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide] at lowerSquare
  rw [deform, Scale.normSq_scale]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct lowerSquare lowerInverse
    (squareScale_positive curve).le
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Every unit-interval deformation of an original outer-boundary point is nonzero. -/
theorem deform_nonzero {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
      deform curve source stage ≠ 0 := by
  intro zero
  have positive := (coordinateLower_positive
    curve).trans_le (deform_norm_lower curve boundary
    inside)
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at positive
  exact (lt_irrefl (0 : Fraction.Rational)) positive

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- The retained coordinate floor is at most one. -/
theorem coordinateLower_le_one : coordinateLower curve ≤
  1 := by
  have denominator : 1 ≤ 2 * radius curve ^ 2 := by
    calc
      _ ≤ radius curve ^ 2 := Reciprocal.Bounds.radius_square_one_le _
      _ ≤ radius curve ^ 2 + radius curve ^ 2 := le_add_of_nonneg_right
        (radius_square_positive curve).le
      _ = _ := by ring1
  have inverse := Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide : (0 : Fraction.Rational) < 1) denominator
  rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide] at inverse
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct (by decide : (1 / 4 : Fraction.Rational) ≤ 1) inverse
    (squareScale_positive curve).le (by
      decide)).trans_eq (by ring1)

/-- The original leading-coefficient squared norm divided by four, times the retained coordinate floor. -/
@[expose] def radicandLower : Fraction.Rational := (Data.Gaussian.Norm.Basic.normSq
  curve.polynomial.leadingCoeff / 4) * coordinateLower
  curve

/-- The retained reciprocal radicand lower bound is strictly positive. -/
theorem radicandLower_positive : 0 < radicandLower curve
  :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (Data.Gaussian.Norm.Basic.normSq_pos (DensePolynomial.leadingCoeff_ne_zero curve.nonzero)) (by decide))
    (coordinateLower_positive curve)

/-- Both degree parities use one positive bound. In the odd case the coordinate factor is retained, rather than hidden
in a nonzero assumption. -/
theorem radicand_lower {point : Data.Gaussian.Basic.Canonical}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point)
    (coordinate : coordinateLower curve ≤
      Data.Gaussian.Norm.Basic.normSq point) :
    radicandLower curve ≤
      Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval point) := by
  have reversed := Reciprocal.Bounds.disk_lower curve.polynomial (BranchIsolation.degreePositive curve) point inside
  have leadingNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff / 4 :=
    Fraction.Order.Field.div_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  rw [HyperellipticReciprocal.polynomial_eval, Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [regular, pow_zero]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct reversed
      (coordinateLower_le_one curve)
      (coordinateLower_positive curve).le
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  · rw [branch, pow_one]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct reversed coordinate
      (coordinateLower_positive curve).le
        (leadingNonnegative.trans reversed)

/-- The reciprocal radicand satisfies the retained uniform lower bound throughout the original boundary deformation. -/
theorem deform_radicand_lower {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient
  curve) source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    radicandLower curve ≤
      Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval
      (deform curve source stage)) :=
  radicand_lower curve
    (deform_inDisk curve boundary inside)
    (deform_norm_lower curve boundary inside)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- The outer radius multiplied by the original reciprocal square scale. -/
@[expose] def innerRadius : Fraction.Rational :=
  squareScale curve * radius curve

/-- The retained reciprocal inner radius is strictly positive. -/
theorem innerRadius_positive : 0 < innerRadius curve :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (squareScale_positive curve)
    (radius_positive curve)

/-- The symmetric rational square with the retained reciprocal inner radius. -/
@[expose] def innerBox : Rational.Box := Rational.Box.symmetric
  (innerRadius curve)
  (innerRadius_positive curve).le

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
/-- Scaled conjugation maps the original ambient square into the retained inner square. -/
theorem chord_contains {source : Data.Gaussian.Basic.Canonical} (inside : (Cuts.Ambient curve).Contains source) :
    (innerBox curve).Contains
      (chord curve source) := by
  change -radius curve ≤ source.re ∧ source.re ≤ radius curve ∧
    -radius curve ≤ source.im ∧ source.im ≤ radius curve at inside
  change -(squareScale curve * radius curve) ≤
    squareScale curve * source.re ∧
    squareScale curve * source.re ≤
      squareScale curve * radius curve ∧
    -(squareScale curve * radius curve) ≤
      squareScale curve * -source.im ∧
    squareScale curve * -source.im ≤
      squareScale curve * radius curve
  have lowerRe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.1
    (squareScale_positive curve).le
  have lowerIm := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.neg_le_neg_direct inside.2.2.2)
      (squareScale_positive curve).le
  have upperIm := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.neg_le_neg_direct inside.2.2.1)
      (squareScale_positive curve).le
  refine ⟨?_, Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2.1
    (squareScale_positive curve).le, ?_, ?_⟩
  · exact (show -(squareScale curve * radius curve) =
      squareScale curve * -radius curve by ring1).trans_le
      lowerRe
  · exact (show -(squareScale curve * radius curve) =
      squareScale curve * -radius curve by ring1).trans_le
      lowerIm
  · simpa only [neg_neg] using upperIm

/-- Conjugation preserves left/right and exchanges bottom/top. Together with affine parameter preservation this records
the reversed orientation. -/
theorem chord_boundary {source : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  source) :
    Boundary.OnBoxBoundary (innerBox curve)
      (chord curve source) := by
  refine ⟨chord_contains curve boundary.1, ?_⟩
  have side := boundary.2
  change source.re = -radius curve ∨ source.re = radius curve ∨
    source.im = -radius curve ∨ source.im = radius curve at side
  change squareScale curve * source.re =
    -(squareScale curve * radius curve) ∨
    squareScale curve * source.re =
      squareScale curve * radius curve ∨
    squareScale curve * -source.im =
      -(squareScale curve * radius curve) ∨
    squareScale curve * -source.im =
      squareScale curve * radius curve
  rcases side with left | right | bottom | top
  · exact Or.inl (by rw [left]; ring1)
  · exact Or.inr (Or.inl (by rw [right]))
  · exact Or.inr (Or.inr (Or.inr (by rw [bottom]; ring1)))
  · exact Or.inr (Or.inr (Or.inl (by rw [top]; ring1)))

end

/-- Scaled conjugation reverses oriented area with the exact squared scale factor. -/
theorem chord_orientation (first last : Data.Gaussian.Basic.Canonical) :
    (chord curve first).re *
      (chord curve last).im -
      (chord curve first).im *
      (chord curve last).re =
      -(squareScale curve ^ 2) * (first.re * last.im -
        first.im * last.re) := by
  simp only [chord, Data.Gaussian.Basic.conj,
    Scale.scale_re, Scale.scale_im]
  ring1

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
/-- The outer and inner squared radii multiply to one quarter. -/
theorem innerRadius_identity : radius curve ^ 2 *
  innerRadius curve ^ 2 = 1 / 4 := by
  calc
    _ = (radius curve ^ 2 * squareScale curve) ^ 2 := by
      unfold innerRadius;
      ring1
    _ = _ := by rw [radius_scale]; decide

/-- A rational between minus a radius and that radius has square at most the radius squared.

The supplied endpoint comparisons bound its square by the maximum of
the two equal endpoint squares, which is that same radius square. -/
private theorem symmetric_square_bound {radius value : Fraction.Rational} (bounds : -radius ≤ value ∧ value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  have estimate := Rational.Box.sq_le_endpoint_max bounds.1 bounds.2
  simpa only [show (-radius) ^ 2 = radius ^ 2 by ring1, Fraction.Order.Basic.max_self] using estimate

/-- The whole retained inner square lies in the original coefficient-certified reciprocal disk. -/
theorem innerBox_inDisk {point : Data.Gaussian.Basic.Canonical} (inside :
  (innerBox curve).Contains point) :
    Reciprocal.Bounds.InDisk curve.polynomial point := by
  have realSquare := symmetric_square_bound ⟨inside.1,
    inside.2.1⟩
  have imaginarySquare := symmetric_square_bound
    ⟨inside.2.2.1, inside.2.2.2⟩
  have normUpper : Data.Gaussian.Norm.Basic.normSq point ≤ 2 *
    innerRadius curve ^ 2 :=
    (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  calc
    _ ≤ radius curve ^ 2 * (2 * innerRadius curve ^ 2)
      :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normUpper
        (radius_square_positive curve).le
    _ = 2 * (radius curve ^ 2 * innerRadius curve ^ 2)
      := by
      ring1
    _ ≤ 1 := by rw [innerRadius_identity]; decide

/-- The retained inner-square boundary satisfies the original positive coordinate floor. -/
theorem innerBoundary_coordinate_lower {point : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary
  (innerBox curve) point) :
    coordinateLower curve ≤
      Data.Gaussian.Norm.Basic.normSq point := by
  have lower := (Symmetric.Norm.symmetric_boundary_norm_bounds
    (innerRadius_positive curve).le boundary).1
  have identity : innerRadius curve ^ 2 = (1 / 2 :
    Fraction.Rational) * squareScale curve := by
    calc
      _ = (radius curve ^ 2 * squareScale curve) *
        squareScale curve := by
          unfold innerRadius;
          ring1
      _ = _ := by rw [radius_scale]
  apply le_trans _ lower
  rw [identity]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 / 4 : Fraction.Rational) ≤ 1 / 2)
    (squareScale_positive curve).le

end

/-- The straight reciprocal patch boundary is accepted directly by the existing finite box-clearance interface. No root
search or caller bound is needed, including when the patch contains the odd-degree branch at zero. -/
@[expose] def innerBoundaryClearance : Boundary.Basic.BoundaryClearance
    (HyperellipticReciprocalCurve.reciprocalCurve curve).polynomial
      (innerBox curve) where
  bound := radicandLower curve
  positive := radicandLower_positive curve
  lower := by
    intro point boundary
    have scalar := radicand_lower curve
      (innerBox_inDisk curve boundary.1)
      (innerBoundary_coordinate_lower curve boundary)
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-! The executable interface caches all coefficient-dependent arithmetic.
Point evaluation consumes the stored scale; it does not reconstruct a
coefficient radius or squarefree certificate for each rational sample. -/

set_option genInjectivity false in
/-- Cached geometry and quantitative clearance for the original reciprocal exterior collar.

Exact equations bind the stored scale, inner box and coordinate and radicand bounds to this curve; point queries reuse
those stored values. -/
structure Data where
  /-- The cached curve-dependent reciprocal square scale. -/ coefficientScale : Fraction.Rational
  /-- The cached scale equals the original coefficient-derived reciprocal square scale. -/ coefficientScale_eq :
    coefficientScale = squareScale curve
  /-- The cached reciprocal inner square. -/ box : Rational.Box
  /-- The cached square is exactly the original inner square. -/ box_eq : box =
    innerBox curve
  /-- The cached uniform coordinate squared-norm lower bound. -/ coordinateBound : Fraction.Rational
  /-- The cached coordinate bound is exactly the original collar coordinate floor. -/ coordinateBound_eq :
    coordinateBound = coordinateLower curve
  /-- The cached uniform reciprocal-radicand squared-norm lower bound. -/ radicandBound : Fraction.Rational
  /-- The cached radicand bound is exactly the original collar radicand floor. -/ radicandBound_eq : radicandBound =
    radicandLower curve

constructive_injectivity Data

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar in
/-- Compute and retain the original reciprocal collar scale, inner square and quantitative bounds once. -/
@[expose] def Data.build : Data curve :=
  let outerRadius := radius curve
  let coefficientScale := (2 * outerRadius ^ 2)⁻¹
  let coordinateBound := (1 / 4 : Fraction.Rational) * coefficientScale
  ⟨coefficientScale, rfl,
    Rational.Box.symmetric (coefficientScale * outerRadius)
      (innerRadius_positive curve).le, rfl,
    coordinateBound, rfl, (Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff / 4) *
      coordinateBound, rfl⟩

namespace Data

variable {curve}

/-- Evaluate the collar deformation using the original cached coefficient scale. -/
@[expose] def point (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) (source :
  Data.Gaussian.Basic.Canonical) (stage : Fraction.Rational) : Gaussian :=
  Scale.scale (1 - stage + stage * (Data.Gaussian.Norm.Basic.normSq source * data.coefficientScale)) source⁻¹

/-- Evaluate the straight reciprocal side using the original cached coefficient scale. -/
@[expose] def sidePoint (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) (source :
  Data.Gaussian.Basic.Canonical) : Gaussian := Scale.scale data.coefficientScale (Data.Gaussian.Basic.conj
  source)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data in
/-- The cached point evaluator equals the original collar deformation at the same source and stage. -/
theorem point_eq (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) (source :
  Data.Gaussian.Basic.Canonical) (stage : Fraction.Rational) :
    data.point source stage = Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.deform curve source stage
      := by
  unfold point
  rw [data.coefficientScale_eq]
  rfl

/-- The cached side evaluator equals the original scaled-conjugate side point. -/
theorem sidePoint_eq (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) (source :
  Data.Gaussian.Basic.Canonical) : data.sidePoint source =
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.chord curve source := by
  unfold ReciprocalExteriorCollar.Data.sidePoint
  rw [data.coefficientScale_eq]
  rfl

/-- The original cached coordinate floor is strictly positive. -/
theorem coordinateBound_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) : 0
  < data.coordinateBound := by
  rw [data.coordinateBound_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.coordinateLower_positive curve

/-- The original cached reciprocal radicand floor is strictly positive. -/
theorem radicandBound_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) : 0 <
  data.radicandBound := by
  rw [data.radicandBound_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.radicandLower_positive curve

/-- The original cached coordinate and radicand bounds hold at every retained boundary deformation stage. -/
theorem point_clearance (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) {source :
  Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    {stage : Fraction.Rational} (inside : 0 ≤ stage ∧ stage ≤ 1) :
    data.coordinateBound ≤ Data.Gaussian.Norm.Basic.normSq (data.point source stage) ∧
    data.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval
      (data.point source stage)) := by
  rw [data.coordinateBound_eq, data.radicandBound_eq, data.point_eq]
  exact ⟨deform_norm_lower curve boundary inside,
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.deform_radicand_lower curve boundary inside⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data in
/-- Construct reciprocal polynomial boundary clearance on the same cached inner square. -/
@[expose] def boundaryClearance (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) :
  Boundary.Basic.BoundaryClearance
    (HyperellipticReciprocalCurve.reciprocalCurve curve).polynomial data.box where
  bound := data.radicandBound
  positive := data.radicandBound_positive
  lower := by
    intro point boundary
    rw [data.box_eq] at boundary
    rw [data.radicandBound_eq]
    exact (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.innerBoundaryClearance curve).lower point
      boundary

/-- Stage zero is exactly the existing reciprocal sample's rational path, including for a retained parent that is a
proper subsegment of a side. -/
theorem parent_zero (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) {differential :
  Differentials.Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter : Fraction.Rational) :
    data.point (parent.edge.point parameter) 0 = ReciprocalPathSamples.point parent.model parameter := by
  rw [data.point_eq, Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.deform_zero,
    PreparedExteriorReciprocal.parentSample_point]

/-- Stage one is affine along the original prepared parameter. Its endpoints are the scaled-conjugate endpoints, not
generally the original inverses. -/
theorem parent_one (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve) {differential :
  Differentials.Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    {parameter : Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    data.point (parent.edge.point parameter) 1 =
      data.sidePoint (parent.edge.point 0) + Scale.scale parameter
        (data.sidePoint (parent.edge.point 1) - data.sidePoint (parent.edge.point 0)) := by
  rw [data.point_eq, Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.deform_one curve
    (PreparedExteriorReciprocal.parent_point_nonzero boundary inside),
    data.sidePoint_eq, data.sidePoint_eq]
  have affine : parent.edge.point parameter = parent.edge.point 0 + Scale.scale parameter
      (parent.edge.point 1 - parent.edge.point 0) := by
    change parent.edge.localSegment.pointAt parameter = parent.edge.localSegment.pointAt 0 + Scale.scale parameter
      (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0)
    rw [ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
    rfl
  rw [affine]
  exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.chord_affine curve _ _ _

/-- The cached collar bounds hold for every unit-interval parameter and stage on the original prepared boundary parent.
-/
theorem parent_clearance (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve)
  {differential : Differentials.Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    {parameter stage : Fraction.Rational} (parameterInside : 0 ≤ parameter ∧ parameter ≤ 1)
    (stageInside : 0 ≤ stage ∧ stage ≤ 1) :
    data.coordinateBound ≤ Data.Gaussian.Norm.Basic.normSq (data.point (parent.edge.point parameter) stage) ∧
    data.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval
      (data.point (parent.edge.point parameter) stage)) :=
  data.point_clearance (boundary.point parameterInside) stageInside

/-- All retained parents of an actual covered boundary segment consume the same cached collar. No new path, center,
owner, or subdivision is prepared. -/
theorem segment_clearance (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve)
  {differential : Differentials.Basic.Differential genus}
    {first last : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment curve.polynomial (Cuts.Ambient curve)
      first last}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval first)}
    {piece : PreparedPathDecomposition.CoveredSegment segment owner} {sheet : Fin 2}
    (cache : PreparedClearPathModels.ParentCache piece.path differential sheet)
    (side : PreparedBoundarySegments.SameSide (Cuts.Ambient curve) first last)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (member : parent ∈ cache.parents)
    {parameter stage : Fraction.Rational} (parameterInside : 0 ≤ parameter ∧ parameter ≤ 1)
    (stageInside : 0 ≤ stage ∧ stage ≤ 1) :
    data.coordinateBound ≤ Data.Gaussian.Norm.Basic.normSq (data.point (parent.edge.point parameter) stage) ∧
    data.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial curve).eval
      (data.point (parent.edge.point parameter) stage)) := by
  have firstInside : (Cuts.Ambient curve).Contains first := by
    simpa only [ClearSegment.pointAt_zero] using segment.pointAt_contains piece.within 0 (by decide)
  have lastInside : (Cuts.Ambient curve).Contains last := by
    simpa only [ClearSegment.pointAt_one] using segment.pointAt_contains piece.within 1 (by decide)
  exact data.parent_clearance parent
    (PreparedSegmentBoundaryGeometry.segment_parent_boundary
      cache firstInside lastInside side member) parameterInside stageInside

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
