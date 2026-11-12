module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedArcArea
import Purelib.Integration.Path.Dyadic.DyadicSteps
public import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-! The even cap uses physical reciprocal coordinates, not sheet signs.
Its chord error is uniform in the cap sample index. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.RootContinuation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds (Data boundingBox boundingBox_contains)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {differential other : Differentials.Basic.Differential genus} {index otherIndex : Nat} {box otherBox :
    Rational.Box}

/-- Every convex point of the retained endpoint chord stays within the original root disk. -/
private theorem chord_inside {first last : Gaussian.Basic.Canonical}
    (firstInside : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Reciprocal.Bounds.InDisk curve.polynomial last)
    {parameter : Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    Reciprocal.Bounds.InDisk curve.polynomial (RootRadialGeometry.chord first last
      parameter) := by
  have convex : Gaussian.Norm.Basic.normSq (RootRadialGeometry.chord first last parameter) ≤
      (1 - parameter) * Gaussian.Norm.Basic.normSq first + parameter * Gaussian.Norm.Basic.normSq last
        := by
    apply Arithmetic.le_of_sub_nonneg_direct
    exact (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct unit.1
      (Arithmetic.sub_nonneg_direct unit.2))
      (Gaussian.Norm.Basic.normSq_nonneg (last - first))).trans_eq (by
        simp only [RootRadialGeometry.chord, Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self]
        ring1)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct convex
    (Arithmetic.sq_nonneg_direct (Bounds.RootRadius.denseLargeSquareRadius
      curve.polynomial))
  have endpoints := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside (Arithmetic.sub_nonneg_direct
      unit.2))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside unit.1)
  exact scaled.trans ((by ring1 :
    Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
      ((1 - parameter) * Gaussian.Norm.Basic.normSq first + parameter * Gaussian.Norm.Basic.normSq
        last) =
      (1 - parameter) * (Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
        Gaussian.Norm.Basic.normSq first) +
        parameter * (Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
          Gaussian.Norm.Basic.normSq last)).trans_le
      (endpoints.trans_eq (by ring1)))

/-- The regular order-zero coefficient is bounded by its retained inverse-root ceiling. -/
theorem regular_coefficient_bound (regular : Data cap)
    (sample : Cap.Primitives.Sample cap differential index box)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) {point :
      Gaussian.Basic.Canonical}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Gaussian.Norm.Basic.normSq (sample.coefficient.eval point) ≤ regular.inverseUpper := by
  rw [sample.coefficient_eq, sample.pulledInverse_eq, sample.inverse_eq]
  simp only [Cap.Primitives.coefficient,
    Cap.Primitives.point,
    Cap.Primitives.degree, unramified, Nat.zero_add, Nat.one_mul, pow_one,
    Nat.cast_one, Ring.Multiplication.neg_mul, one_mul, Gaussian.Norm.Basic.normSq_neg,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, -eq_self, -iff_self]
  have numerator := Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg point)
    (Reciprocal.Bounds.disk_unit_bound inside)
    (HyperellipticReciprocal.reversedDifferential differential).exponent
  rw [one_pow] at numerator
  exact (Arithmetic.mul_le_mul_direct numerator (regular.inverse_bound index inside)
    (Gaussian.Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Coordinate) ≤ 1)).trans_eq (Fraction.Field.one_mul _)

/-- The retained chord equals the affine line with the same original endpoints. -/
private theorem chord_line (first last : Gaussian.Basic.Canonical) (parameter :
  Coordinate) :
    Rational.Affine.line first (last - first) parameter = RootRadialGeometry.chord
      first last parameter := by
  apply Gaussian.Basic.ext <;> simp only [Rational.Affine.line, Gaussian.Cast.ofCoordinate_re,
    Gaussian.Cast.ofCoordinate_im, RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
    Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Scale.scale_re,
      Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1

/-- The actual regular primitive increment along the original endpoint chord satisfies the retained slope bound. -/
theorem regular_chord_increment (regular : Data cap)
    (sample : Cap.Primitives.Sample cap differential index box)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) {first last :
      Gaussian.Basic.Canonical}
    (firstInside : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Reciprocal.Bounds.InDisk curve.polynomial last)
    {left right : Coordinate} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤
      right ∧ right ≤ 1) :
    Gaussian.Norm.Basic.normSq (sample.primitive.value.eval (RootRadialGeometry.chord first
      last right) -
      sample.primitive.value.eval (RootRadialGeometry.chord first last left)) ≤
        (2 * regular.inverseUpper * Gaussian.Norm.Basic.normSq (last - first)) * (right - left) ^ 2 := by
  let primitive : Primitive.Certificate.DensePrimitive sample.coefficient boundingBox :=
    { value := sample.primitive.value
      derivative_eq := sample.primitive.derivative_eq
      remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound sample.primitive.value
        boundingBox
      remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun startInside finishInside => by
        have estimate := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
          sample.primitive.value finishInside startInside
        rw [sample.primitive.derivative_eq] at estimate
        exact estimate }
  let interval : Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : Coordinate) (unit : interval.Contains parameter) :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox.Contains (Rational.Affine.line first (last - first)
        parameter) := by
    rw [chord_line]
    exact boundingBox_contains
      (chord_inside firstInside lastInside unit)
  have coefficient (parameter : Coordinate) (unit : interval.Contains parameter) :
      Gaussian.Norm.Basic.normSq (sample.coefficient.eval (Rational.Affine.line first (last - first)
        parameter)) ≤ regular.inverseUpper := by
    rw [chord_line]
    exact regular_coefficient_bound regular sample
      unramified (chord_inside firstInside
      lastInside unit)
  have estimate := Primitive.Segment.Bounds.DensePrimitive.segment_increment_le primitive first (last -
    first) interval inside
    regular.inverseUpper coefficient rightUnit leftUnit
  rw [chord_line,
    chord_line] at estimate
  exact estimate

open Purelib.Integration in
/-- The two original regular polynomial arc increments satisfy the retained inverse-root fourth-power distance bound at
any shared sample stage and radial depth. -/
theorem regular_paired_arc_refinement (regular : Data cap)
    (sample : Cap.Primitives.Sample cap differential index box)
    (otherSample : Cap.Primitives.Sample cap other otherIndex otherBox)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) {first last :
      Gaussian.Basic.Canonical}
    (firstInside : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Reciprocal.Bounds.InDisk curve.polynomial last) (depth : Nat) :
    let values := Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample
    Gaussian.Norm.Basic.normSq (RootRadialPairedArcs.Bilinear.arcArea values depth first last
      - Topology.Polygon.Stokes.edgeArea (values first) (values last)) ≤
      16 * regular.inverseUpper ^ 2 * Gaussian.Norm.Basic.normSq (last - first) ^ 2 := by
  intro values
  let slope := 2 * regular.inverseUpper * Gaussian.Norm.Basic.normSq (last - first)
  have nonnegative : 0 ≤ slope := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) regular.inverseUpper_positive.le)
      (Gaussian.Norm.Basic.normSq_nonneg _)
  have estimate := Path.Dyadic.DyadicPairedAreaRefinement.dyadicArea_chord_bound
    (fun parameter => values (RootRadialGeometry.chord first last parameter)) nonnegative
    (fun a b aUnit bUnit => by
      constructor
      · change normSq
          (sample.primitive.value.eval (RootRadialGeometry.chord first last b) -
            sample.primitive.value.eval (RootRadialGeometry.chord first last a)) ≤ slope * (b - a) ^ 2
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
        exact regular_chord_increment regular sample unramified firstInside lastInside aUnit bUnit
      · change normSq
          (otherSample.primitive.value.eval (RootRadialGeometry.chord first last b) -
            otherSample.primitive.value.eval (RootRadialGeometry.chord first last a)) ≤ slope * (b - a)
              ^ 2
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
        exact regular_chord_increment
          regular otherSample unramified firstInside lastInside aUnit bUnit)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord first last 0 = first := by
    apply Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1
  have atOne : RootRadialGeometry.chord first last 1 = last := by
    apply Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    rw [show ((1 : Coordinate) - 0) ^ 4 = 1 by decide]
    dsimp only [slope, -eq_self, -iff_self]
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)

variable {genus count otherCount depth floor index : Nat} {curve : Basic.HyperellipticCurve genus}
  {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData : Data otherPatch otherCount}
  {cover : UniformReciprocalCover.Cover data} {otherCover :
    UniformReciprocalCover.Cover otherData}
  {interval : UniformReciprocalCommonCover.CommonInterval cover otherCover} {regular :
    Disk.RegularBounds.Data cap}
  {geometry : Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth} {target :
    Coordinate}
  {prepared : Disk.CommonChartSources.SourceChartRequest regular geometry target floor}
  {box otherBox : Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box}
  {otherSample : Cap.Primitives.Sample cap other index otherBox}
  {firstComparison : Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Disk.ArcSamples.Data regular interval.second.cell}
  {first : Disk.ArcSamples.Sample firstComparison sample}
  {second : Disk.ArcSamples.Sample secondComparison otherSample}

/-- The finite paired polynomial arc area on the original physical reciprocal mesh vertices. -/
@[expose] def regularArcArea (geometry : Disk.CommonChartPaths.ChartGeometry (cap :=
  cap) interval depth)
    (sample : Cap.Primitives.Sample cap differential index box)
    (otherSample : Cap.Primitives.Sample cap other index otherBox) (radialDepth : Nat) :
      Gaussian :=
  FiniteSum.Fin.sumFin (fun edge : Fin geometry.tail.length => RootRadialPairedArcs.Bilinear.arcArea
    (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) radialDepth
    (parent.edge.point (SourceChartRequest.Parameter (geometry
      := geometry) edge.castSucc))⁻¹
    (parent.edge.point (SourceChartRequest.Parameter (geometry
      := geometry) edge.succ))⁻¹)

/-- A mesh-only error: neither the sampled cap coefficients nor the radial
refinement depth enters this bound. -/
@[expose] def regularArcError (regular : Disk.RegularBounds.Data cap)
    (geometry : Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :
      Coordinate :=
  (geometry.tail.length : Coordinate) * FiniteSum.Fin.sumFin (fun edge : Fin
    geometry.tail.length =>
    16 * regular.inverseUpper ^ 2 * Gaussian.Norm.Basic.normSq
      ((parent.edge.point (SourceChartRequest.Parameter
        (geometry := geometry) edge.succ))⁻¹ -
        (parent.edge.point (SourceChartRequest.Parameter
          (geometry := geometry) edge.castSucc))⁻¹) ^ 2)

/-- A finite rational sum of nonnegative terms is nonnegative. -/
private theorem sumFin_nonnegative {n : Nat} (values : Fin n → Coordinate)
    (positive : ∀ i, 0 ≤ values i) : 0 ≤ FiniteSum.Fin.sumFin values := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact add_nonneg (positive 0) (ih _ (fun i => positive i.succ))

/-- The original mesh-only regular arc error is nonnegative. -/
theorem regularArcError_nonnegative (regular : Disk.RegularBounds.Data cap)
    (geometry : Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) : 0 ≤
      regularArcError regular
      geometry :=
  Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (sumFin_nonnegative _ (fun edge
      => Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Coordinate) ≤ 16) (Arithmetic.sq_nonneg_direct
        regular.inverseUpper))
      (Arithmetic.sq_nonneg_direct (Gaussian.Norm.Basic.normSq
        ((parent.edge.point (SourceChartRequest.Parameter
          (geometry := geometry) edge.succ))⁻¹ -
          (parent.edge.point (SourceChartRequest.Parameter
            (geometry := geometry) edge.castSucc))⁻¹)))))

/-- The difference of two nonzero Gaussian inverses equals their reversed difference divided by the original product. -/
private theorem inverse_difference {a b : Gaussian.Basic.Canonical} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) * a⁻¹ * b⁻¹ := by
  open Purelib.Data.Gaussian.Basic.Canonical in
  have ca : a⁻¹ * a = 1 := by rw [Gaussian.Field.inv_eq]; exact Gaussian.Field.inv_mul a ha
  open Purelib.Data.Gaussian.Basic.Canonical in
  have cb : b⁻¹ * b = 1 := by rw [Gaussian.Field.inv_eq]; exact Gaussian.Field.inv_mul b hb
  apply Gaussian.Field.mul_right_cancel_of_ne
    (Gaussian.Field.mul_ne_zero_direct ha hb)
  calc
    _ = (a⁻¹ * a) * b - (b⁻¹ * b) * a := by ring1
    _ = b - a := by rw [ca, cb]; ring1
    _ = (b - a) * (a⁻¹ * a) * (b⁻¹ * b) := by rw [ca, cb]; ring1
    _ = _ := by ring1

/-- The distance between original inverse vertices is bounded by the retained parent displacement and parameter
separation. -/
private theorem inverse_vertex_distance (a b : Fin (geometry.tail.length + 1)) :
    Gaussian.Norm.Basic.normSq ((parent.edge.point
      (SourceChartRequest.Parameter (geometry := geometry) b))⁻¹
      -
      (parent.edge.point (SourceChartRequest.Parameter (geometry
        := geometry) a))⁻¹) ≤
      Gaussian.Norm.Basic.normSq parent.model.displacement *
        (SourceChartRequest.Parameter (geometry := geometry) b -
        SourceChartRequest.Parameter (geometry := geometry) a) ^
        2 := by
  have boundary (i : Fin (geometry.tail.length + 1)) :
      Rational.Box.Boundary.OnBoxBoundary (Branches.Cuts.Ambient curve)
        (parent.edge.point (SourceChartRequest.Parameter
          (geometry := geometry) i)) := data.boundary.point
    ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩
  have unit (i : Fin (geometry.tail.length + 1)) := Reciprocal.Bounds.disk_unit_bound
    (ReciprocalExteriorCollar.inverse_inDisk curve (boundary i))
  rw [inverse_difference
    (PreparedExteriorReciprocal.boundary_nonzero (boundary b))
    (PreparedExteriorReciprocal.boundary_nonzero (boundary a)),
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
  have reduced := Arithmetic.mul_le_mul_direct (Arithmetic.mul_le_mul_direct (le_refl
    (Gaussian.Norm.Basic.normSq (parent.edge.point
      (SourceChartRequest.Parameter (geometry := geometry) a) -
      parent.edge.point (SourceChartRequest.Parameter (geometry
      := geometry) b))))
    (unit b) (Gaussian.Norm.Basic.normSq_nonneg _) (Gaussian.Norm.Basic.normSq_nonneg _))
    (unit a) (Gaussian.Norm.Basic.normSq_nonneg _)
    (Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Coordinate) ≤ 1))
  apply reduced.trans_eq
  rw [Fraction.Field.mul_one_direct, Fraction.Field.mul_one_direct,
    UniformReciprocalCover.Cell.point_line parent
    (SourceChartRequest.Parameter (geometry := geometry) a),
    UniformReciprocalCover.Cell.point_line parent
      (SourceChartRequest.Parameter (geometry := geometry) b)]
  simp only [Rational.Affine.line, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im,
    Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im, -eq_self, -iff_self]
  ring1

/-- A finite rational sum bounded termwise by a common ceiling is bounded by the index count times that ceiling. -/
private theorem sum_ceiling {n : Nat} (values : Fin n → Coordinate) (bound :
  Coordinate)
    (bounded : ∀ i, values i ≤ bound) : FiniteSum.Fin.sumFin values ≤ (n :
      Coordinate) * bound := by
  induction n with
  | zero => change (0 : Coordinate) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ, Nat.cast_succ]
      exact (Arithmetic.add_le_add_direct (bounded 0) (ih _ (fun i => bounded i.succ))).trans_eq (by
        ring1)

/-- The original mesh-only arc error is bounded by the retained quarter radius, inverse-root ceiling and original parent
displacement. -/
theorem regularArcError_geometric (regular : Disk.RegularBounds.Data cap)
    (geometry : Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :
    regularArcError regular geometry
      ≤ Rational.Geometric.Basic.quarterRadius
      (16 * regular.inverseUpper ^ 2 * (Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2) depth :=
        open Purelib.Integration in by
  let q := Rational.Geometric.Basic.quarterRadius 1 depth
  have qNonnegative : 0 ≤ q := Rational.Geometric.Basic.quarterRadius_nonneg (by decide) depth
  have steps : Path.Dyadic.DyadicSteps.Steps interval.edge.left.parameter geometry.tail
      ((interval.edge.right.parameter - interval.edge.left.parameter) * (1 / 2) ^ depth) := by
    rw [geometry.tail_eq]
    exact Path.Dyadic.DyadicSteps.tail_steps _ _ _
  have width : (interval.edge.right.parameter - interval.edge.left.parameter) ^ 2 ≤ 1 :=
    (Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct interval.ordered)
      ((Arithmetic.sub_le_sub_direct interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
        (by decide : (1 : Coordinate) - 0 = 1)) 2).trans_eq (by decide)
  have distance (edge : Fin geometry.tail.length) :
      Gaussian.Norm.Basic.normSq ((parent.edge.point
        (SourceChartRequest.Parameter (geometry := geometry)
        edge.succ))⁻¹ -
        (parent.edge.point (SourceChartRequest.Parameter
          (geometry := geometry) edge.castSucc))⁻¹) ≤ Gaussian.Norm.Basic.normSq parent.model.displacement * q
          := by
    have bound :=
      inverse_vertex_distance
      (geometry := geometry) edge.castSucc edge.succ
    have widths := steps.width_square edge
    change (SourceChartRequest.Parameter (geometry := geometry)
      edge.succ - SourceChartRequest.Parameter (geometry :=
      geometry) edge.castSucc) ^ 2 = _ at widths
    rw [widths] at bound
    exact bound.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct width qNonnegative)
      (Gaussian.Norm.Basic.normSq_nonneg _)).trans_eq (by ring1))
  have each (edge : Fin geometry.tail.length) := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg _) (distance edge) 2)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 16)
      (Arithmetic.sq_nonneg_direct regular.inverseUpper))
  have counted := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (sum_ceiling _ _ each)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le geometry.tail.length))
  apply counted.trans_eq
  have countEq : geometry.tail.length = 2 ^ depth := by
    rw [geometry.tail_eq, Path.Dyadic.DyadicSteps.tail_length]
  have cancel : (((2 ^ depth : Nat) : Coordinate) ^ 2) * q = 1 := by
    rw [pow_two, mul_assoc]
    exact Rational.Geometric.DyadicCount.dyadic_count_cancel 1 depth
  rw [countEq]
  calc
    _ = ((((2 ^ depth : Nat) : Coordinate) ^ 2) * q) *
        (16 * regular.inverseUpper ^ 2 * (Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2 * q) := by
          ring1
    _ = _ := by
      rw [cancel]
      dsimp only [q, -eq_self, -iff_self]
      simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
      ring1

/-- The finite actual paired polynomial arc sum meets the original mesh-only regular arc error bound. -/
theorem regular_polynomial_arcs_bound (regular : Disk.RegularBounds.Data cap)
    (sample : Cap.Primitives.Sample cap differential index box)
    (otherSample : Cap.Primitives.Sample cap other index otherBox)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) (radialDepth : Nat) :
    Gaussian.Norm.Basic.normSq
      (regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample)) ≤
      regularArcError regular
        geometry := by
  have inside (i : Fin (geometry.tail.length + 1)) :=
    ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩)
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin _ _
    (fun edge : Fin geometry.tail.length =>
      Data.regular_paired_arc_refinement regular sample
      otherSample unramified
      (inside edge.castSucc) (inside edge.succ) radialDepth)
  rw [FiniteSum.Fin.sumFin_sub] at bound
  exact bound

/-- Compare the complete cached chart polygon with the physical-coordinate
polynomial arcs, paying sheet error and chord refinement separately. -/
theorem Evaluation.regular_chart_arcs_bound (evaluated :
  Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second target)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
      (minimum : Nat)
    (later : max prepared.index
      (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) (radialDepth : Nat) :
    Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      regularArcArea geometry sample
      otherSample radialDepth) ≤
      2 * ((geometry.tail.length : Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2
        * target) +
        regularArcError regular
          geometry) := by
  have chart := ReciprocalRegularChartSteps.Evaluation.regular_area_uniform evaluated
    unramified positive minimum later
  have arcs :=
    regular_polynomial_arcs_bound
    (geometry := geometry) regular sample otherSample unramified radialDepth
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))
    (regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct chart
        arcs) (by decide : (0 : Coordinate) ≤ 2))
  exact (congrArg Gaussian.Norm.Basic.normSq (by ring1 : evaluated.area.evaluated.chart.originalArea -
    regularArcArea geometry sample
      otherSample radialDepth =
      (evaluated.area.evaluated.chart.originalArea -
        Periods.CenteredBilinearPath.area
          (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)) -
      (regularArcArea geometry sample
        otherSample radialDepth -
        Periods.CenteredBilinearPath.area
          (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)))).trans_le bound

/-- The cached chart polygon compared with the physical arcs when the
retained chart's target and the requested area error are independent. The
bound uses the requested error; the model threshold uses the chart target. -/
theorem Evaluation.regular_chart_arcs_bound_requested {requested : Coordinate}
    (evaluated : Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first
      second requested)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
    (requestedPositive : 0 < requested) (targetLe : target ≤ requested) (minimum : Nat)
    (later : max prepared.index
      (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) (radialDepth : Nat) :
    Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      regularArcArea geometry sample
      otherSample radialDepth) ≤
      2 * ((geometry.tail.length : Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2
        * requested) +
        regularArcError regular
          geometry) := by
  have chart := ReciprocalRegularChartSteps.Evaluation.regular_area_uniform_requested
    evaluated unramified positive requestedPositive targetLe minimum later
  have arcs :=
    regular_polynomial_arcs_bound
    (geometry := geometry) regular sample otherSample unramified radialDepth
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))
    (regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct chart
        arcs) (by decide : (0 : Coordinate) ≤ 2))
  exact (congrArg Gaussian.Norm.Basic.normSq (by ring1 : evaluated.area.evaluated.chart.originalArea -
    regularArcArea geometry sample
      otherSample radialDepth =
      (evaluated.area.evaluated.chart.originalArea -
        Periods.CenteredBilinearPath.area
          (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)) -
      (regularArcArea geometry sample
        otherSample radialDepth -
        Periods.CenteredBilinearPath.area
          (ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)))).trans_le bound

/-- The spatial threshold is chosen from fixed geometric data. After that
mesh is retained, allocate its finite sheet budget and the later model stage.
Every radial refinement consumes the same cached chart and cap samples. -/
theorem regular_chart_arcs_requested (original :
  Disk.CommonChartSources.SourceChartRequest regular geometry target floor)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (error : Coordinate) (positive : 0 < error) (minimum : Nat)
    (meshLater : Rational.Geometric.Search.firstQuarterBelow
      (16 * regular.inverseUpper ^ 2 * (Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2) minimum
        (error / 4) ≤ depth) :
    let rate : Coordinate := (geometry.tail.length : Coordinate) ^ 2 * (264 *
      regular.factorUpper ^ 2)
    let nonnegative : (0 : Coordinate) ≤ rate :=
      Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Coordinate) ≤ 264) (Arithmetic.sq_nonneg_direct _))
    let tolerance := Rational.Budget.Weighted.allowance (error / 4) rate
    let tolerancePositive := Rational.Budget.Weighted.allowance_positive
      (Field.div_pos_direct positive (by decide)) nonnegative
    let source := Disk.CommonChartAreas.SourceChartRequest.withTarget original tolerance
      tolerancePositive
    let threshold := max source.index
      (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        tolerance)
        (Arithmetic.mul_pos_direct (by decide) tolerancePositive) minimum).val
    ∀ (evaluated : Disk.CommonChartSources.SourceChartRequest.Evaluation source first
      second tolerance), threshold ≤ index → ∀ radialDepth,
      Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
        regularArcArea geometry
        sample otherSample radialDepth) < error := by
  intro rate nonnegative tolerance tolerancePositive source threshold evaluated later radialDepth
  have quarterPositive : 0 < error / 4 := Field.div_pos_direct positive (by decide)
  have paid := Rational.Budget.Weighted.mul_allowance_le quarterPositive.le nonnegative
  have sheet : (geometry.tail.length : Coordinate) ^ 2 * (264 * regular.factorUpper
    ^ 2 * tolerance) ≤ error / 4 :=
    (by ring1 : (geometry.tail.length : Coordinate) ^ 2 * (264 * regular.factorUpper
      ^ 2 * tolerance) = rate * tolerance).trans_le paid
  have scaleNonnegative : 0 ≤ 16 * regular.inverseUpper ^ 2 * (Gaussian.Norm.Basic.normSq
    parent.model.displacement) ^ 2 :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.sq_nonneg_direct _)) (Arithmetic.sq_nonneg_direct _)
  have arcs : regularArcError regular
    geometry < error / 4 :=
    (regularArcError_geometric
      regular geometry).trans_lt
      ((quarterRadius_antitone scaleNonnegative meshLater).trans_lt
        (Rational.Geometric.Search.firstQuarterBelow_accurate _ scaleNonnegative minimum _ quarterPositive))
  have total := (Arithmetic.add_lt_add_left_direct arcs
    ((geometry.tail.length : Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2 *
      tolerance))).trans_le
      (Arithmetic.add_le_add_direct sheet (le_refl (error / 4)))
  have bound :=
    (Evaluation.regular_chart_arcs_bound
    evaluated unramified tolerancePositive minimum later radialDepth).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Coordinate) < 2) total)
  exact bound.trans_eq (by
    have cancel := Fraction.Field.div_mul_cancel_of_ne error 4 (by decide)
    calc
      2 * (error / 4 + error / 4) = (error / 4) * 4 := by ring1
      _ = error := cancel)

/-- The requested chart-versus-arc comparison in the orientation consumed by
the parent aggregation. The retained chart's target and the requested area
error are independent; the numeric obligation is supplied separately. -/
theorem Evaluation.regular_area_perTerm {requested : Coordinate}
    (evaluated : Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first
      second requested)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (positive : 0 < target) (requestedPositive : 0 < requested) (targetLe : target ≤ requested)
    (minimum : Nat)
    (later : max prepared.index
      (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4)
          positive) minimum).val ≤ index)
    {error : Coordinate}
    (small : 2 * ((geometry.tail.length : Coordinate) ^ 2 * (264 *
      regular.factorUpper ^ 2 * requested) +
      regularArcError regular
        geometry) ≤ error) :
    Gaussian.Norm.Basic.normSq
      (regularArcArea geometry sample
      otherSample radialDepth -
      evaluated.area.evaluated.chart.originalArea) ≤ error := by
  have bound :=
    Evaluation.regular_chart_arcs_bound_requested
    evaluated unramified positive requestedPositive
    targetLe minimum later radialDepth
  have equal : regularArcArea
    geometry sample otherSample radialDepth -
        evaluated.area.evaluated.chart.originalArea =
      -(evaluated.area.evaluated.chart.originalArea -
        regularArcArea geometry
          sample otherSample radialDepth) := by
    ring1
  exact ((congrArg Gaussian.Norm.Basic.normSq equal).trans_le
    ((le_of_eq (Gaussian.Norm.Basic.normSq_neg _)).trans bound)).trans small

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest
