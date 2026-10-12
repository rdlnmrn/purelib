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

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus} {index otherIndex : Nat} {box otherBox :
    Rational.Box}

/-- Every convex point of the retained endpoint chord stays within the original root disk. -/
private theorem chord_inside {first last : Gaussian.Basic.Canonical}
    (firstInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial last)
    {parameter : Normalization.InverseRootPolynomial.Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial (RootContinuation.RootRadialGeometry.chord first last
      parameter) := by
  have convex : Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.chord first last parameter) ≤
      (1 - parameter) * Data.Gaussian.Norm.Basic.normSq first + parameter * Data.Gaussian.Norm.Basic.normSq last
        := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct unit.1
      (Fraction.Order.Arithmetic.sub_nonneg_direct unit.2))
      (Gaussian.Norm.Basic.normSq_nonneg (last - first))).trans_eq (by
        simp only [RootContinuation.RootRadialGeometry.chord, Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self]
        ring1)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct convex
    (Fraction.Order.Arithmetic.sq_nonneg_direct (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
      curve.polynomial))
  have endpoints := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside (Fraction.Order.Arithmetic.sub_nonneg_direct
      unit.2))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside unit.1)
  exact scaled.trans ((by ring1 :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
      ((1 - parameter) * Data.Gaussian.Norm.Basic.normSq first + parameter * Data.Gaussian.Norm.Basic.normSq
        last) =
      (1 - parameter) * (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
        Data.Gaussian.Norm.Basic.normSq first) +
        parameter * (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius curve.polynomial ^ 2 *
          Data.Gaussian.Norm.Basic.normSq last)).trans_le
      (endpoints.trans_eq (by ring1)))

/-- The regular order-zero coefficient is bounded by its retained inverse-root ceiling. -/
theorem regular_coefficient_bound (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) {point :
      Gaussian.Basic.Canonical}
    (inside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval point) ≤ regular.inverseUpper := by
  rw [sample.coefficient_eq, sample.pulledInverse_eq, sample.inverse_eq]
  simp only [Hyperelliptic.Charts.Reciprocal.Cap.Primitives.coefficient,
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point,
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.degree, unramified, Nat.zero_add, Nat.one_mul, pow_one,
    Nat.cast_one, Purelib.Algebra.Ring.Multiplication.neg_mul, one_mul, Gaussian.Norm.Basic.normSq_neg,
      Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, -eq_self, -iff_self]
  have numerator := Fraction.Order.Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg point)
    (Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound inside)
    (Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.reversedDifferential differential).exponent
  rw [one_pow] at numerator
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct numerator (regular.inverse_bound index inside)
    (Gaussian.Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)).trans_eq (Fraction.Field.one_mul _)

/-- The retained chord equals the affine line with the same original endpoints. -/
private theorem chord_line (first last : Gaussian.Basic.Canonical) (parameter :
  Normalization.InverseRootPolynomial.Coordinate) :
    Purelib.Geometry.Rational.Affine.line first (last - first) parameter = RootContinuation.RootRadialGeometry.chord
      first last parameter := by
  apply Gaussian.Basic.ext <;> simp only [Rational.Affine.line, Gaussian.Cast.ofCoordinate_re,
    Gaussian.Cast.ofCoordinate_im, RootContinuation.RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
    Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Scale.scale_re,
      Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1

/-- The actual regular primitive increment along the original endpoint chord satisfies the retained slope bound. -/
theorem regular_chord_increment (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) {first last :
      Gaussian.Basic.Canonical}
    (firstInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial last)
    {left right : Normalization.InverseRootPolynomial.Coordinate} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤
      right ∧ right ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first
      last right) -
      sample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last left)) ≤
        (2 * regular.inverseUpper * Data.Gaussian.Norm.Basic.normSq (last - first)) * (right - left) ^ 2 := by
  let primitive : Dense.Gaussian.Primitive.Certificate.DensePrimitive sample.coefficient boundingBox :=
    { value := sample.primitive.value
      derivative_eq := sample.primitive.derivative_eq
      remainderBound := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound sample.primitive.value
        Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox
      remainderBound_nonnegative := (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun startInside finishInside => by
        have estimate := Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
          sample.primitive.value finishInside startInside
        rw [sample.primitive.derivative_eq] at estimate
        exact estimate }
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : Normalization.InverseRootPolynomial.Coordinate) (unit : interval.Contains parameter) :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox.Contains (Rational.Affine.line first (last - first)
        parameter) := by
    rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_line]
    exact Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_inside firstInside lastInside unit)
  have coefficient (parameter : Normalization.InverseRootPolynomial.Coordinate) (unit : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval (Rational.Affine.line first (last - first)
        parameter)) ≤ regular.inverseUpper := by
    rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_line]
    exact Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.regular_coefficient_bound regular sample
      unramified (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_inside firstInside
      lastInside unit)
  have estimate := Dense.Gaussian.Primitive.Segment.Bounds.DensePrimitive.segment_increment_le primitive first (last -
    first) interval inside
    regular.inverseUpper coefficient rightUnit leftUnit
  rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_line,
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.chord_line] at estimate
  exact estimate

open Purelib.Integration in
/-- The two original regular polynomial arc increments satisfy the retained inverse-root fourth-power distance bound at
any shared sample stage and radial depth. -/
theorem regular_paired_arc_refinement (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) {first last :
      Gaussian.Basic.Canonical}
    (firstInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial last) (depth : Nat) :
    let values := Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialPairedArcs.Bilinear.arcArea values depth first last
      - Topology.Polygon.Stokes.edgeArea (values first) (values last)) ≤
      16 * regular.inverseUpper ^ 2 * Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 := by
  intro values
  let slope := 2 * regular.inverseUpper * Data.Gaussian.Norm.Basic.normSq (last - first)
  have nonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) regular.inverseUpper_positive.le)
      (Gaussian.Norm.Basic.normSq_nonneg _)
  have estimate := Path.Dyadic.DyadicPairedAreaRefinement.dyadicArea_chord_bound
    (fun parameter => values (RootContinuation.RootRadialGeometry.chord first last parameter)) nonnegative
    (fun a b aUnit bUnit => by
      constructor
      · change Gaussian.Basic.Canonical.normSq
          (sample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last b) -
            sample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last a)) ≤ slope * (b - a) ^ 2
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
        exact regular_chord_increment regular sample unramified firstInside lastInside aUnit bUnit
      · change Gaussian.Basic.Canonical.normSq
          (otherSample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last b) -
            otherSample.primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last a)) ≤ slope * (b - a)
              ^ 2
        rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
        exact Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.regular_chord_increment
          regular otherSample unramified firstInside lastInside aUnit bUnit)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : RootContinuation.RootRadialGeometry.chord first last 0 = first := by
    apply Gaussian.Basic.ext <;> simp only [RootContinuation.RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1
  have atOne : RootContinuation.RootRadialGeometry.chord first last 1 = last := by
    apply Gaussian.Basic.ext <;> simp only [RootContinuation.RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    rw [show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0) ^ 4 = 1 by decide]
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

variable {genus count otherCount depth floor index : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData : Data otherPatch otherCount}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {interval : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval cover otherCover} {regular :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth} {target :
    Normalization.InverseRootPolynomial.Coordinate}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {firstComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell}
  {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
  {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}

/-- The finite paired polynomial arc area on the original physical reciprocal mesh vertices. -/
@[expose] def regularArcArea (geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap :=
  cap) interval depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox) (radialDepth : Nat) :
      Gaussian :=
  FiniteSum.Fin.sumFin (fun edge : Fin geometry.tail.length => RootContinuation.RootRadialPairedArcs.Bilinear.arcArea
    (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) radialDepth
    (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
      := geometry) edge.castSucc))⁻¹
    (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
      := geometry) edge.succ))⁻¹)

/-- A mesh-only error: neither the sampled cap coefficients nor the radial
refinement depth enters this bound. -/
@[expose] def regularArcError (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :
      Coordinate :=
  (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun edge : Fin
    geometry.tail.length =>
    16 * regular.inverseUpper ^ 2 * Data.Gaussian.Norm.Basic.normSq
      ((parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
        (geometry := geometry) edge.succ))⁻¹ -
        (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
          (geometry := geometry) edge.castSucc))⁻¹) ^ 2)

/-- A finite rational sum of nonnegative terms is nonnegative. -/
private theorem sumFin_nonnegative {n : Nat} (values : Fin n → Normalization.InverseRootPolynomial.Coordinate)
    (positive : ∀ i, 0 ≤ values i) : 0 ≤ FiniteSum.Fin.sumFin values := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact add_nonneg (positive 0) (ih _ (fun i => positive i.succ))

/-- The original mesh-only regular arc error is nonnegative. -/
theorem regularArcError_nonnegative (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) : 0 ≤
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
      geometry :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.sumFin_nonnegative _ (fun edge
      => Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 16) (Fraction.Order.Arithmetic.sq_nonneg_direct
        regular.inverseUpper))
      (Fraction.Order.Arithmetic.sq_nonneg_direct (Data.Gaussian.Norm.Basic.normSq
        ((parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
          (geometry := geometry) edge.succ))⁻¹ -
          (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
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
    Data.Gaussian.Norm.Basic.normSq ((parent.edge.point
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b))⁻¹
      -
      (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
        := geometry) a))⁻¹) ≤
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement *
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b -
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a) ^
        2 := by
  have boundary (i : Fin (geometry.tail.length + 1)) :
      Rational.Box.Boundary.OnBoxBoundary (Hyperelliptic.Branches.Cuts.Ambient curve)
        (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
          (geometry := geometry) i)) := data.boundary.point
    ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩
  have unit (i : Fin (geometry.tail.length + 1)) := Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound
    (Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.inverse_inDisk curve (boundary i))
  rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.inverse_difference
    (Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal.boundary_nonzero (boundary b))
    (Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal.boundary_nonzero (boundary a)),
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
  have reduced := Fraction.Order.Arithmetic.mul_le_mul_direct (Fraction.Order.Arithmetic.mul_le_mul_direct (le_refl
    (Data.Gaussian.Norm.Basic.normSq (parent.edge.point
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a) -
      parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
      := geometry) b))))
    (unit b) (Gaussian.Norm.Basic.normSq_nonneg _) (Gaussian.Norm.Basic.normSq_nonneg _))
    (unit a) (Gaussian.Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1))
  apply reduced.trans_eq
  rw [Fraction.Field.mul_one_direct, Fraction.Field.mul_one_direct,
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell.point_line parent
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a),
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell.point_line parent
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b)]
  simp only [Rational.Affine.line, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im,
    Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im, -eq_self, -iff_self]
  ring1

/-- A finite rational sum bounded termwise by a common ceiling is bounded by the index count times that ceiling. -/
private theorem sum_ceiling {n : Nat} (values : Fin n → Normalization.InverseRootPolynomial.Coordinate) (bound :
  Normalization.InverseRootPolynomial.Coordinate)
    (bounded : ∀ i, values i ≤ bound) : FiniteSum.Fin.sumFin values ≤ (n :
      Normalization.InverseRootPolynomial.Coordinate) * bound := by
  induction n with
  | zero => change (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 0 * bound; rw [Fraction.Field.zero_mul_direct]
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ, Nat.cast_succ]
      exact (Fraction.Order.Arithmetic.add_le_add_direct (bounded 0) (ih _ (fun i => bounded i.succ))).trans_eq (by
        ring1)

/-- The original mesh-only arc error is bounded by the retained quarter radius, inverse-root ceiling and original parent
displacement. -/
theorem regularArcError_geometric (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth) :
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular geometry
      ≤ Rational.Geometric.Basic.quarterRadius
      (16 * regular.inverseUpper ^ 2 * (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2) depth :=
        open Purelib.Integration in by
  let q := Rational.Geometric.Basic.quarterRadius 1 depth
  have qNonnegative : 0 ≤ q := Rational.Geometric.Basic.quarterRadius_nonneg (by decide) depth
  have steps : Path.Dyadic.DyadicSteps.Steps interval.edge.left.parameter geometry.tail
      ((interval.edge.right.parameter - interval.edge.left.parameter) * (1 / 2) ^ depth) := by
    rw [geometry.tail_eq]
    exact Path.Dyadic.DyadicSteps.tail_steps _ _ _
  have width : (interval.edge.right.parameter - interval.edge.left.parameter) ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct interval.ordered)
      ((Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
        (by decide : (1 : Normalization.InverseRootPolynomial.Coordinate) - 0 = 1)) 2).trans_eq (by decide)
  have distance (edge : Fin geometry.tail.length) :
      Data.Gaussian.Norm.Basic.normSq ((parent.edge.point
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry)
        edge.succ))⁻¹ -
        (parent.edge.point (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
          (geometry := geometry) edge.castSucc))⁻¹) ≤ Data.Gaussian.Norm.Basic.normSq parent.model.displacement * q
          := by
    have bound :=
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.inverse_vertex_distance
      (geometry := geometry) edge.castSucc edge.succ
    have widths := steps.width_square edge
    change (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry)
      edge.succ - Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry :=
      geometry) edge.castSucc) ^ 2 = _ at widths
    rw [widths] at bound
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width qNonnegative)
      (Gaussian.Norm.Basic.normSq_nonneg _)).trans_eq (by ring1))
  have each (edge : Fin geometry.tail.length) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg _) (distance edge) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.sq_nonneg_direct regular.inverseUpper))
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.sum_ceiling _ _ each)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le geometry.tail.length))
  apply counted.trans_eq
  have countEq : geometry.tail.length = 2 ^ depth := by
    rw [geometry.tail_eq, Path.Dyadic.DyadicSteps.tail_length]
  have cancel : (((2 ^ depth : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2) * q = 1 := by
    rw [pow_two, mul_assoc]
    exact Rational.Geometric.DyadicCount.dyadic_count_cancel 1 depth
  rw [countEq]
  calc
    _ = ((((2 ^ depth : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2) * q) *
        (16 * regular.inverseUpper ^ 2 * (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2 * q) := by
          ring1
    _ = _ := by
      rw [cancel]
      dsimp only [q, -eq_self, -iff_self]
      simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
      ring1

/-- The finite actual paired polynomial arc sum meets the original mesh-only regular arc error bound. -/
theorem regular_polynomial_arcs_bound (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (radialDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample)) ≤
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
        geometry := by
  have inside (i : Fin (geometry.tail.length + 1)) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩)
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin _ _
    (fun edge : Fin geometry.tail.length =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.Data.regular_paired_arc_refinement regular sample
      otherSample unramified
      (inside edge.castSucc) (inside edge.succ) radialDepth)
  rw [FiniteSum.Fin.sumFin_sub] at bound
  exact bound

/-- Compare the complete cached chart polygon with the physical-coordinate
polynomial arcs, paying sheet error and chord refinement separately. -/
theorem Evaluation.regular_chart_arcs_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second target)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
      (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) (radialDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth) ≤
      2 * ((geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2
        * target) +
        Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
          geometry) := by
  have chart := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_area_uniform evaluated
    unramified positive minimum later
  have arcs :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regular_polynomial_arcs_bound
    (geometry := geometry) regular sample otherSample unramified radialDepth
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct chart
        arcs) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1 : evaluated.area.evaluated.chart.originalArea -
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth =
      (evaluated.area.evaluated.chart.originalArea -
        Periods.CenteredBilinearPath.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)) -
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
        otherSample radialDepth -
        Periods.CenteredBilinearPath.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)))).trans_le bound

/-- The cached chart polygon compared with the physical arcs when the
retained chart's target and the requested area error are independent. The
bound uses the requested error; the model threshold uses the chart target. -/
theorem Evaluation.regular_chart_arcs_bound_requested {requested : Normalization.InverseRootPolynomial.Coordinate}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first
      second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
    (requestedPositive : 0 < requested) (targetLe : target ≤ requested) (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) (radialDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth) ≤
      2 * ((geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2
        * requested) +
        Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
          geometry) := by
  have chart := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_area_uniform_requested
    evaluated unramified positive requestedPositive targetLe minimum later
  have arcs :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regular_polynomial_arcs_bound
    (geometry := geometry) regular sample otherSample unramified radialDepth
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct chart
        arcs) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1 : evaluated.area.evaluated.chart.originalArea -
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth =
      (evaluated.area.evaluated.chart.originalArea -
        Periods.CenteredBilinearPath.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)) -
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
        otherSample radialDepth -
        Periods.CenteredBilinearPath.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)))).trans_le bound

/-- The spatial threshold is chosen from fixed geometric data. After that
mesh is retained, allocate its finite sheet budget and the later model stage.
Every radial refinement consumes the same cached chart and cap samples. -/
theorem regular_chart_arcs_requested (original :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (error : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < error) (minimum : Nat)
    (meshLater : Rational.Geometric.Search.firstQuarterBelow
      (16 * regular.inverseUpper ^ 2 * (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) ^ 2) minimum
        (error / 4) ≤ depth) :
    let rate : Coordinate := (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 *
      regular.factorUpper ^ 2)
    let nonnegative : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ rate :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 264) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    let tolerance := Rational.Budget.Weighted.allowance (error / 4) rate
    let tolerancePositive := Rational.Budget.Weighted.allowance_positive
      (Fraction.Order.Field.div_pos_direct positive (by decide)) nonnegative
    let source := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget original tolerance
      tolerancePositive
    let threshold := max source.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        tolerance)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) tolerancePositive) minimum).val
    ∀ (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation source first
      second tolerance), threshold ≤ index → ∀ radialDepth,
      Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
        Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry
        sample otherSample radialDepth) < error := by
  intro rate nonnegative tolerance tolerancePositive source threshold evaluated later radialDepth
  have quarterPositive : 0 < error / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have paid := Rational.Budget.Weighted.mul_allowance_le quarterPositive.le nonnegative
  have sheet : (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 * regular.factorUpper
    ^ 2 * tolerance) ≤ error / 4 :=
    (by ring1 : (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 * regular.factorUpper
      ^ 2 * tolerance) = rate * tolerance).trans_le paid
  have scaleNonnegative : 0 ≤ 16 * regular.inverseUpper ^ 2 * (Data.Gaussian.Norm.Basic.normSq
    parent.model.displacement) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have arcs : Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
    geometry < error / 4 :=
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError_geometric
      regular geometry).trans_lt
      ((quarterRadius_antitone scaleNonnegative meshLater).trans_lt
        (Rational.Geometric.Search.firstQuarterBelow_accurate _ scaleNonnegative minimum _ quarterPositive))
  have total := (Fraction.Order.Arithmetic.add_lt_add_left_direct arcs
    ((geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 * regular.factorUpper ^ 2 *
      tolerance))).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct sheet (le_refl (error / 4)))
  have bound :=
    (Evaluation.regular_chart_arcs_bound
    evaluated unramified tolerancePositive minimum later radialDepth).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2) total)
  exact bound.trans_eq (by
    have cancel := Fraction.Field.div_mul_cancel_of_ne error 4 (by decide)
    calc
      2 * (error / 4 + error / 4) = (error / 4) * 4 := by ring1
      _ = error := cancel)

/-- The requested chart-versus-arc comparison in the orientation consumed by
the parent aggregation. The retained chart's target and the requested area
error are independent; the numeric obligation is supplied separately. -/
theorem Evaluation.regular_area_perTerm {requested : Normalization.InverseRootPolynomial.Coordinate}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first
      second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (positive : 0 < target) (requestedPositive : 0 < requested) (targetLe : target ≤ requested)
    (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
          positive) minimum).val ≤ index)
    {error : Normalization.InverseRootPolynomial.Coordinate}
    (small : 2 * ((geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (264 *
      regular.factorUpper ^ 2 * requested) +
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcError regular
        geometry) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry sample
      otherSample radialDepth -
      evaluated.area.evaluated.chart.originalArea) ≤ error := by
  have bound :=
    Evaluation.regular_chart_arcs_bound_requested
    evaluated unramified positive requestedPositive
    targetLe minimum later radialDepth
  have equal : Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea
    geometry sample otherSample radialDepth -
        evaluated.area.evaluated.chart.originalArea =
      -(evaluated.area.evaluated.chart.originalArea -
        Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest.regularArcArea geometry
          sample otherSample radialDepth) := by
    ring1
  exact ((congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_le
    ((le_of_eq (Gaussian.Norm.Basic.normSq_neg _)).trans bound)).trans small

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest
