module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PrimitiveEdgeControl
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Riemann.Integration.PrimitiveEdgeRibbon
public import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon

@[expose] public section

/-!
# Requested primitive comparison on actual dyadic mesh sides

The model accuracy is chosen first, independently of the later spatial
subdivision.  Every depth of the existing horizontal and vertical boundary
sums then meets the same corrected ribbon bound.  These are open sides: the
remaining endpoint term must still be paid or canceled in a global assembly.
-/

namespace Purelib.Riemann.Readings.PrimitiveDyadicBoundary

section
open Purelib.Data
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Polynomial in
/-- A dense polynomial over Gaussian rationals. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry in
/-- A rational rectangular box. -/
private abbrev Box := Rational.Box
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea dyadicDifference dyadicDifference_bound
  horizontalBoundary_eq_lineArea verticalBoundary_eq_lineArea)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveEdgeAnchor)
open _root_.Purelib.Riemann.Integration (PrimitiveEdgeControl)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Integration.PrimitiveEdgeRibbon (PrimitiveRibbonAccuracy)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_zero line_one)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)

namespace PrimitiveEdgeAnchor

variable {polynomial leftPrimitive rightPrimitive :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {leftBox
  rightBox : Purelib.Geometry.Rational.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish :
      Purelib.Data.Gaussian.Basic.Canonical}
    {edge : EdgeTransition left right start finish}

open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- Identify the corrected dyadic area difference with the two actual areas and their final endpoint ribbon.

Alignment cancels the initial ribbon; the final contribution remains explicit for this open side. -/
theorem dyadic_difference_eq (anchor : PrimitiveEdgeAnchor edge leftPrimitive rightPrimitive) (depth : Nat) :
    Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference (fun parameter => anchor.alignedValue (Rational.Affine.line start
      (finish - start) parameter))
      (fun parameter => leftPrimitive.eval (Rational.Affine.line start (finish - start) parameter)) depth 0 1 =
        Path.Dyadic.DyadicBoundaryRibbon.dyadicArea (fun parameter => anchor.alignedValue (Rational.Affine.line start
          (finish - start) parameter)) depth 0 1 -
          Path.Dyadic.DyadicBoundaryRibbon.dyadicArea (fun parameter => leftPrimitive.eval (Rational.Affine.line start
            (finish - start) parameter)) depth 0 1 -
            Path.BoundaryRibbon.area (leftPrimitive.eval finish) (anchor.alignedValue finish - leftPrimitive.eval
              finish) := by
  rw [Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference, line_zero, line_one, anchor.aligned_at_start,
    Gaussian.Basic.sub_self]
  simp only [Path.BoundaryRibbon.area, Gaussian.Basic.conj_zero, Gaussian.Basic.mul_zero, Gaussian.Basic.zero_mul,
    Gaussian.Basic.sub_zero, -eq_self, -iff_self]
  rfl

end PrimitiveEdgeAnchor

namespace PrimitiveEdgeControl

variable {polynomial numerator leftCoefficient rightCoefficient :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {leftBox rightBox :
  Purelib.Geometry.Rational.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish :
      Purelib.Data.Gaussian.Basic.Canonical}
    {edge : EdgeTransition left right start finish} {leftPrimitive : DensePrimitive leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox} {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value
      rightPrimitive.value}

open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- Bound the corrected ribbon at every dyadic depth by eight times drift times four slopes plus drift.

The actual error, right increment and drift increment bounds use the same retained primitive edge control. -/
theorem dyadic_difference_bound (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) (depth
  : Nat) :
    normSq (Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference (fun parameter => anchor.alignedValue
      (Rational.Affine.line start (finish - start) parameter))
      (fun parameter => leftPrimitive.value.eval (Rational.Affine.line start (finish - start) parameter)) depth 0 1) ≤
        8 * control.drift * (4 * control.slope + control.drift) := by
  have estimate := Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference_bound
    (lower := 0) (upper := 1) (error := control.drift)
    (slope := control.slope) (drift := control.drift)
    (fun parameter => anchor.alignedValue (Rational.Affine.line start (finish - start) parameter))
    (fun parameter => leftPrimitive.value.eval (Rational.Affine.line start (finish - start) parameter))
    control.drift_nonnegative (fun parameter inside => by
      have scalar := control.error_bound (parameter := parameter) inside
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    (fun first last firstInside lastInside => by
      have scalar := control.right_increment_bound (first := first) (last := last) firstInside lastInside
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    (fun first last firstInside lastInside => by
      have scalar := control.drift_increment_bound (first := first) (last := last) firstInside lastInside
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    depth (show (0 : Rat.Fraction.Rational) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
      (show (0 : Rat.Fraction.Rational) ≤ 1 ∧ 1 ≤ 1 from ⟨by decide, le_rfl⟩) (show (0 : Rat.Fraction.Rational) ≤ 1 by
        decide)
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, (show (1 : Rat.Fraction.Rational) - 0 = 1 by decide +kernel),
    one_pow, Rat.Fraction.Field.mul_one_direct] using estimate

open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
open Purelib.Geometry
/-- Bound the actual horizontal boundary-sum difference with its final endpoint ribbon retained. -/
theorem horizontal_difference_bound {first last height : Rat.Fraction.Rational}
    {edge : EdgeTransition left right ⟨first, height⟩ ⟨last, height⟩}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value}
    (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) (depth : Nat) :
    normSq (Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary (fun point => Energy.Polygon.energyPrimitivePoint
      (anchor.alignedValue point)) depth first last height -
      Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary (fun point => Energy.Polygon.energyPrimitivePoint
        (leftPrimitive.value.eval point)) depth first last height -
        Path.BoundaryRibbon.area (leftPrimitive.value.eval ⟨last, height⟩) (anchor.alignedValue ⟨last, height⟩ -
          leftPrimitive.value.eval ⟨last, height⟩)) ≤
      8 * control.drift * (4 * control.slope + control.drift) := by
  rw [Path.Dyadic.DyadicBoundaryRibbon.horizontalBoundary_eq_lineArea,
    Path.Dyadic.DyadicBoundaryRibbon.horizontalBoundary_eq_lineArea]
  rw [← Readings.PrimitiveDyadicBoundary.PrimitiveEdgeAnchor.dyadic_difference_eq anchor depth]
  exact Readings.PrimitiveDyadicBoundary.PrimitiveEdgeControl.dyadic_difference_bound control depth

/-- Bound the actual vertical boundary-sum difference with its final endpoint ribbon retained. -/
theorem vertical_difference_bound {first last horizontal : Rat.Fraction.Rational}
    {edge : EdgeTransition left right ⟨horizontal, first⟩ ⟨horizontal, last⟩}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value}
    (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) (depth : Nat) :
    normSq (Rectangle.Partition.PreparedBoxBoundary.verticalBoundary (fun point => Energy.Polygon.energyPrimitivePoint
      (anchor.alignedValue point)) depth first last horizontal -
      Rectangle.Partition.PreparedBoxBoundary.verticalBoundary (fun point => Energy.Polygon.energyPrimitivePoint
        (leftPrimitive.value.eval point)) depth first last horizontal -
        Path.BoundaryRibbon.area (leftPrimitive.value.eval ⟨horizontal, last⟩) (anchor.alignedValue ⟨horizontal, last⟩ -
          leftPrimitive.value.eval ⟨horizontal, last⟩)) ≤
      8 * control.drift * (4 * control.slope + control.drift) := by
  rw [Path.Dyadic.DyadicBoundaryRibbon.verticalBoundary_eq_lineArea,
    Path.Dyadic.DyadicBoundaryRibbon.verticalBoundary_eq_lineArea]
  rw [← Readings.PrimitiveDyadicBoundary.PrimitiveEdgeAnchor.dyadic_difference_eq anchor depth]
  exact Readings.PrimitiveDyadicBoundary.PrimitiveEdgeControl.dyadic_difference_bound control depth

end PrimitiveEdgeControl

namespace PrimitiveRibbonAccuracy

variable {polynomial numerator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {leftBox
  rightBox :
  Purelib.Geometry.Rational.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish :
      Purelib.Data.Gaussian.Basic.Canonical} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- One retained model request pays the corrected ribbon at every spatial depth.

The model index is fixed before subdivision, and the supplied original edge control gives the strict requested bound on
each actual dyadic reading. -/
theorem dyadic_accurate (request : PrimitiveRibbonAccuracy bounds left right start finish target)
    {edge : EdgeTransition (left.refine request.edgeRequest.index) (right.refine request.edgeRequest.index) start
      finish}
    {leftCoefficient rightCoefficient : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
      {leftPrimitive : DensePrimitive
      leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value}
    (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) (depth : Nat) :
    normSq (Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference (fun parameter => anchor.alignedValue
      (Rational.Affine.line start (finish - start) parameter))
      (fun parameter => leftPrimitive.value.eval (Rational.Affine.line start (finish - start) parameter)) depth 0 1) <
        target :=
  (Readings.PrimitiveDyadicBoundary.PrimitiveEdgeControl.dyadic_difference_bound control depth).trans_lt
    (request.allowance_lt control)

end PrimitiveRibbonAccuracy

end Purelib.Riemann.Readings.PrimitiveDyadicBoundary

