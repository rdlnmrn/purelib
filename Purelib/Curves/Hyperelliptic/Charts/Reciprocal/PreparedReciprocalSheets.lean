module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelOverlap
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open Purelib.Riemann.Normalization.InverseModelOverlap
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name

/-!
# Source/reciprocal sheet agreement throughout a covered boundary arc

The two initial neighborhoods are built from the actual prepared source
occurrence and its attached reciprocal owner. The finite root comparison
fixes their initial polynomial sign. Denominator-cleared sign constancy
then propagates that same sign throughout their common covered prefix.
The source and reciprocal refinement indices are independent.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets

open Purelib.Riemann.Curves
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
open Purelib.Riemann.Branches
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open PreparedBoundarySegments (ParentOnBoundary)
open PreparedPrimitiveSheets (CompatiblePatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives (Patch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples (Attachment)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus leftCount rightCount : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {parent : CenteredEdge curve differential} {boundary :
    ParentOnBoundary parent (Ambient curve)}
  {attached : Attachment parent boundary}

/-- The original source root and attached reciprocal root satisfy the retained exact coordinate-scaling equivalence. -/
private def initialRoots (source : CompatiblePatch parent leftCount) (reciprocal : Patch parent boundary attached
  rightCount)
    (first : ContinuedNeighborhood.Point source.neighborhood (parent.edge.point 0))
    (second : ContinuedNeighborhood.Point reciprocal.patch (parent.edge.point 0)⁻¹) :
    Equivalence.NamedEquivalent (Coherent.CoherentNamed.mul (Coherent.CoherentNamed.Coherence.exact
      (ReciprocalRootNames.factor genus (parent.edge.point 0))) first.certificate.value).name
      second.certificate.value.name := by
  let original := PreparedModels.rootAtCached curve parent.edge.segment parent.edge.within
    parent.edge.left parent.edge.owner parent.edge.request parent.edge.cached parent.edge.ordered parent.edge.small
    0 parent.edge.baseInside
  have sourceRoots : Equivalence.NamedEquivalent original.value.name first.certificate.value.name := by
    have same := source.point_equivalent 0 parent.edge.baseInside first
    unfold Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.rootName at same
    exact same
  have multiplied := Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    (Coherent.CoherentNamed.Coherence.exact (ReciprocalRootNames.factor genus (parent.edge.point 0)))
    (Coherent.CoherentNamed.Coherence.exact (ReciprocalRootNames.factor genus (parent.edge.point 0)))
      first.certificate.value original.value
    (Equivalence.NamedEquivalent.refl _) sourceRoots.symm
  exact multiplied.trans ((PreparedReciprocalSamples.root parent boundary).prepared.equivalent.trans
    (attached.equivalent.trans (reciprocal.pointEquivalent second)))

/-- At the original starting point, arbitrary source and reciprocal model stages select the same nearest root branch. -/
theorem initial_nearest (source : CompatiblePatch parent leftCount) (reciprocal : Patch parent boundary attached
  rightCount)
    (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval (parent.edge.point
      0) -
      ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) (parent.edge.point 0)) ≤
    Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval (parent.edge.point
      0) +
      ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) (parent.edge.point 0)) := by
  let first := ContinuedNeighborhood.Point.acquire source.neighborhood (parent.edge.point 0) source.start_inside
  let second := ContinuedNeighborhood.Point.acquire reciprocal.patch (parent.edge.point 0)⁻¹ reciprocal.start_inside
  exact ReciprocalInverseModelOverlap.scaled_equivalent_nearest first second source.start_inside reciprocal.start_inside
    (initialRoots source reciprocal first second)
      leftIndex rightIndex

/-- The retained initial source and reciprocal polynomial models select the unflipped alignment at any original stage
pair. -/
theorem initial_flip (source : CompatiblePatch parent leftCount) (reciprocal : Patch parent boundary attached
  rightCount)
    (leftIndex rightIndex : Nat) :
    (SignAlignment.build ((source.neighborhood.base.refine
      leftIndex).value.eval (parent.edge.point 0))
      (ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) (parent.edge.point 0))).flip
        = false := by
  have nearest := initial_nearest source reciprocal
    leftIndex rightIndex
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at nearest
  unfold SignAlignment.build
  rw [dif_pos nearest]

set_option genInjectivity false in
/-- A retained, positive common source interval. Coverage quantifies over the actual inverted arc, not a list of points
or the reciprocal endpoint chord. -/
structure CommonPrefix (source : CompatiblePatch parent leftCount) (reciprocal : Patch parent boundary attached
  rightCount) where
  /-- The retained positive fraction of the original source interval covered by both patches. -/ fraction :
    Fraction.Rational
  /-- The retained common source fraction is strictly positive. -/ positive : 0 < fraction
  /-- The retained common source fraction is at most one. -/ upper : fraction ≤ 1
  /-- Every original source point up to the retained fraction lies in the source patch. -/ source_contains : ∀
    parameter, 0 ≤ parameter ∧ parameter ≤ fraction → source.neighborhood.box.Contains (parent.edge.point parameter)
  /-- Every actual reciprocal image point up to the retained fraction lies in the reciprocal patch. -/
    reciprocal_contains : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ fraction → reciprocal.patch.box.Contains
    (parent.edge.point parameter)⁻¹

constructive_injectivity CommonPrefix

namespace CommonPrefix

variable {source : CompatiblePatch parent leftCount} {reciprocal : Patch parent boundary attached rightCount}

/-- The original prefix movement squared norm equals its parameter squared times the full source displacement squared
norm. -/
private theorem source_movement (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point 0) = parameter ^ 2 *
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement := by
  change Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt parameter -
    parent.edge.localSegment.pointAt 0) =
    parameter ^ 2 * Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt 1 -
      parent.edge.localSegment.pointAt 0)
  rw [parent.edge.localSegment.normSq_pointAt_sub_pointAt parameter 0,
    parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0]
  ring1

/-- The original prefix movement squared norm equals its parameter squared times the full source displacement squared
norm. -/
theorem source_movement_for_build (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point 0) = parameter ^ 2 *
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement := by
  change Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt parameter -
    parent.edge.localSegment.pointAt 0) =
    parameter ^ 2 * Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt 1 -
      parent.edge.localSegment.pointAt 0)
  rw [parent.edge.localSegment.normSq_pointAt_sub_pointAt parameter 0,
    parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0]
  ring1

/-- Intersect the already proved reciprocal coverage with a finite source radius calculation. This succeeds without a
geometric or sign-check premise. -/
@[expose] def build (source : CompatiblePatch parent leftCount) (reciprocal : Patch parent boundary attached rightCount)
  :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets.CommonPrefix source reciprocal := by
  let covered := CoveredPrefix.build reciprocal
  let scale := Data.Gaussian.Norm.Basic.normSq parent.model.displacement + 1
  have scalePositive : 0 < scale := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  let target := source.neighborhood.radius ^ 2 / scale
  have targetPositive : 0 < target := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct source.neighborhood.radius_positive 2) scalePositive
  let sourceFraction := Geometric.dyadicSquareRadius target
  let fraction := min covered.fraction sourceFraction
  have positive : 0 < fraction := Fraction.Order.Basic.lt_min covered.positive (Geometric.dyadicSquareRadius_positive
    target)
  refine ⟨fraction, positive, (Fraction.Order.Basic.min_le_left _ _).trans covered.upper, ?_, ?_⟩
  · intro parameter inside
    have parameterLe : parameter ≤ sourceFraction := inside.2.trans (Fraction.Order.Basic.min_le_right _ _)
    have paid : Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point 0) ≤
      source.neighborhood.radius ^ 2 := by
      rw [source_movement_for_build]
      calc
        _ ≤ sourceFraction ^ 2 * scale := Fraction.Order.Arithmetic.mul_le_mul_direct
          (Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 parameterLe 2)
          (le_add_of_nonneg_right (by decide : (0 : Fraction.Rational) ≤ 1))
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ ≤ target * scale := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Geometric.dyadicSquareRadius_sq_lt targetPositive).le scalePositive.le
        _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ scalePositive.ne'
    rw [source.neighborhood.box_eq, source.center_eq]
    exact Centered.centeredBox_contains_of_normSq_sub_le source.neighborhood.radius_positive.le paid
  · intro parameter inside
    exact covered.contains parameter ⟨inside.1, inside.2.trans (Fraction.Order.Basic.min_le_left _ _)⟩

/-- The original prepared parent parametrization is its retained starting point plus the scaled original displacement.
-/
private theorem point_line (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  Fraction.Rational) :
    parent.edge.point parameter = Affine.line (parent.edge.point 0) parent.model.displacement parameter := by
  change parent.edge.localSegment.pointAt parameter = Affine.line (parent.edge.localSegment.pointAt 0)
    (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) parameter
  rw [ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
  apply Data.Gaussian.Basic.ext <;>
    simp only [ClearSegment.pointAt, Affine.line,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
        ring1

/-- Actual retained ownership fixes the unflipped branch throughout every rational point of the covered source interval,
at arbitrary model indices. -/
theorem flip_false (covered : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets.CommonPrefix source
  reciprocal) (leftIndex rightIndex : Nat)
    (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ covered.fraction) :
    (SignAlignment.build ((source.neighborhood.base.refine leftIndex).value.eval (parent.edge.point parameter))
      (ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) (parent.edge.point
        parameter))).flip = false := by
  let interval : Data.Rat.Interval.Bounds := ⟨0, covered.fraction, covered.positive.le⟩
  have leftContains (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
      source.neighborhood.base.box.Contains (Affine.line (parent.edge.point 0) parent.model.displacement parameter) :=
        by
    rw [← point_line]
    exact source.neighborhood.box_refines.contains (covered.source_contains parameter inside)
  have rightContains (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
      reciprocal.patch.base.box.Contains (Affine.line (parent.edge.point 0) parent.model.displacement parameter)⁻¹ := by
    rw [← point_line]
    exact reciprocal.patch.box_refines.contains (covered.reciprocal_contains parameter inside)
  have lower (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Affine.line (parent.edge.point 0) parent.model.displacement
        parameter) := by
    rw [← point_line]
    exact PreparedExteriorReciprocal.boundary_norm_lower (boundary.point ⟨inside.1, inside.2.trans covered.upper⟩)
  have same := ReciprocalInverseModelOverlap.flip_eq (source.neighborhood.base.refine leftIndex)
    (reciprocal.patch.base.refine rightIndex) (parent.edge.point 0) parent.model.displacement interval
    leftContains rightContains lower (first := 0) (last := parameter) ⟨le_rfl, covered.positive.le⟩ inside
  rw [← point_line, ←
    point_line] at same
  exact same.symm.trans (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets.initial_flip source reciprocal
    leftIndex rightIndex)

/-- The quantitative model discrepancy now follows the same branch at every point of the actual arc. Both residual terms
decay under refinement; there is no fixed prepared-center error floor in this chart-to-chart comparison. -/
theorem distance_le (covered : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets.CommonPrefix source
  reciprocal) (leftIndex rightIndex : Nat)
    (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ covered.fraction) :
    Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval (parent.edge.point
      parameter) -
      ReciprocalInverseModelOverlap.value curve (reciprocal.patch.base.refine rightIndex) (parent.edge.point parameter))
        ≤
      6 * ((source.neighborhood.base.refine leftIndex).bound + (reciprocal.patch.base.refine rightIndex).bound) *
        Data.Gaussian.Norm.Basic.normSq ((source.neighborhood.base.refine leftIndex).value.eval
          (parent.edge.point parameter)) := by
  let left := source.neighborhood.base.refine leftIndex
  let right := reciprocal.patch.base.refine rightIndex
  let alignment := SignAlignment.build (left.value.eval (parent.edge.point parameter))
    (ReciprocalInverseModelOverlap.value curve right (parent.edge.point parameter))
  have leftResidual : Data.Gaussian.Norm.Basic.normSq (1 - curve.polynomial.eval (parent.edge.point parameter)
    *
      (left.value.eval (parent.edge.point parameter)) ^ 2) ≤ left.bound := by
    rw [← left.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact left.residualBound _ (source.neighborhood.box_refines.contains (covered.source_contains parameter inside))
  have rightResidual := ReciprocalInverseModelOverlap.residual right
    (PreparedExteriorReciprocal.parent_point_nonzero boundary ⟨inside.1, inside.2.trans covered.upper⟩)
    (reciprocal.patch.box_refines.contains (covered.reciprocal_contains parameter inside))
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
  have bound := alignment.distance_le leftResidual rightResidual left.bound_small
  simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at bound
  have selected : alignment.value = ReciprocalInverseModelOverlap.value curve right (parent.edge.point parameter) := by
    rw [alignment.value_eq, covered.flip_false leftIndex rightIndex parameter inside]
    rfl
  rw [selected] at bound
  exact bound

end CommonPrefix

/-- Reuse an actual reciprocal reading's owner while acquiring the compatible source patch and their common covered
interval. -/
@[expose] def acquire {target : Fraction.Rational} (reading : PreparedReciprocalSamples.Reading parent boundary target)
  :
    (source : CompatiblePatch parent genus) × (reciprocal : Patch parent boundary reading.1 genus) ×
      CommonPrefix source reciprocal :=
  let source := CompatiblePatch.acquire parent genus
  let reciprocal := Patch.build reading.1 genus
  ⟨source, reciprocal, Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets.CommonPrefix.build source
    reciprocal⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSheets
