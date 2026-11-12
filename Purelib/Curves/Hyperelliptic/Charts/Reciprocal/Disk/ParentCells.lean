module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# Cap paths beside the actual retained reciprocal area cells

The original cell, its source path and summary, and its reciprocal inverse
polynomial are consumed directly. Only the cap comparison polynomial and
its fine increment path are added. Bounds use the cached parent budget.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Budget quarterRadius_mono)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicIncrements_sum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {edge :
    ParameterEdge} {cell :
    Cell data edge}
  {comparison : ArcSamples.Data regular cell} {source :
    SourcePrimitive data index}
  {box : Geometry.Rational.Box} {capSample :
    Primitives.Sample cap differential index box}

/-- Both records certify the same model from the same retained source and parameter edge. Only their proof fields can
differ; no paths are equated. -/
theorem sameCell (first last : Cell data edge) : first = last := by
  rcases first with ⟨firstOrdered, firstModel, firstEq, firstContains⟩
  rcases last with ⟨lastOrdered, lastModel, lastEq, lastContains⟩
  have models : firstModel = lastModel := firstEq.trans lastEq.symm
  cases models
  rfl

set_option genInjectivity false in
/-- The original reciprocal area cell with its cached cap increment path and summary.

The retained cap sample reuses the original cell primitive exactly; source paths and their summaries keep their original
identities. -/
structure ComparedCell (comparison : ArcSamples.Data regular cell)
    (source : SourcePrimitive data index) (capSample : Primitives.Sample cap differential
      index box) (depth : Nat) where
  /-- The original reciprocal source area cell and its retained summaries. -/ original : ReciprocalBoundaryArea.CellArea
    source depth edge
  /-- The cached cap comparison sample using this exact original cell primitive. -/ sample : ArcSamples.Sample
    comparison capSample
  /-- The cached cap sample retains exactly the original cell's right primitive. -/ retained_eq : sample.retained =
    original.right
  /-- The cached finite dyadic increment path of the retained cap primitive. -/ capPath : List
    Gaussian
  /-- The cap path is exactly the original cap value's dyadic increments on this edge and depth. -/ capPath_eq : capPath
    = dyadicIncrements (ArcArea.Sample.capValue sample) depth edge.left.parameter
    edge.right.parameter
  /-- The cached exact total and area summary of the retained cap path. -/ capSummary : Summary capPath

constructive_injectivity ComparedCell

namespace ComparedCell

/-- Reuse the original area cell and inverse primitive, then cache its cap path and exact increment summary. -/
@[expose] def build (comparison : ArcSamples.Data regular cell)
    (capSample : Primitives.Sample cap differential index box)
    (original : ReciprocalBoundaryArea.CellArea source depth edge) :
      ComparedCell comparison source capSample depth :=
  let sample := ArcSamples.Sample.ofPrimitive comparison capSample original.right (sameCell _ _)
  let capPath := dyadicIncrements (ArcArea.Sample.capValue sample) depth edge.left.parameter
    edge.right.parameter
  ⟨original, sample, rfl, capPath, rfl, Summary.build capPath⟩

/-- The retained cap-path total is exactly the cached original cap sample increment. -/
theorem cap_total (compared : ComparedCell comparison source
  capSample depth) :
    compared.capSummary.total = compared.sample.increment := by
  rw [compared.capSummary.total_eq, compared.capPath_eq, dyadicIncrements_sum,
    ArcArea.Sample.capValue_left compared.sample,
    Data.Gaussian.Basic.sub_zero, ArcArea.Sample.capValue_right compared.sample]

/-- The retained cap-path area is the finite dyadic area of its original cap primitive. -/
theorem cap_area (compared : ComparedCell comparison source
  capSample depth) :
    compared.capSummary.area = dyadicArea (ArcArea.Sample.capValue compared.sample) depth
      edge.left.parameter edge.right.parameter := by
  rw [compared.capSummary.area_eq, compared.capPath_eq]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _
    (ArcArea.Sample.capValue_left compared.sample)

/-- The original source and retained cap totals satisfy the cached parent budget times squared parameter width. -/
theorem total_error (compared : ComparedCell comparison source
  capSample depth)
    (budget : Budget data) (bounded : comparison.scale ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (compared.original.left.total - compared.capSummary.total) ≤
      quarterRadius budget.scale index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  rw [compared.original.left_total, compared.cap_total]
  exact (ArcComparison.Sample.increment_error compared.sample source).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (quarterRadius_mono bounded index)
      (Arithmetic.sq_nonneg_direct _))

/-- The original source and retained cap areas satisfy the cached parent area budget times fourth-power width. -/
theorem area_error (compared : ComparedCell comparison source
  capSample depth)
    (budget : Budget data) (bounded : comparison.scale ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (compared.original.left.area - compared.capSummary.area) ≤
      quarterRadius budget.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  rw [compared.original.left_area, compared.cap_area]
  exact (ArcArea.Sample.area_error_geometric source compared.sample depth).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (quarterRadius_mono (Budget.areaScale_le budget comparison bounded) index)
      (Arithmetic.pow_nonneg_direct (Arithmetic.sub_nonneg_direct cell.ordered.le) 4))

/-- The original source total satisfies the retained parent slope bound. -/
theorem left_bound (compared : ComparedCell comparison source
  capSample depth) (budget : Budget data) :
    Data.Gaussian.Norm.Basic.normSq compared.original.left.total ≤ budget.slope * (edge.right.parameter -
      edge.left.parameter) ^ 2 := by
  rw [budget.slope_eq]
  exact compared.original.left_bound

/-- The cached cap total satisfies the original parent slope and paid geometric discrepancy bound. -/
theorem cap_bound (compared : ComparedCell comparison source
  capSample depth)
    (budget : Budget data) (bounded : comparison.scale ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ 2 * (budget.slope +
      quarterRadius budget.scale index) *
      (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have estimate := ArcArea.Sample.cap_increment_bound source compared.sample ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le,
    le_rfl⟩
  rw [ArcArea.Sample.capValue_left compared.sample, Data.Gaussian.Basic.sub_zero, ArcArea.Sample.capValue_right
    compared.sample] at estimate
  rw [compared.cap_total, budget.slope_eq]
  exact estimate.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (quarterRadius_mono bounded index)) (by decide))
    (Arithmetic.sq_nonneg_direct _))

end ComparedCell
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
