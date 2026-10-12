module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Literal cap paths over the complete retained parent mesh

Every compared block keeps its original source/reciprocal area record.
The new path is assembled from cached cap-block summaries, including the
cross terms of their endpoint totals. Source provenance is exact.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells (ComparedCell)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- A dependent spine of original reciprocal area cells and their cached cap paths.

Every entry is indexed by the retained comparison bank, common source sample and finite depth; the original source paths
and summaries remain available. -/
inductive ComparedCells (source : UniformReciprocalPrimitives.SourcePrimitive data index) (capSample : Primitives.Sample
  cap differential index box)
    (depth : Nat) : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → ParentBank.Bank regular data edges
      → Type
  /-- The empty original comparison bank has no compared area cells. -/ | nil :
    ComparedCells source capSample depth .nil
  /-- Prepend one retained original area cell and its cap comparison to the exact tail bank. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      (head : ParentCells.ComparedCell comparison source capSample depth) (tail :
        ComparedCells source capSample depth bank) :
      ComparedCells source capSample depth (.cons
        comparison bank)

constructive_injectivity ComparedCells

namespace ComparedCells

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells in
/-- Reuse every original area cell and attach its cap path on the shared retained polynomial sample. -/
def build (capSample : Primitives.Sample cap differential index box) : {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} →
    (bank : ParentBank.Bank regular data edges) → ReciprocalBoundaryArea.AreaCells source depth edges →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank
  | _, .nil, .nil => .nil
  | _, .cons comparison bank, .cons original rest =>
      .cons (ComparedCell.build comparison capSample original)
        (build capSample bank rest)

/-- Read back the original reciprocal area-cell spine from the retained comparison bank. -/
def original : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank →
      ReciprocalBoundaryArea.AreaCells source depth edges
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.original tail.original

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells in
/-- Building cap comparisons preserves exactly the original area-cell spine. -/
theorem build_original {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank : ParentBank.Bank regular
  data edges)
    (original : ReciprocalBoundaryArea.AreaCells source depth edges) :
      (build capSample bank original).original =
      original := by
  induction bank with
  | nil => cases original; rfl
  | cons comparison bank ih =>
      cases original with
      | cons head tail => exact congrArg (AreaCells.cons head) (ih tail)

/-- Read the original source and retained cap increment paths in their actual cell order. -/
def pairs : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank → List (List
      InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head tail => (head.original.leftPath, head.capPath) :: tail.pairs

/-- The retained path-pair bank has exactly one entry per original covered edge. -/
theorem pairs_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges} (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth
  bank) :
    cells.pairs.length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Append the cached original source summaries, retaining their exact cross terms. -/
def leftSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) →
      IncrementArea.Summary (cells.pairs.map Prod.fst).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head tail => head.original.left.append tail.leftSummary

/-- Append the cached original cap summaries, retaining their exact cross terms. -/
def capSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) →
      IncrementArea.Summary (cells.pairs.map Prod.snd).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head tail => head.capSummary.append tail.capSummary

/-- The retained comparison spine reads back exactly the original source path list. -/
theorem left_paths {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) :
    cells.pairs.map Prod.fst = cells.original.pairs.map Prod.fst := by
  induction cells with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head.original.leftPath) ih

/-- The original complete source path total is its actual endpoint primitive difference. -/
theorem source_total (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) :
    cells.leftSummary.total = source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [cells.leftSummary.total_eq, cells.left_paths, ← cells.original.leftSummary.total_eq]
  exact cells.original.source_total mesh

/-- The retained complete source area is the original finite dyadic area at the combined mesh and cell depth. -/
theorem source_area (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) :
    cells.leftSummary.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval
        (parent.edge.point 0))
      (mesh.depth + depth) 0 1 := by
  rw [cells.leftSummary.area_eq, cells.left_paths, ← cells.original.leftSummary.area_eq]
  exact cells.original.source_area mesh

/-- Read the original source-minus-cap total discrepancy of every retained cell. -/
def errors : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => (head.original.left.total - head.capSummary.total) :: tail.errors

/-- Read the actual cached original cap increment of every cell. -/
def increments : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => head.sample.increment :: tail.increments

/-- The retained cap path total is the sum of its original cached cell increments. -/
theorem cap_total {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) :
    cells.capSummary.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.increments := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      change head.capSummary.total + tail.capSummary.total = head.sample.increment +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.increments
      rw [head.cap_total, ih]

/-- There is exactly one retained source-to-cap discrepancy for each original covered edge. -/
theorem errors_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges} (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth
  bank) :
    cells.errors.length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The original retained cell discrepancies sum to the source total minus the cap total. -/
theorem errors_sum {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} (cells : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.errors = cells.leftSummary.total - cells.capSummary.total := by
  induction cells with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons head tail ih =>
      change (head.original.left.total - head.capSummary.total) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        tail.errors =
        (head.original.left.total + tail.leftSummary.total) - (head.capSummary.total + tail.capSummary.total)
      rw [ih]
      ring1

end ComparedCells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
