module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEstimates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# One shared signed cap primitive on the complete retained parent

The prepared endpoint joins identify every cell's signed polynomial.
Flattening their actual increment paths gives the exact inverse-arc path
at the retained coarse depth plus the requested fine depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicIncrements_sum)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace RegularCells

/-- Read the retained common signed cap primitive from the first comparison cell, using the supplied cap sample for an
empty bank. -/
def primitive : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} →
    {retained : ParentPaths.ComparedCells source capSample depth bank} → RegularCells retained →
      InverseRootPolynomial.Polynomial
  | _, _, _, .nil => capSample.primitive.value
  | _, _, _, .cons head _ => head.alignment.primitive

/-- Read the first retained cell's cap sign, with the positive sign for an empty bank. -/
def flip : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges}
  →
    {retained : ParentPaths.ComparedCells source capSample depth bank} → RegularCells retained → Bool
  | _, _, _, .nil => false
  | _, _, _, .cons head _ => head.alignment.first.flip

/-- The retained common primitive is the supplied cap polynomial with exactly the cached sign. -/
theorem primitive_signed {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained) :
    primitive cells = if
      flip cells then -capSample.primitive.value
      else capSample.primitive.value := by
  cases cells with
  | nil => rfl
  | cons head tail => exact head.alignment.primitive_eq

/-- Every retained comparison cell uses the specified exact cap polynomial. -/
def WithPrimitive (value : InverseRootPolynomial.Polynomial) : {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
    {retained : ParentPaths.ComparedCells source capSample depth bank} → RegularCells retained → Prop
  | _, _, _, .nil => True
  | _, _, _, .cons head tail => head.alignment.primitive = value ∧
    WithPrimitive value tail

/-- The cached endpoint joins identify all retained cells' signed cap polynomials once the polynomial stage is at least
two. -/
theorem shared {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (later : 2 ≤ index) :
      WithPrimitive
      (primitive cells) cells := by
  induction cells with
  | nil => trivial
  | @cons edge remaining cell comparison bank originalHead originalTail head tail ih =>
      cases owners with
      | cons first rest =>
          cases tail with
          | nil => exact ⟨rfl, trivial⟩
          | @cons nextEdge remaining nextCell nextComparison nextBank originalNext originalRest next remainingCells =>
              cases rest with
              | cons nextOwner remainingOwners =>
                  have same := Join.primitive_eq links.head head.alignment next.alignment later
                  refine ⟨rfl, ?_⟩
                  change WithPrimitive
                    head.alignment.primitive (.cons next remainingCells)
                  rw [same]
                  exact ih (.cons nextOwner remainingOwners) links.tail

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent.RegularCells
/-- Each actual retained cap path is the dyadic increment path of the shared signed polynomial on its original cell
interval. -/
theorem cap_paths {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (value : InverseRootPolynomial.Polynomial) (shared :
      WithPrimitive value cells) :
    cells.pairs.map Prod.snd = edges.map (fun edge => DyadicPrimitivePaths.dyadicIncrements
      (fun parameter => value.eval (parent.edge.point parameter)⁻¹) depth edge.left.parameter edge.right.parameter) :=
        by
  induction cells with
  | nil => rfl
  | @cons edge remaining cell comparison bank originalHead originalTail head tail ih =>
      change head.capPath :: tail.pairs.map Prod.snd = _ :: _
      have path : head.capPath = DyadicPrimitivePaths.dyadicIncrements (fun parameter => value.eval (parent.edge.point
        parameter)⁻¹)
          depth edge.left.parameter edge.right.parameter := by
        rw [head.capPath_eq]
        change DyadicPrimitivePaths.dyadicIncrements (fun parameter => head.alignment.primitive.eval (parent.edge.point
          parameter)⁻¹ -
          head.alignment.primitive.eval (parent.edge.point edge.left.parameter)⁻¹) depth edge.left.parameter
            edge.right.parameter = _
        rw [DyadicPrimitivePaths.dyadicIncrements_sub_constant, shared.1]
      rw [path, ih shared.2]

/-- Flattening the retained cap-cell paths gives the shared primitive's exact whole-parent dyadic increment path. -/
theorem cap_path_eq (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (later : 2 ≤ index) :
    (cells.pairs.map Prod.snd).flatten = DyadicPrimitivePaths.dyadicIncrements
      (fun parameter => (primitive cells).eval
        (parent.edge.point parameter)⁻¹) (mesh.depth + depth) 0 1 := by
  have flatten (value : InverseRootPolynomial.Coordinate → InverseRootPolynomial.Gaussian) :
      (mesh.edges.map (fun edge => DyadicPrimitivePaths.dyadicIncrements value depth edge.left.parameter
        edge.right.parameter)).flatten =
        DyadicPrimitivePaths.dyadicIncrements value (mesh.depth + depth) 0 1 := by
    rw [mesh.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments]
    rfl
  exact (congrArg List.flatten (cap_paths cells
    (primitive cells) (shared cells owners links
    later))).trans (flatten _)

end

/-- The cached whole-cap total is the endpoint difference of the retained common signed polynomial. -/
theorem cap_total_eq (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (later : 2 ≤ index) :
    cells.capSummary.total = (primitive
      cells).eval (parent.edge.point 1)⁻¹ -
      (primitive cells).eval (parent.edge.point
      0)⁻¹ := by
  rw [cells.capSummary.total_eq, cap_path_eq mesh
    cells owners links later, DyadicPrimitivePaths.dyadicIncrements_sum]

/-- The cached whole-cap area is the anchored dyadic area of its retained common signed polynomial. -/
theorem cap_area_eq (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (later : 2 ≤ index) :
    cells.capSummary.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => (primitive cells).eval
        (parent.edge.point parameter)⁻¹ -
        (primitive cells).eval (parent.edge.point
        0)⁻¹)
      (mesh.depth + depth) 0 1 := by
  rw [cells.capSummary.area_eq, cap_path_eq mesh
    cells owners links later,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant _
      ((primitive cells).eval (parent.edge.point
      0)⁻¹)]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (Data.Gaussian.Basic.sub_self _)

/-- Negating every value leaves its finite dyadic signed area unchanged. -/
private theorem dyadicArea_neg (values : InverseRootPolynomial.Coordinate → InverseRootPolynomial.Gaussian) (depth :
  Nat) (first last : InverseRootPolynomial.Coordinate) :
    DyadicBoundaryRibbon.dyadicArea (fun parameter => -values parameter) depth first last =
      DyadicBoundaryRibbon.dyadicArea values depth first last := by
  induction depth generalizing first last with
  | zero =>
      rw [DyadicBoundaryRibbon.dyadicArea_zero, DyadicBoundaryRibbon.dyadicArea_zero]
      apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
  | succ depth ih => rw [DyadicBoundaryRibbon.dyadicArea_succ, DyadicBoundaryRibbon.dyadicArea_succ, ih, ih]

/-- Negating the common primitive leaves its anchored area unchanged. The parent area therefore uses the very polynomial
supplied to cap energy. -/
theorem cap_area_unsigned (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (later : 2 ≤ index) :
    cells.capSummary.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => capSample.primitive.value.eval (parent.edge.point parameter)⁻¹ -
        capSample.primitive.value.eval (parent.edge.point 0)⁻¹) (mesh.depth + depth) 0 1 := by
  rw [cap_area_eq mesh cells owners links later,
    primitive_signed cells]
  have signed (value : InverseRootPolynomial.Polynomial) (bit : Bool) :
      DyadicBoundaryRibbon.dyadicArea (fun parameter => (if bit then -value else value).eval (parent.edge.point
        parameter)⁻¹ -
        (if bit then -value else value).eval (parent.edge.point 0)⁻¹) (mesh.depth + depth) 0 1 =
      DyadicBoundaryRibbon.dyadicArea (fun parameter => value.eval (parent.edge.point parameter)⁻¹ -
        value.eval (parent.edge.point 0)⁻¹) (mesh.depth + depth) 0 1 := by
    cases bit with
    | false => rfl
    | true =>
        change DyadicBoundaryRibbon.dyadicArea (fun parameter => (-value).eval (parent.edge.point parameter)⁻¹ -
          (-value).eval (parent.edge.point 0)⁻¹) _ _ _ = _
        have terms (parameter : InverseRootPolynomial.Coordinate) : (-value).eval (parent.edge.point parameter)⁻¹ -
            (-value).eval (parent.edge.point 0)⁻¹ =
            -(value.eval (parent.edge.point parameter)⁻¹ - value.eval (parent.edge.point 0)⁻¹) := by
          rw [DensePolynomial.eval_neg, DensePolynomial.eval_neg]
          ring1
        exact (DyadicBoundaryRibbon.dyadicArea_congr terms _ _ _).trans
          (dyadicArea_neg _ _ _ _)
  exact signed _ _

end RegularCells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
