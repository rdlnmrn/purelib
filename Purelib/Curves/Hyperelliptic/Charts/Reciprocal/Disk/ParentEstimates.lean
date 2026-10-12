module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Branches
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization

/-!
# Complete parent integral and area error, including all block cross terms

The finite cell-count factors cancel against the actual dyadic widths.
Both estimates use one cached parent budget and hold at every additional
fine spatial depth. Source and cap summaries refer to their literal paths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEstimates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank Budget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint dyadicEdges_width)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_eq_mul_pow)

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

namespace ComparedCells

/-- Every original cell total discrepancy satisfies the retained common budget weighted by its exact dyadic width. -/
private theorem errors_bounded (mesh : UniformReciprocalCover.Mesh data) (budget : ParentBank.Budget data) {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    {bank : ParentBank.Bank regular data edges} (cells : ParentPaths.ComparedCells source capSample depth bank) (bounded
      : bank.Bounded budget.scale)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ value ∈ cells.errors, Data.Gaussian.Norm.Basic.normSq value ≤ Geometric.Basic.quarterRadius budget.scale
      index * Geometric.Basic.quarterRadius 1 mesh.depth := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining cell comparison bank head tail ih =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst value
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth UniformPrimitiveMesh.firstEndpoint
          UniformPrimitiveMesh.lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : InverseRootPolynomial.Coordinate) := by decide
        rw [unit] at width
        exact (head.total_error budget bounded.1).trans_eq (by rw [width])
      · exact ih bounded.2 (fun other found => members other (List.mem_cons_of_mem _ found)) value member

/-- The total of the complete literal cap path is compared directly with that of the retained source path, paying both
finite cell-count factors. -/
theorem whole_total_error (mesh : UniformReciprocalCover.Mesh data) (budget : ParentBank.Budget data) {bank :
  ParentBank.Bank regular data mesh.edges}
    (cells : ParentPaths.ComparedCells source capSample depth bank) (bounded : bank.Bounded budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (cells.leftSummary.total - cells.capSummary.total) ≤
      Geometric.Basic.quarterRadius budget.scale index := by
  rw [← cells.errors_sum]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le cells.errors _
    (errors_bounded mesh budget cells bounded
      (fun _ member => member))
  rw [cells.errors_length, mesh.edges_length, mesh.edgeCount_eq] at estimate
  apply estimate.trans_eq
  calc
    _ = Geometric.Basic.quarterRadius budget.scale index *
        (((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) * (((2 ^ mesh.depth : Nat) :
          InverseRootPolynomial.Coordinate) * Geometric.Basic.quarterRadius 1 mesh.depth)) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel, Fraction.Field.mul_one_direct]

/-- Each original path pair retains area, total-error and both total-magnitude bounds at the actual common dyadic width.
-/
private theorem bounds (mesh : UniformReciprocalCover.Mesh data) (budget : ParentBank.Budget data) {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    {bank : ParentBank.Bank regular data edges} (cells : ParentPaths.ComparedCells source capSample depth bank) (bounded
      : bank.Bounded budget.scale)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ pair ∈ cells.pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤
        Geometric.Basic.quarterRadius budget.areaScale index * (Geometric.Basic.quarterRadius 1 mesh.depth) ^ 2 ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ Geometric.Basic.quarterRadius budget.scale index *
        Geometric.Basic.quarterRadius 1 mesh.depth ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 *
        (budget.slope + Geometric.Basic.quarterRadius budget.scale index) * Geometric.Basic.quarterRadius 1 mesh.depth ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 *
        (budget.slope + Geometric.Basic.quarterRadius budget.scale index) * Geometric.Basic.quarterRadius 1 mesh.depth
        := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining cell comparison bank head tail ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth UniformPrimitiveMesh.firstEndpoint
          UniformPrimitiveMesh.lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : InverseRootPolynomial.Coordinate) := by decide
        rw [unit] at width
        change Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea head.original.leftPath -
          IncrementArea.pathArea head.capPath) ≤ _ ∧
          Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum head.original.leftPath
            - Data.Gaussian.Norm.Sum.Basic.gaussianSum head.capPath) ≤ _ ∧
          Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            head.original.leftPath) ≤ _ ∧ Data.Gaussian.Norm.Basic.normSq
            (Data.Gaussian.Norm.Sum.Basic.gaussianSum head.capPath) ≤ _
        rw [← head.original.left.area_eq, ← head.capSummary.area_eq, ← head.original.left.total_eq, ←
          head.capSummary.total_eq]
        refine ⟨(head.area_error budget bounded.1).trans_eq ?_, (head.total_error budget bounded.1).trans_eq (by
            rw [width]), ?_,
          (head.cap_bound budget bounded.1).trans_eq (by rw [width])⟩
        · rw [show (edge.right.parameter - edge.left.parameter) ^ 4 = ((edge.right.parameter - edge.left.parameter) ^ 2)
            ^ 2 by ring1, width]
        · have slopeLe : budget.slope ≤ 2 * (budget.slope + Geometric.Basic.quarterRadius budget.scale index) := by
            have errorNonnegative := Geometric.Basic.quarterRadius_nonneg budget.nonnegative index
            exact (le_add_of_nonneg_right errorNonnegative).trans
              ((le_add_of_nonneg_right (add_nonneg budget.slope_nonnegative errorNonnegative)).trans_eq (by ring1))
          exact (head.left_bound budget).trans
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct slopeLe
              (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by rw [width]))
      · exact ih bounded.2 (fun other found => members other (List.mem_cons_of_mem _ found)) pair member

/-- The whole literal reciprocal path pays internal area errors AND the polygon of block totals. No fine depth or coarse
cell count is hidden. -/
theorem whole_area_bound (mesh : UniformReciprocalCover.Mesh data) (budget : ParentBank.Budget data) {bank :
  ParentBank.Bank regular data mesh.edges}
    (cells : ParentPaths.ComparedCells source capSample depth bank) (bounded : bank.Bounded budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (cells.leftSummary.area - cells.capSummary.area) ≤
      2 * (Geometric.Basic.quarterRadius budget.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth +
        32 * Geometric.Basic.quarterRadius budget.scale index * (budget.slope + Geometric.Basic.quarterRadius
          budget.scale index)) := by
  rw [cells.leftSummary.area_eq, cells.capSummary.area_eq]
  have bounded := bounds mesh budget cells
    bounded (fun _ member => member)
  have estimate := IncrementAreaComparison.blocks_area_difference_bound cells.pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg budget.nonnegative index)
      (Geometric.Basic.quarterRadius_nonneg (by decide) mesh.depth))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg budget.slope_nonnegative (Geometric.Basic.quarterRadius_nonneg budget.nonnegative index)))
      (Geometric.Basic.quarterRadius_nonneg (by decide) mesh.depth))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [cells.pairs_length] at estimate
  have countWidth : (mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1
    mesh.depth = 1 := by
    rw [mesh.edges_length, mesh.edgeCount_eq]
    exact (by ring1 : (((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1
      mesh.depth) =
      ((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) * (((2 ^ mesh.depth : Nat) :
        InverseRootPolynomial.Coordinate) * Geometric.Basic.quarterRadius 1 mesh.depth)).trans
      (DyadicCount.dyadic_count_cancel 1 mesh.depth)
  apply estimate.trans_eq
  calc
    _ = 2 * (Geometric.Basic.quarterRadius budget.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth *
        ((mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1 mesh.depth) +
        32 * Geometric.Basic.quarterRadius budget.scale index * (budget.slope + Geometric.Basic.quarterRadius
          budget.scale index) *
          ((mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1 mesh.depth) ^ 2)
            := by ring1
    _ = _ := by rw [countWidth]; ring1

/-- A single pre-index scale pays the entire concatenated path area at every fine spatial depth. The geometric rate has
no count-dependent floor. -/
theorem whole_area_error (mesh : UniformReciprocalCover.Mesh data) (budget : ParentBank.Budget data) {bank :
  ParentBank.Bank regular data mesh.edges}
    (cells : ParentPaths.ComparedCells source capSample depth bank) (bounded : bank.Bounded budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (cells.leftSummary.area - cells.capSummary.area) ≤
      Geometric.Basic.quarterRadius budget.boundaryAreaScale index := by
  have errorLe : Geometric.Basic.quarterRadius budget.scale index ≤ budget.scale := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone budget.nonnegative (Nat.zero_le index)
  have widthLe : Geometric.Basic.quarterRadius (1 : InverseRootPolynomial.Coordinate) mesh.depth ≤ 1 := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) (Nat.zero_le mesh.depth)
  have fineBound : Geometric.Basic.quarterRadius budget.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth ≤
    Geometric.Basic.quarterRadius budget.areaScale index := by
    simpa only [Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthLe (Geometric.Basic.quarterRadius_nonneg
        budget.areaScale_nonnegative index)
  have coarseBound : 32 * Geometric.Basic.quarterRadius budget.scale index * (budget.slope +
    Geometric.Basic.quarterRadius budget.scale index) ≤
      32 * Geometric.Basic.quarterRadius budget.scale index * (budget.slope + budget.scale) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl errorLe)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Geometric.Basic.quarterRadius_nonneg
        budget.nonnegative index))
  exact (whole_area_bound mesh budget cells
    bounded).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add fineBound coarseBound) (by
      decide)).trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, budget.boundaryAreaScale_eq, -eq_self, -iff_self]
      ring1))

end ComparedCells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEstimates
