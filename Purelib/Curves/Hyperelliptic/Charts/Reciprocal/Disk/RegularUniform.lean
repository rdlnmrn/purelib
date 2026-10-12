module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-!
# One requested subdivision depth for the retained regular cap path

All original parents and their reciprocal covers are reused. A common
subdivision changes only the sampled polynomial paths. Exact endpoint totals
remove cross-term error, and the aggregate bound pays the full parent count.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {regular :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {index : Nat} {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}

namespace Preparation

/-- The mesh depth of the original retained cover. -/
@[expose] def coarseDepth (_prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  : Nat := cover.mesh.depth

/-- The unsigned primitive increment path on the same original inverse parent at one uniform depth. -/
@[expose] def uniformPrimitivePath (_prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation
  regular cover) (value : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat) : List Gaussian :=
  Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value.eval ((parent.edge.point parameter)⁻¹))
    depth 0 1

/-- The uniform primitive path area equals its original anchored dyadic area. -/
theorem uniform_area (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover) (value
  : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat) :
    Path.IncrementArea.pathArea (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath
      prepared value depth) = Path.Dyadic.DyadicBoundaryRibbon.dyadicArea
      (fun parameter => value.eval ((parent.edge.point parameter)⁻¹) - value.eval ((parent.edge.point 0)⁻¹)) depth 0 1
        := by
  unfold Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath
  rw [← Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sub_constant _ (value.eval ((parent.edge.point 0)⁻¹))]
  exact Path.Dyadic.DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (Gaussian.Basic.sub_self _)

/-- A sufficient uniform depth preserves the original quarter-radius area refinement bound. -/
theorem refinement_bound (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  (bounds : Cap.EnergyBounds sample)
    (fine common : Nat) (later : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth prepared +
      fine ≤ common) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath prepared
      sample.primitive.value common) -
      Path.IncrementArea.pathArea
        (Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath prepared
        sample.primitive.value fine)) ≤ Rational.Geometric.Basic.quarterRadius
        (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds) fine := by
  change Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath prepared
    sample.primitive.value common) -
    Path.IncrementArea.pathArea (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath
      prepared sample.primitive.value (cover.mesh.depth + fine))) ≤ _
  rw [Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniform_area prepared,
    Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniform_area prepared]
  have estimate := Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_refinement_bound bounds data.boundary
    (cover.mesh.depth + fine) (common - (cover.mesh.depth + fine))
  change cover.mesh.depth + fine ≤ common at later
  rw [Data.Nat.Subtraction.add_sub_of_le later] at estimate
  exact estimate.trans (quarterRadius_antitone
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale_nonnegative bounds) (Nat.le_add_left fine
    cover.mesh.depth))

/-- The uniform path total is bounded by the original retained arc slope. -/
theorem uniform_total_bound (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  (bounds : Cap.EnergyBounds sample) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath prepared
      sample.primitive.value depth)) ≤ Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath,
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum]
  have estimate := Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_increment_le bounds data.boundary (left :=
    0) (right := 1) (by decide) (by decide)
  exact estimate.trans_eq (by
    rw [
      show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 by decide];
    ring1)

end Preparation

namespace SideBank

/-- The finite maximum of the original side preparations' coarse depths. -/
@[expose] def maximumDepth : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  → {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => max (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth head)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth tail)

/-- The ordered uniform primitive paths on the original retained side parents. -/
@[expose] def uniformPrimitivePaths (value : Normalization.InverseRootPolynomial.Polynomial) (common : Nat) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers → List (List
      Normalization.InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head tail => Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath head
    value common :: Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths
    value common tail

/-- Pair each original side path with its uniform refinement in the same order. -/
private def refinementPairs (value : Normalization.InverseRootPolynomial.Polynomial) (fine common : Nat) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers → List (List
      Normalization.InverseRootPolynomial.Gaussian × List Normalization.InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head tail =>
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath head value common,
        Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath head value fine) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs value fine common
          tail

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}

/-- The two projections of the refinement pairs are exactly the uniform and original path lists. -/
private theorem refinementPairs_paths (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular
  covers) (value : Normalization.InverseRootPolynomial.Polynomial) (fine common : Nat) :
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs value fine common prepared).map
      Prod.fst = Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths value common
      prepared ∧
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs value fine common prepared).map
        Prod.snd = Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value fine
        prepared := by
  induction prepared with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih => exact ⟨congrArg (List.cons _) ih.1, congrArg (List.cons _) ih.2⟩

/-- The refinement pair list has exactly the original side count. -/
private theorem refinementPairs_length (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular
  covers) (value : Normalization.InverseRootPolynomial.Polynomial) (fine common : Nat) :
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs value fine common prepared).length =
      parents.length := by
  induction prepared with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

/-- Each original pair has the retained area error, identical totals and the original slope bounds. -/
private theorem refinementPairs_bounds (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular
  covers) (bounds : Cap.EnergyBounds sample)
    (fine common : Nat) (later : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth prepared +
      fine ≤ common) :
    ∀ pair ∈ Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs sample.primitive.value fine
      common prepared,
      Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea pair.1 - Path.IncrementArea.pathArea pair.2) ≤
        Rational.Geometric.Basic.quarterRadius (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds)
        fine ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 0 ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤
        Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds ∧ Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope
        bounds := by
  induction prepared with
  | nil => intro pair member; cases member
  | cons head tail ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · have headLater : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth head + fine ≤
          common :=
          (Nat.add_le_add_right (Data.Nat.Order.le_max_left
            (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth head)
            (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth tail)) fine).trans later
        refine ⟨Preparation.refinement_bound head bounds fine common headLater, ?_,
          Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniform_total_bound head bounds common, ?_⟩
        · change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements _ common 0 1) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements _ _ 0 1)) ≤ 0
          rw [Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum,
            Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum, Gaussian.Basic.sub_self,
            Gaussian.Norm.Basic.normSq_zero]
        · exact Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniform_total_bound head bounds
            (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth head + fine)
      · exact ih ((Nat.add_le_add_right (Data.Nat.Order.le_max_right
          (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.coarseDepth head)
          (maximumDepth tail)) fine).trans later) pair member

/-- The entire path is compared, including its polygon of parent totals.
The two actual totals agree parent by parent, so its cross-term error is zero. -/
theorem uniform_area_bound (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) (bounds
  : Cap.EnergyBounds sample)
    (fine common : Nat) (later : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth prepared +
      fine ≤ common) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths sample.primitive.value common
      prepared).flatten -
      Path.IncrementArea.pathArea
        (Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths sample.primitive.value
        fine prepared).flatten) ≤
        Rational.Geometric.Basic.quarterRadius (2 * (parents.length : Normalization.InverseRootPolynomial.Coordinate) ^
          2 * (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds)) fine := by
  have estimates := Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs_bounds prepared bounds
    fine common later
  have bound := Path.IncrementAreaComparison.blocks_area_difference_bound
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs sample.primitive.value fine common
    prepared)
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 0)
      (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope_nonnegative bounds)
    (fun pair member => (estimates pair member).1) (fun pair member => (estimates pair member).2.1)
    (fun pair member => (estimates pair member).2.2.1) (fun pair member => (estimates pair member).2.2.2)
  rw [(Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs_paths prepared
    sample.primitive.value fine common).1,
    (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs_paths prepared sample.primitive.value
      fine common).2,
    Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.refinementPairs_length prepared] at bound
  exact bound.trans_eq (by
      simp only [Rational.Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self];
      ring1)

end SideBank

namespace Path

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}

set_option genInjectivity false in
/-- A finite area request retains the existing polynomial bounds and the
coarse maximum; later consumers read both instead of scanning the covers again. -/
structure UniformAreaRequest (prepared : Preparation regular parents)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (target :
      Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original retained regular arc bounds. -/ bounds :
    Cap.EnergyBounds sample
  /-- The cached original side count. -/ count : Nat
  /-- The count is exactly the original retained side-bank length. -/ count_eq : count = parents.length
  /-- The cached largest original side coarse depth. -/ coarseDepth : Nat
  /-- The cached coarse depth is the original side-bank maximum. -/ coarseDepth_eq : coarseDepth =
    Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth prepared.bank
  /-- The cached whole-path area refinement scale. -/ scale : Normalization.InverseRootPolynomial.Coordinate
  /-- The scale is twice the original count squared times its retained area scale. -/ scale_eq : scale = 2 * (count :
    Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale
    bounds)
  /-- The retained whole-path scale is nonnegative. -/ scale_nonnegative : 0 ≤ scale
  /-- The cached sufficient fine refinement depth. -/ depth : Nat
  /-- The fine depth is the original finite quarter-radius search result. -/ depth_eq : depth =
    Rational.Geometric.Search.firstQuarterBelow scale minimum target
  /-- The retained fine depth respects the original minimum. -/ minimum_le : minimum ≤ depth
  /-- The cached whole-path quarter-radius error. -/ error : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached error is exactly the original retained scale times the selected quarter radius. -/ error_eq : error =
    Rational.Geometric.Basic.quarterRadius scale depth
  /-- The retained whole-path error fits the requested target. -/ accurate : error < target

constructive_injectivity UniformAreaRequest

namespace UniformAreaRequest

/-- Cache the original side count, maximum coarse depth and area scale, then retain their finite sufficient-depth
certificate. -/
@[expose] def build (prepared : Preparation regular parents) (bounds :
  Cap.EnergyBounds sample)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest prepared sample target minimum := by
  let count := parents.length
  let coarseDepth := Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth prepared.bank
  let scale := 2 * (count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds)
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale_nonnegative bounds)
  let depth := Rational.Geometric.Search.firstQuarterBelow scale minimum target
  exact ⟨bounds, count, rfl, coarseDepth, rfl, scale, rfl, nonnegative, depth, rfl,
    Rational.Geometric.Search.firstQuarterBelow_ge scale minimum target, Rational.Geometric.Basic.quarterRadius scale
      depth, rfl,
    Rational.Geometric.Search.firstQuarterBelow_accurate scale nonnegative minimum target positive⟩

variable {prepared : Preparation regular parents} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum :
  Nat}
  {totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floor fine readingIndex : Nat}
  {capRequest : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared totalTarget areaTarget
    floor}

set_option genInjectivity false in
/-- Only the new uniform subdivision is sampled. The original cap area is
read from the supplied comparison cache, with no new root preparation. -/
structure Evaluation (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest prepared
  sample target minimum)
    (original : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Evaluation capRequest sample fine
      readingIndex) (common : Nat) where
  /-- The evaluated fine depth is at least the retained sufficient depth. -/ fine_later : request.depth ≤ fine
  /-- The shared depth covers every original coarse depth together with the evaluated fine depth. -/ coarse_later :
    request.coarseDepth + fine ≤ common
  /-- The cached ordered uniform paths on the original side parents. -/ paths : List (List
    Normalization.InverseRootPolynomial.Gaussian)
  /-- These paths are exactly the original uniform side-bank evaluation. -/ paths_eq : paths =
    Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths sample.primitive.value common
    prepared.bank
  /-- The cached flattening of the original ordered uniform paths. -/ path : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached whole path is exactly their ordered flattening. -/ path_eq : path = paths.flatten
  /-- The cached summary of that same complete uniform path. -/ summary : Path.IncrementArea.Summary path
  /-- The actual uniform full area differs from the original cached cap by at most the retained requested error. -/
    area_error : Data.Gaussian.Norm.Basic.normSq (summary.area - original.cap.area) < target

constructive_injectivity Evaluation

/-- Evaluate only the new uniform paths at sufficient coarse and fine depths, retaining the original cap comparison and
cached full summary. -/
@[expose] def evaluate (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest prepared
  sample target minimum)
    (original : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Evaluation capRequest sample fine
      readingIndex) (common : Nat)
    (fineLater : request.depth ≤ fine) (coarseLater : request.coarseDepth + fine ≤ common) :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest.Evaluation request original common :=
      by
  let paths := Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths sample.primitive.value
    common prepared.bank
  let path := paths.flatten
  let summary := Path.IncrementArea.Summary.build path
  refine ⟨fineLater, coarseLater, paths, rfl, path, rfl, summary, ?_⟩
  rw [summary.area_eq, original.cap_area_unsigned]
  have later : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.maximumDepth prepared.bank + fine ≤ common
    := by rw [← request.coarseDepth_eq]; exact coarseLater
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniform_area_bound prepared.bank
    request.bounds fine common later
  have scaleEq : 2 * (parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale request.bounds) = request.scale := by
    rw [request.scale_eq, request.count_eq]
  rw [scaleEq] at bounded
  exact bounded.trans_lt ((quarterRadius_antitone request.scale_nonnegative
    fineLater).trans_lt
    (request.error_eq ▸ request.accurate))

end UniformAreaRequest
end Path
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
