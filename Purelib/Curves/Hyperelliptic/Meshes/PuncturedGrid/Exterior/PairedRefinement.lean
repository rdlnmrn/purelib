module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Group.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedUniformPaths
import Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Refinement of the full paired exterior cap path. All retained parents
are paid; their endpoint totals stay exact under further subdivision. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement
open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source target :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap}

/-- Evaluate two retained polynomials at the reciprocal point of one original parent parameter. -/
@[expose] def pairedParentValues (left right : InverseRootPolynomial.Polynomial) (parent :
  Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  ⟨left.eval ((parent.edge.point parameter)⁻¹), right.eval ((parent.edge.point parameter)⁻¹)⟩

/-- Every retained paired parent path totals to its exact two-component endpoint difference, independently of
subdivision depth. -/
theorem pairedUniformPaths_totals (left right : InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (bank : Disk.ParentJoins.SideBank regular covers) :
    (bank.pairedUniformPaths left right depth).map Path.PairedIncrementArea.total =
      parents.map (fun parent => (PairedRefinement.pairedParentValues left
        right parent 1).sub (PairedRefinement.pairedParentValues left right
        parent 0)) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      change Path.PairedIncrementArea.total (Path.Dyadic.DyadicPairedPrimitivePaths.increments _ depth 0 1) :: _ = _
      rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_total, ih]
      rfl

/-- Subtracting parent-area sums cancels their unchanged endpoint chords pointwise. -/
private theorem area_sums_difference (left right : InverseRootPolynomial.Polynomial) (coarse fine : Nat)
    (parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)) :
    Gaussian.Norm.Sum.Basic.gaussianSum (parents.map (fun parent =>
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues left right parent) (coarse +
        fine) 0 1 -
        Topology.Polygon.Stokes.edgeArea
          (PairedRefinement.pairedParentValues left right parent 0)
          (PairedRefinement.pairedParentValues left right parent 1))) -
    Gaussian.Norm.Sum.Basic.gaussianSum (parents.map (fun parent =>
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues left right parent) coarse 0 1 -
        Topology.Polygon.Stokes.edgeArea
          (PairedRefinement.pairedParentValues left right parent 0)
          (PairedRefinement.pairedParentValues left right parent 1))) =
    Gaussian.Norm.Sum.Basic.gaussianSum (parents.map (fun parent =>
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues left right parent) (coarse +
        fine) 0 1 -
        Periods.DyadicBilinearBoundaryRibbon.dyadicArea
          (PairedRefinement.pairedParentValues left right parent) coarse 0
          1)) := by
  induction parents with
  | nil => change (0 : InverseRootPolynomial.Gaussian) - 0 = 0; ring1
  | cons parent rest ih =>
      change (_ + _) - (_ + _) = _ + _
      rw [show ∀ a b c d : InverseRootPolynomial.Gaussian, (a + b) - (c + d) = (a - c) + (b - d) from
        fun a b c d => by ring1, ih]
      ring1

/-- The complete paired-path area change is the sum of the original parents' dyadic area changes.

Exact retained endpoint totals cancel the polygon contribution across the two subdivision depths. -/
theorem pairedUniformPaths_refinement_eq (left right : InverseRootPolynomial.Polynomial) (coarse fine :
  Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (bank : Disk.ParentJoins.SideBank regular covers) :
    Path.PairedIncrementArea.area (bank.pairedUniformPaths left right (coarse + fine)).flatten -
      Path.PairedIncrementArea.area (bank.pairedUniformPaths left right coarse).flatten =
    Gaussian.Norm.Sum.Basic.gaussianSum (parents.map (fun parent =>
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues left right parent) (coarse +
        fine) 0 1 -
        Periods.DyadicBilinearBoundaryRibbon.dyadicArea
          (PairedRefinement.pairedParentValues left right parent) coarse 0
          1)) := by
  rw [bank.pairedUniformPaths_area, bank.pairedUniformPaths_area,
    PairedRefinement.pairedUniformPaths_totals _ _ _ bank,
      PairedRefinement.pairedUniformPaths_totals _ _ _ bank,
      Algebra.Group.add_sub_add_right_eq_sub]
  exact PairedRefinement.area_sums_difference left right coarse fine parents

variable {index otherIndex : Nat} {box otherBox : Rational.Box}
  {sample : Cap.Primitives.Sample cap source index box}
  {otherSample : Cap.Primitives.Sample cap target otherIndex otherBox}

/-- Bound one original boundary parent's paired dyadic area change by the common cap-slope scale.

Both component energy bounds use the same parent geometry, and the coarse depth determines the geometric error. -/
private theorem parent_refinement (left : Cap.EnergyBounds sample)
    (right : Cap.EnergyBounds otherSample)
    {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent
      (Branches.Cuts.Ambient curve)) (coarse fine : Nat) :
    Gaussian.Norm.Basic.normSq (Periods.DyadicBilinearBoundaryRibbon.dyadicArea
      (PairedRefinement.pairedParentValues sample.primitive.value
      otherSample.primitive.value parent)
        (coarse + fine) 0 1 -
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues sample.primitive.value
        otherSample.primitive.value parent)
        coarse 0 1) ≤ Basic.quarterRadius (4 * (max
          (Cap.RefinementArea.arcSlope left)
          (Cap.RefinementArea.arcSlope right))^2) coarse := open Data.Rat in by
  have recast : PreparedBoundarySegments.ParentOnBoundary (Integration.PreparedEdgeRecasting.recastCenteredEdge target
    parent) (Branches.Cuts.Ambient curve) :=
    ⟨boundary.startInside, boundary.finishInside, boundary.side⟩
  have bounded (a b : InverseRootPolynomial.Coordinate) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((PairedRefinement.pairedParentValues sample.primitive.value
          otherSample.primitive.value parent b).sub
        (PairedRefinement.pairedParentValues sample.primitive.value
          otherSample.primitive.value parent a))
          (max (Cap.RefinementArea.arcSlope left)
            (Cap.RefinementArea.arcSlope right) * (b - a)^2) := by
    have recastPoint (parameter : InverseRootPolynomial.Coordinate) :
        (recastCenteredEdge target parent).edge.point parameter = parent.edge.point parameter := rfl
    constructor
    · simpa only [PairedRefinement.pairedParentValues,
        PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        ((Cap.RefinementArea.parent_increment_le left) boundary ha hb).trans
          (Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_left _ _)
            (Arithmetic.sq_nonneg_direct _))
    · simpa only [PairedRefinement.pairedParentValues,
        PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, recastPoint, -eq_self, -iff_self] using
        ((Cap.RefinementArea.parent_increment_le right) recast ha hb).trans
          (Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right _ _)
            (Arithmetic.sq_nonneg_direct _))
  have estimate := Path.Dyadic.DyadicPairedAreaRefinement.dyadicArea_refinement_bound _
    ((Cap.RefinementArea.arcSlope_nonnegative left).trans
      (Fraction.Order.Basic.le_max_left _ _)) bounded coarse fine
    (first := 0) (last := 1) (by decide) (by decide) (by decide)
  exact estimate.trans_eq (by
    rw [
      show ((1 : InverseRootPolynomial.Coordinate) - 0)^4 = 1 by decide];
    ring1)

/-- The complete original parent count is paid once, independently of both
the old reciprocal covers and the number of later dyadic children. -/
theorem pairedUniformPaths_refinement_bound (left : Cap.EnergyBounds
  sample)
    (right : Cap.EnergyBounds otherSample) (coarse fine : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (bank : Disk.ParentJoins.SideBank regular covers) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
        (bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value (coarse + fine)).flatten -
      Path.PairedIncrementArea.area
        (bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value coarse).flatten) ≤
      Basic.quarterRadius ((parents.length : InverseRootPolynomial.Coordinate)^2 * (4 *
        (max (Cap.RefinementArea.arcSlope left)
        (Cap.RefinementArea.arcSlope right))^2)) coarse := by
  have bounds : ∀ value ∈ parents.map (fun parent =>
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues sample.primitive.value
        otherSample.primitive.value parent)
        (coarse + fine) 0 1 -
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea
        (PairedRefinement.pairedParentValues sample.primitive.value
        otherSample.primitive.value parent)
        coarse 0 1), Gaussian.Norm.Basic.normSq value ≤ Basic.quarterRadius (4 * (max
          (Cap.RefinementArea.arcSlope left)
          (Cap.RefinementArea.arcSlope right))^2) coarse := by
    induction bank with
    | nil => intro value member; cases member
    | @cons parent parents patch data cover covers head tail ih =>
        intro value member
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact PairedRefinement.parent_refinement left right data.boundary
            coarse fine
        · exact ih value member
  rw [PairedRefinement.pairedUniformPaths_refinement_eq _ _ _ _ bank]
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounds
  rw [List.Map.length_map] at estimate
  exact estimate.trans_eq (by
    simp only [Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
    ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement
open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source other :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
    UniformReciprocalCover.ParentCovers parents}
  {index otherIndex : Nat} {box otherBox : Rational.Box}

set_option genInjectivity false in
/-- The requested baseline caches the entire paired path and its area.
Later refinements consume the retained polynomial bounds and count. -/
structure PairedRefinementRequest (bank : Disk.ParentJoins.SideBank regular covers)
    (sample : Cap.Primitives.Sample cap source index box)
    (otherSample : Cap.Primitives.Sample cap other otherIndex otherBox)
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The first cap sample's retained polynomial energy bound. -/ left :
    Cap.EnergyBounds sample
  /-- The second cap sample's retained polynomial energy bound. -/ right :
    Cap.EnergyBounds otherSample
  /-- The cached number of original parents. -/ count : Nat
  /-- The cached count is exactly the original parent-list length. -/ count_eq : count = parents.length
  /-- The cached complete parent-count and paired-slope error scale. -/ scale :
    InverseRootPolynomial.Coordinate
  /-- The error scale is the squared parent count times the common paired cap-slope factor. -/ scale_eq : scale = (count
    : InverseRootPolynomial.Coordinate)^2 * (4 * (max
    (Cap.RefinementArea.arcSlope left)
    (Cap.RefinementArea.arcSlope right))^2)
  /-- The cached baseline dyadic depth. -/ depth : Nat
  /-- The baseline depth is the first paid quarter-radius stage above the supplied minimum. -/ depth_eq : depth =
    Search.firstQuarterBelow scale minimum target
  /-- The baseline depth respects the requested minimum. -/ minimum_le : minimum ≤ depth
  /-- The cached geometric error at the baseline depth. -/ error : InverseRootPolynomial.Coordinate
  /-- The cached error is the quarter-radius value of the retained scale and depth. -/ error_eq : error =
    Basic.quarterRadius scale depth
  /-- The cached baseline error is strictly below the requested tolerance. -/ accurate : error < target
  /-- The cached paired increment path for each original parent. -/ blocks : List (List
    PrimitivePoint)
  /-- The cached blocks are exactly the paired uniform paths at the chosen baseline depth. -/ blocks_eq : blocks =
    bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value depth
  /-- The cached complete paired increment path. -/ path : List PrimitivePoint
  /-- The cached complete path is the flattening of its retained parent blocks. -/ path_eq : path = blocks.flatten
  /-- The retained total and area summary of this exact cached complete path. -/ summary :
    Path.PairedIncrementArea.Summary path

constructive_injectivity PairedRefinementRequest

namespace PairedRefinementRequest
variable {bank : Disk.ParentJoins.SideBank regular covers}
  {sample : Cap.Primitives.Sample cap source index box}
  {otherSample : Cap.Primitives.Sample cap other otherIndex otherBox}
  {target : InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Choose a paid baseline depth and cache the complete paired parent paths and their area summary.

The original parent count and both retained polynomial energy bounds determine the scale; the requested positive
tolerance pays every later refinement. -/
@[expose] def build (bank : Disk.ParentJoins.SideBank regular covers) (left :
  Cap.EnergyBounds sample)
    (right : Cap.EnergyBounds otherSample) (target :
      InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (minimum : Nat) :
      PairedRefinementRequest bank sample otherSample
      target minimum := open Data.Rat in by
  let count := parents.length
  let scale := (count : InverseRootPolynomial.Coordinate)^2 * (4 * (max
    (Cap.RefinementArea.arcSlope left)
    (Cap.RefinementArea.arcSlope right))^2)
  have nonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct
    (Arithmetic.sq_nonneg_direct _)
    (Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.sq_nonneg_direct _))
  let depth := Search.firstQuarterBelow scale minimum target
  let blocks := bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value depth
  let path := blocks.flatten
  exact ⟨left, right, count, rfl, scale, rfl, depth, rfl,
    Search.firstQuarterBelow_ge scale minimum target,
    Basic.quarterRadius scale depth, rfl, Search.firstQuarterBelow_accurate scale
      nonnegative minimum target positive,
    blocks, rfl, path, rfl, Path.PairedIncrementArea.Summary.build path⟩

/-- Every later finite subdivision is compared with the cached baseline.
This certifies a finite refinement error, not disappearance of the exterior. -/
theorem later_error (request : PairedRefinementRequest bank
  sample otherSample target minimum)
    (later : Nat) (after : request.depth ≤ later) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
        (bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value later).flatten -
      request.summary.areaValue) < target := by
  rw [request.summary.area_eq, request.path_eq, request.blocks_eq]
  have estimate := PairedRefinement.pairedUniformPaths_refinement_bound
    request.left request.right request.depth (later - request.depth) bank
  rw [Nat.Subtraction.add_sub_of_le after] at estimate
  have scale : (parents.length : InverseRootPolynomial.Coordinate)^2 * (4 * (max
    (Cap.RefinementArea.arcSlope request.left)
    (Cap.RefinementArea.arcSlope request.right))^2) =
      request.scale := by rw [request.scale_eq, request.count_eq]
  rw [scale] at estimate
  exact estimate.trans_lt (request.error_eq ▸ request.accurate)

end PairedRefinementRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement
