module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Riemann
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes.UniformPrimitiveMesh

/-!
# The retained parent path is the actual source inverse arc

Uniform refinement of the cached, ordered source parents is exactly dyadic
refinement of their original segment at the sum of the two depths. This
identifies every intermediate primitive increment, not just the endpoints.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (midpoint_affine)

/-- Pointwise equal parameter values have identical complete dyadic increment lists on every retained interval. -/
theorem dyadicIncrements_congr {left right : Fraction.Rational → Data.Gaussian.Basic.Canonical}
    (equal : ∀ parameter, left parameter = right parameter)
    (depth : Nat) (first last : Fraction.Rational) :
    DyadicPrimitivePaths.dyadicIncrements left depth first last = DyadicPrimitivePaths.dyadicIncrements right depth
      first last := by
  induction depth generalizing first last with
  | zero =>
      simp only [DyadicPrimitivePaths.dyadicIncrements, equal, -eq_self, -iff_self]
      rfl
  | succ depth ih => rw [DyadicPrimitivePaths.dyadicIncrements, DyadicPrimitivePaths.dyadicIncrements, ih, ih]

/-- Affine reparameterization preserves the exact dyadic increment list after transporting both interval endpoints. -/
theorem dyadicIncrements_affine (values : Fraction.Rational → Data.Gaussian.Basic.Canonical) (origin slope :
  Fraction.Rational)
    (depth : Nat) (first last : Fraction.Rational) :
    DyadicPrimitivePaths.dyadicIncrements (fun parameter => values (origin + slope * parameter)) depth first last =
      DyadicPrimitivePaths.dyadicIncrements values depth (origin + slope * first) (origin + slope * last) := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
    rw [DyadicPrimitivePaths.dyadicIncrements, DyadicPrimitivePaths.dyadicIncrements, ih, ih,
      DyadicBoundaryRibbon.midpoint_affine]

end Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece : CoveredSegment segment owner} {sheet : Fin 2}

/-- Every actual retained parent point is the original segment point at its affine parent parameter. -/
theorem segment_parent_point (cache : ParentCache piece.path differential sheet)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents) (parameter : Fraction.Rational) :
    parent.edge.point parameter = segment.pointAt (parent.parameterEdge.left.parameter +
      (parent.parameterEdge.right.parameter - parent.parameterEdge.left.parameter) * parameter) := by
  have endpoints := Paths.PreparedSegmentBoundaryGeometry.segment_parent_endpoints cache member
  have interpolate : parent.edge.point parameter = parent.edge.point 0 +
      Scale.scale parameter (parent.edge.point 1 - parent.edge.point 0) := by
    change parent.edge.localSegment.pointAt parameter = parent.edge.localSegment.pointAt 0 +
      Scale.scale parameter (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0)
    rw [ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
    rfl
  rw [interpolate, endpoints.1, endpoints.2]
  change start + Scale.scale parent.parameterEdge.left.parameter (finish - start) +
    Scale.scale parameter ((start + Scale.scale parent.parameterEdge.right.parameter (finish - start)) -
      (start + Scale.scale parent.parameterEdge.left.parameter (finish - start))) = _
  change _ = start + Scale.scale _ (finish - start)
  apply Data.Gaussian.Basic.ext <;> simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re,
    Scale.scale_im, -eq_self, -iff_self] <;> ring1

/-- The retained parent inverse-coordinate increments equal the original segment increments on its exact retained
parameter interval. -/
theorem segment_parent_increments (cache : ParentCache piece.path differential sheet)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents)
    (values : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) (fine : Nat) :
    DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((parent.edge.point parameter)⁻¹)) fine 0 1 =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((segment.pointAt parameter)⁻¹)) fine
        parent.parameterEdge.left.parameter parent.parameterEdge.right.parameter := by
  have pointwise (parameter : Fraction.Rational) : values ((parent.edge.point parameter)⁻¹) =
      values ((segment.pointAt (parent.parameterEdge.left.parameter +
        (parent.parameterEdge.right.parameter - parent.parameterEdge.left.parameter) * parameter))⁻¹) := by
    rw [cache.segment_parent_point member]
  rw [Integration.Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_congr pointwise,
    Integration.Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_affine
    (fun parameter => values ((segment.pointAt parameter)⁻¹))]
  simp only [Fraction.Field.mul_zero_direct, _root_.add_zero,
    Fraction.Field.mul_one_direct, -eq_self, -iff_self]
  have finishEq : parent.parameterEdge.left.parameter +
      (parent.parameterEdge.right.parameter - parent.parameterEdge.left.parameter) =
      parent.parameterEdge.right.parameter := by ring1
  exact congrArg (fun finish => DyadicPrimitivePaths.dyadicIncrements
    (fun parameter => values ((segment.pointAt parameter)⁻¹)) fine
    parent.parameterEdge.left.parameter finish) finishEq

/-- Exact path equality reads both the cached parent order and the original mesh specification. No parent list is
replaced merely from equal counts. -/
theorem segment_uniform_increments (cache : ParentCache piece.path differential sheet)
    (values : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) (fine : Nat) :
    (cache.parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((parent.edge.point
      parameter)⁻¹)) fine 0 1)).flatten =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((segment.pointAt parameter)⁻¹)) (piece.mesh.depth
        + fine) 0 1 := by
  have paths : cache.parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => values
    ((parent.edge.point parameter)⁻¹)) fine 0 1) =
      cache.parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((segment.pointAt
        parameter)⁻¹)) fine
        parent.parameterEdge.left.parameter parent.parameterEdge.right.parameter) := by
    apply Map.map_congr_left
    intro parent member
    exact cache.segment_parent_increments member values fine
  have parameters : cache.parents.map CenteredEdge.parameterEdge = piece.mesh.edges := by
    rw [cache.parents_eq, Paths.PreparedSegmentParentBanks.CoveredSegment.path_parents piece differential sheet,
      Paths.PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges, piece.mesh_eq]
  rw [paths]
  calc
    _ = ((cache.parents.map CenteredEdge.parameterEdge).map (fun edge =>
        DyadicPrimitivePaths.dyadicIncrements (fun parameter => values ((segment.pointAt parameter)⁻¹)) fine
          edge.left.parameter edge.right.parameter)).flatten := by
      rw [Data.List.Map.map_map]
      rfl
    _ = _ := by
      rw [parameters, Mesh.edges, DyadicPrimitivePaths.dyadicEdges_flatten_increments]
      rfl

end Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- The retained uniform primitive paths are exactly the original parent list of dyadic inverse-polynomial increments.
-/
theorem uniformPrimitivePaths_eq {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {covers : UniformReciprocalCover.ParentCovers parents} (bank : ParentJoins.SideBank regular covers) (value :
      InverseRootPolynomial.Polynomial) (fine : Nat) :
    SideBank.uniformPrimitivePaths value fine bank =
      parents.map (fun parent => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value.eval ((parent.edge.point
        parameter)⁻¹)) fine 0 1) := by
  induction bank with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons _) ih

variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical} {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
  ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- Flattening the retained parent paths gives the original segment inverse-arc increments at the sum of coarse and fine
depths. -/
theorem uniformPrimitivePaths_segment (cache : Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache
  piece.path differential sheet)
    {covers : UniformReciprocalCover.ParentCovers cache.parents} (bank : ParentJoins.SideBank regular covers) (value :
      InverseRootPolynomial.Polynomial) (fine : Nat) :
    (SideBank.uniformPrimitivePaths value fine bank).flatten =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => value.eval ((segment.pointAt parameter)⁻¹))
        (piece.mesh.depth + fine) 0 1 := by
  rw [uniformPrimitivePaths_eq bank]
  exact cache.segment_uniform_increments value.eval fine

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest (RegularRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path (UniformAreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest (Evaluation)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}
  {cache : ParentCache piece.path differential
    sheet} {prepared : Preparation regular
    cache.parents}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target totalTarget areaTarget : Purelib.Data.Rat.Fraction.Rational} {minimum floor fine readingIndex common : Nat}
  {capRequest : RegularRequest prepared
    totalTarget areaTarget floor}
  {request : UniformAreaRequest prepared sample
    target minimum}
  {original : RegularRequest.Evaluation
    capRequest sample fine readingIndex}

/-- The actual uniform area evaluation path is the original segment inverse-arc increment list at its retained combined
depth. -/
theorem path_eq_segment (evaluated : UniformAreaRequest.Evaluation request original common) :
    evaluated.path = DyadicPrimitivePaths.dyadicIncrements
      (fun parameter => sample.primitive.value.eval ((segment.pointAt parameter)⁻¹)) (piece.mesh.depth + common) 0 1 :=
        by
  rw [evaluated.path_eq, evaluated.paths_eq,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths_segment cache
    prepared.bank]

/-- The open segment's origin term is retained. It cancels only when a later consumer proves the corresponding boundary
closure. -/
theorem area_eq_arc (evaluated : UniformAreaRequest.Evaluation request original common) :
    evaluated.summary.area = ReciprocalRadialGeometry.arcArea sample.primitive.value.eval
      (piece.mesh.depth + common) start finish -
        BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) := by
  rw [evaluated.summary.area_eq, evaluated.path_eq_segment]
  have trace := DyadicPrimitivePaths.traceArea_dyadicIncrements
    (fun parameter => sample.primitive.value.eval ((segment.pointAt parameter)⁻¹)) (piece.mesh.depth + common) 0 1
  rw [IncrementArea.traceArea_eq, DyadicPrimitivePaths.dyadicIncrements_sum,
    ClearSegment.pointAt_zero, ClearSegment.pointAt_one] at trace
  have offset : BoundaryRibbon.area (sample.primitive.value.eval start⁻¹)
      (sample.primitive.value.eval finish⁻¹ - sample.primitive.value.eval start⁻¹) =
      BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) := by
    apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re,
      Basic.sub_im, Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1
  rw [offset] at trace
  change _ + _ = ReciprocalRadialGeometry.arcArea sample.primitive.value.eval (piece.mesh.depth + common) start finish
    at trace
  calc
    _ = (_ + _) - _ := by ring1
    _ = _ := congrArg (fun value : InverseRootPolynomial.Gaussian => value - _) trace

/-- This estimate compares the actual original cap-area cache to the original edge's inverse arc, with its endpoint term
still explicit. -/
theorem original_area_close_arc (evaluated : UniformAreaRequest.Evaluation request original common) :
    Data.Gaussian.Norm.Basic.normSq (ReciprocalRadialGeometry.arcArea sample.primitive.value.eval
      (piece.mesh.depth + common) start finish -
        BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) -
          original.cap.area) < target := by
  rw [← evaluated.area_eq_arc]
  exact evaluated.area_error

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest.Evaluation

namespace Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Integration.Path.BoundaryRibbon (area)

/-- Interchanging two rational endpoints preserves their midpoint. -/
private theorem midpoint_reverse (first last : Fraction.Rational) :
    Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint last first =
      Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint first last := by
  have doubled (left right : Fraction.Rational) : PreparedBoxPartitions.midpoint left right * 2 = left + right := by
    calc
      _ = left * 2 + ((right - left) / 2) * 2 := by unfold PreparedBoxPartitions.midpoint; ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
  apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  rw [doubled, doubled]
  ring1

/-- Reversing the two interval endpoints negates the complete dyadic area at every depth. -/
theorem dyadicArea_reverse (values : Fraction.Rational → Data.Gaussian.Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    DyadicBoundaryRibbon.dyadicArea values depth last first = -DyadicBoundaryRibbon.dyadicArea values depth first last
      := by
  induction depth generalizing first last with
  | zero =>
    rw [DyadicBoundaryRibbon.dyadicArea_zero, DyadicBoundaryRibbon.dyadicArea_zero]; unfold BoundaryRibbon.area; ring1
  | succ depth ih =>
      rw [DyadicBoundaryRibbon.dyadicArea_succ, DyadicBoundaryRibbon.dyadicArea_succ,
        Integration.Path.Dyadic.DyadicBoundaryRibbon.midpoint_reverse first last, ih last, ih _ first]
      ring1

end Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
/-- The cap fan's opposite orientation reverses the whole inverse arc, including all finite subdivision vertices. -/
theorem arcArea_reverse (values : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) (depth : Nat) (first
  last : Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea values depth last first =
      -Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea values depth first last := by
  have sourceReverse (parameter : Fraction.Rational) : ReciprocalRadialGeometry.source last first parameter =
    ReciprocalRadialGeometry.source first last (1 + (-1) * parameter) := by
    apply Data.Gaussian.Basic.ext <;> simp only [ReciprocalRadialGeometry.source, Basic.add_re, Basic.add_im,
      Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im, -eq_self, -iff_self] <;> ring1
  unfold ReciprocalRadialGeometry.arcArea
  rw [DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg (fun point : Data.Gaussian.Basic.Canonical =>
    values point⁻¹) (sourceReverse parameter)),
    DyadicBoundaryRibbon.dyadicArea_affine (fun parameter => values ((ReciprocalRadialGeometry.source first last
      parameter)⁻¹))]
  rw [show (1 : Fraction.Rational) + (-1) * 0 = 1 by decide, show (1 : Fraction.Rational) + (-1) * 1 = 0 by decide]
  exact Integration.Path.Dyadic.DyadicBoundaryRibbon.dyadicArea_reverse _ _ _ _

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
