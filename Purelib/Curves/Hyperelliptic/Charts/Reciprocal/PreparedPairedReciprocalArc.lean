module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalArc
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedUniformPaths
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.UniformPrimitiveMesh

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

/-! Both components identify the same complete increment list on the
original prepared segment. Its paired area retains the endpoint chord. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc

/-- Two lists of paired primitive points agree when both component lists agree. -/
private theorem paired_lists_eq : (first last : List Topology.Polygon.Stokes.PrimitivePoint) →
    first.map Topology.Polygon.Stokes.PrimitivePoint.left = last.map Topology.Polygon.Stokes.PrimitivePoint.left →
    first.map Topology.Polygon.Stokes.PrimitivePoint.right = last.map Topology.Polygon.Stokes.PrimitivePoint.right →
      first = last
  | [], [], _, _ => rfl
  | [], _ :: _, equal, _ => by cases equal
  | _ :: _, [], equal, _ => by cases equal
  | a :: first, b :: last, left, right => by
      have l := List.cons.inj left
      have r := List.cons.inj right
      have head : a = b := by
        cases a; cases b
        exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk l.1 r.1
      exact congrArg₂ List.cons head
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.paired_lists_eq first last l.2 r.2)

/-- Mapping a flattened block list agrees with flattening the individually mapped blocks. -/
private theorem flatten_map {A B : Type} (f : A → B) (blocks : List (List A)) :
    blocks.flatten.map f = (blocks.map (List.map f)).flatten := by
  induction blocks with
  | nil => rfl
  | cons head tail ih => rw [List.flatten_cons, Data.List.Map.map_append, List.map_cons, List.flatten_cons, ih]

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical} {segment :
    Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner} {sheet : Fin 2}

/-- Equality of both component lists proves equality of the complete paired
list, including every intermediate vertex and the retained parent order. -/
theorem pairedUniformPaths_segment (cache : Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache
  piece.path differential sheet)
    {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers cache.parents} (bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers)
    (left right : Normalization.InverseRootPolynomial.Polynomial) (fine : Nat) :
    (bank.pairedUniformPaths left right fine).flatten =
      Path.Dyadic.DyadicPairedPrimitivePaths.increments
        (fun parameter => (⟨left.eval ((segment.pointAt parameter)⁻¹), right.eval ((segment.pointAt parameter)⁻¹)⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))
        (piece.mesh.depth + fine) 0 1 := by
  apply Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.paired_lists_eq
  · rw [Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.flatten_map, bank.pairedUniformPaths_left,
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths_segment cache bank,
      Path.Dyadic.DyadicPairedPrimitivePaths.increments_left]
  · rw [Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.flatten_map, bank.pairedUniformPaths_right,
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths_segment cache bank,
      Path.Dyadic.DyadicPairedPrimitivePaths.increments_right]

/-- The complete retained paired parent area equals the reciprocal segment arc area minus its endpoint chord.

The original prepared segment mesh and the supplied refinement depth determine the arc subdivision. -/
theorem pairedUniformPaths_area_eq_arc (cache : Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache
  piece.path differential sheet)
    {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers cache.parents} (bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers)
    (left right : Normalization.InverseRootPolynomial.Polynomial) (fine : Nat) :
    Path.PairedIncrementArea.area (bank.pairedUniformPaths left right fine).flatten =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea (fun point => ⟨left.eval point,
        right.eval point⟩)
        (piece.mesh.depth + fine) start finish -
      Topology.Polygon.Stokes.edgeArea ⟨left.eval start⁻¹, right.eval start⁻¹⟩ ⟨left.eval finish⁻¹, right.eval finish⁻¹⟩
        := by
  rw [Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.pairedUniformPaths_segment cache bank,
    Path.Dyadic.DyadicPairedPrimitivePaths.increments_area,
    Geometry.ClearPath.ClearSegment.pointAt_zero, Geometry.ClearPath.ClearSegment.pointAt_one]
  rfl

namespace PairedRefinementRequest
variable {other : Hyperelliptic.Differentials.Basic.Differential genus} {index otherIndex : Nat} {box otherBox :
  Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox}
  {cache : Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache piece.path differential sheet} {covers :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers cache.parents}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {target : Fraction.Rational}
    {minimum : Nat}

/-- The requested cache is now read as the actual inverse segment arc.
The endpoint term is still explicit, and no new polynomial is sampled. -/
theorem later_arc_error (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedRefinement.PairedRefinementRequest
  bank sample otherSample target minimum)
    (later : Nat) (after : request.depth ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea (fun point =>
        ⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩)
        (piece.mesh.depth + later) start finish -
      Topology.Polygon.Stokes.edgeArea ⟨sample.primitive.value.eval start⁻¹, otherSample.primitive.value.eval start⁻¹⟩
        ⟨sample.primitive.value.eval finish⁻¹, otherSample.primitive.value.eval finish⁻¹⟩ - request.summary.areaValue) <
          target := by
  rw [← Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.pairedUniformPaths_area_eq_arc cache bank]
  exact request.later_error later after

end PairedRefinementRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc
