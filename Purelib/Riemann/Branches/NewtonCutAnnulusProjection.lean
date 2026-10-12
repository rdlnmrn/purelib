module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceSelection
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Subtraction

public section

/-!
# Exact projected coverage of the selected cut annulus

The sewn selection follows the actual source-face mask. Its cut triangles
project, with full multiplicity, to the same retained two-sheeted annulus
used by the Newton boundary identity. No equality of cut primitives is used.
-/

namespace Purelib.Riemann.Branches.NewtonCutAnnulusProjection

open Purelib.Data.Nat

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_map sumValues_congr)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (triangles)
open Purelib.Riemann.Meshes.GridLiftedFaceSelection (Selection select)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus sourceFace)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_succ)

open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Topology.Surface in
/-- The retained selected sewn triangles project to the masked sum over the original source faces.

Exact trace projections, source coverage and the original finite permutation identify each selected triangle without
replacing its source owner. -/
private theorem selected_projected_sum {vertexCount faceCount : Nat}
    {faces : Fin faceCount → OrientedTriangle vertexCount} {forest : Topology.Surface.Sewing.SewingForest faces}
    (polygon : Sewing.SewingConnected.SewingForest.SinglePolygon forest) {localValues : Fin faceCount →
      Sewing.PrimitiveSewing.PrimitiveValues 3}
    (sample : Sewing.SewnPrimitiveSamples.CachedSample polygon.patch localValues) {keep : Fin faceCount → Bool}
    (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample keep) (value :
      OrientedTriangle vertexCount → Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun triangle => value (Sewing.VertexSewing.OrientedTriangle.map
      polygon.patch.cut.vertexLabels triangle)) selected.triangles =
      sumFin (fun source => if keep source then value (faces source) else 0) := by
  rw [selected.triangles_eq, Geometry.Grid.CellBoundary.sumValues_map]
  have projected := Geometry.Grid.CellBoundary.sumValues_congr _ (fun trace => value (faces trace.source))
    selected.traces
    (fun trace member => congrArg value (selected.trace_projection trace member))
  rw [projected, selected.traces_eq, Geometry.Grid.CellBoundary.sumValues_filter]
  have readback := (Geometry.Grid.CellBoundary.sumValues_map (fun source => if keep source then value (faces source)
    else 0)
    Sewing.SewnPrimitiveFaces.FaceTrace.source sample.faces.entries).symm
  rw [readback, sample.faces.sources_eq]
  exact (Geometry.Grid.CellBoundary.sumValues_perm _ polygon.coverage).trans (Geometry.Grid.CellBoundary.sumValues_ofFn
    _)

/-- Repeat each face predicate over its four consecutive lifted triangle positions.

Every retained face contributes the same Boolean value at its four positions.
The tail mask starts after those four positions. -/
private def faceMask {Face : Type} (keep : Face → Bool) : List Face → Nat → Bool
  | [], _ => false
  | face :: faces, index => if index < 4 then keep face else faceMask keep faces (index - 4)

/-- Advancing four triangle positions drops exactly one head face from the mask.

The natural index subtraction recovers the unchanged tail position, preserving
the predicate and the retained face list. -/
private theorem faceMask_four {Face : Type} (keep : Face → Bool) (face : Face) (faces : List Face) (index : Nat) :
    faceMask keep (face :: faces) (index + 4) = faceMask keep faces index := by
  rw [faceMask, if_neg (by omega), Subtraction.add_sub_cancel_right]

/-- At a valid triangle position, the repeated mask reads its face index divided by four.

The supplied bound identifies an occurrence in the retained face list.
Head and tail cases retain that same divided index and lookup certificate. -/
private theorem faceMask_get {Face : Type} (keep : Face → Bool) : ∀ (faces : List Face) (index : Nat)
    (inside : index / 4 < faces.length), faceMask keep faces index = keep faces[index / 4]
  | [], _, inside => (Nat.not_lt_zero _ inside).elim
  | face :: faces, index, inside => by
      by_cases first : index < 4
      · rw [faceMask, if_pos first]
        simp only [show index / 4 = 0 by omega, List.getElem_cons_zero, -eq_self]
        rfl
      · have next : (index - 4) / 4 < faces.length := by
          change index / 4 < faces.length + 1 at inside
          have := Nat.le_of_not_gt first
          omega
        rw [faceMask, if_neg first, faceMask_get keep faces (index - 4) next]
        simp only [show index / 4 = (index - 4) / 4 + 1 by omega, List.getElem_cons_succ, -eq_self]
        rfl

open Purelib.Data.Gaussian in
/-- Equality of original ordered lists transports their exact position-dependent finite sums. -/
private theorem indexed_sum_congr {Item : Type} {first last : List Item} (equal : first = last)
    (value : Nat → Item → Basic.Canonical) :
    sumFin (fun index : Fin first.length => value index.val first[index.val]) =
      sumFin (fun index : Fin last.length => value index.val last[index.val]) := by
  cases equal
  rfl

namespace BranchCellBank.LiftedFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The retained selected lifted triangles have the same sum as the original triangle list weighted by its repeated face
mask.

Each original face contributes its exact four sheet triangles, with zeros at all rejected positions. -/
private theorem select_weighted (keep : RegularFace bank → Bool) (value : OrientedTriangle vertices.count →
  Basic.Canonical) :
    ∀ {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces),
    Geometry.Grid.CellBoundary.sumValues value (select keep lifts).selected.triangles =
      sumFin (fun index : Fin lifts.triangles.length => if faceMask keep faces index.val then value
        lifts.triangles[index.val] else 0)
  | _, .nil => rfl
  | face :: faces, .cons zero one tail => by
      have rest := select_weighted keep value tail
      have shifted : (sumFin fun index : Fin tail.triangles.length =>
          if faceMask keep (face :: faces) (index.val + 4) then value tail.triangles[index.val] else 0) =
          sumFin (fun index : Fin tail.triangles.length => if faceMask keep faces index.val then value
            tail.triangles[index.val] else 0) :=
        FiniteSum.Fin.sumFin_congr (fun index => by rw [faceMask_four])
      by_cases kept : keep face = true
      · have selected := congrArg
          (fun result : Selection vertices edges keep (face :: faces) => Geometry.Grid.CellBoundary.sumValues value
            result.selected.triangles)
          (show select keep (.cons zero one tail) = _ from dif_pos kept)
        rw [selected]
        change _ = sumFin (fun index : Fin (tail.triangles.length + 4) =>
          if faceMask keep (face :: faces) index.val then value (triangles (.cons zero one tail))[index.val] else 0)
        rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
        change _ = (if keep face then value zero.quad.firstTriangle else 0) +
          ((if keep face then value zero.quad.secondTriangle else 0) +
          ((if keep face then value one.quad.firstTriangle else 0) +
          ((if keep face then value one.quad.secondTriangle else 0) + _)))
        rw [if_pos kept, if_pos kept, if_pos kept, if_pos kept]
        exact congrArg (fun remaining => value zero.quad.firstTriangle + (value zero.quad.secondTriangle +
          (value one.quad.firstTriangle + (value one.quad.secondTriangle + remaining)))) (rest.trans shifted.symm)
      · have selected := congrArg
          (fun result : Selection vertices edges keep (face :: faces) => Geometry.Grid.CellBoundary.sumValues value
            result.selected.triangles)
          (show select keep (.cons zero one tail) = _ from dif_neg kept)
        rw [selected]
        change _ = sumFin (fun index : Fin (tail.triangles.length + 4) =>
          if faceMask keep (face :: faces) index.val then value (triangles (.cons zero one tail))[index.val] else 0)
        rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
        change _ = (if keep face then value zero.quad.firstTriangle else 0) +
          ((if keep face then value zero.quad.secondTriangle else 0) +
          ((if keep face then value one.quad.firstTriangle else 0) +
          ((if keep face then value one.quad.secondTriangle else 0) + _)))
        rw [if_neg kept, if_neg kept, if_neg kept, if_neg kept,
          Basic.zero_add, Basic.zero_add, Basic.zero_add, Basic.zero_add]
        exact rest.trans shifted.symm

end BranchCellBank.LiftedFaces

namespace BranchCellBank.NewtonGrid.AllHoleExcision.SewnAnnulus

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → PrimitiveValues 3}
  {sample : CachedSample lifted.cutPolygon.patch localValues}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
open Purelib.Topology.Surface in
/-- The original sewn selection and retained lifted-face selection have equal projected triangle sums.

The exact source-face mask and mesh face equation identify their bounded original indices and preserve the retained
triangle-list cache. -/
theorem selected_lifted_sum (keep : RegularFace grid.shrunk.prepared.toBranchCellBank → Bool)
    (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection sample (fun source => keep
      (sourceFace lifted source)))
    (value : OrientedTriangle lifted.vertices.count → Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun triangle => value (Sewing.VertexSewing.OrientedTriangle.map
      lifted.cutPolygon.patch.cut.vertexLabels triangle)) selected.triangles =
      Geometry.Grid.CellBoundary.sumValues value (GridLiftedFaceSelection.select keep
        lifted.mesh.lifts).selected.triangles := by
  rw [selected_projected_sum lifted.cutPolygon sample selected value]
  erw [LiftedFaces.select_weighted]
  have equal : (sumFin fun index : Fin lifted.mesh.triangles.length =>
      if keep (sourceFace lifted index) then value (lifted.mesh.triangulation.faces index) else 0) =
      sumFin (fun index : Fin lifted.mesh.triangles.length =>
        if faceMask keep grid.faces.regulars index.val then value lifted.mesh.triangles[index.val] else 0) := by
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [lifted.mesh.faces_eq, faceMask_get]
    rfl
  rw [equal]
  exact indexed_sum_congr lifted.mesh.triangles_eq
    (fun index triangle => if faceMask keep grid.faces.regulars index then value triangle else 0)

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Topology.Surface in
/-- A retained sewn annulus projects to its annular region's exact triangle sum.

The source selection equation identifies the same lifted triangle occurrences.
The projected sum preserves their order, multiplicity and retained mesh cache. -/
theorem projected_sum (annulus : SewnAnnulus sample) (value : OrientedTriangle lifted.vertices.count → Basic.Canonical)
  :
    Geometry.Grid.CellBoundary.sumValues (fun triangle => value (Sewing.VertexSewing.OrientedTriangle.map
      lifted.cutPolygon.patch.cut.vertexLabels triangle)) annulus.selected.triangles =
      Geometry.Grid.CellBoundary.sumValues value annulus.source.region.triangles := by
  rw [annulus.source.selection_eq]
  exact selected_lifted_sum annulus.source.keep annulus.selected value

end BranchCellBank.NewtonGrid.AllHoleExcision.SewnAnnulus
end Purelib.Riemann.Branches.NewtonCutAnnulusProjection
