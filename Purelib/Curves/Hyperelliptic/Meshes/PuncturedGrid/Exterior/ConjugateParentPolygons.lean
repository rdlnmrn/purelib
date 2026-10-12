module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring
import Purelib.Data.List.Flatten

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Geometry.Path.Gaussian

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Regroup canonical parent endpoint polygons into the actual exterior
occurrences, retaining their internal areas and the attachment joining polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily (PairedArcRequest)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea edgeListArea)
open Purelib.Integration.Path.PairedIncrementArea (total area traceArea)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceComponent SurfaceOccurrence)
open Purelib.Integration.Path.PairedAreaBlocks (area_flatten)
/-- The paired primitive difference between the two physical endpoints of one retained original parent. -/
private def parentIncrement {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint) (parent : PreparedSubdivisionModelCore.CenteredEdge
      curve differential) : PrimitivePoint :=
  (values (parent.edge.point 1)).sub (values (parent.edge.point 0))

/-- The paired increment total of an actual direct parent chain equals its original outer endpoint difference. -/
private theorem parent_total {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint) {parents : List
      (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start :=
      first) (finish := last)) :
    PairedIncrementArea.total (parents.map
      (parentIncrement values)) = (values
      last.coordinate).sub (values first.coordinate) := by
  induction chain with
  | nil =>
      apply congrArg₂ PrimitivePoint.mk <;>
        simp only [List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, sub_self, -eq_self, -iff_self] <;> rfl
  | cons parent chain ih =>
      change (parentIncrement values
        parent).add (PairedIncrementArea.total _) = _
      rw [ih]
      simp only [parentIncrement,
        parent.edge.point_zero, parent.edge.point_one, -eq_self, -iff_self]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only [PrimitivePoint.add, PrimitivePoint.sub, -eq_self, -iff_self] <;>
        ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {stage : Nat} {box otherBox : Purelib.Geometry.Rational.Box}

/-- The actual parent polygon area decomposes into all original occurrence polygons and the retained exterior joining
polygon. -/
private theorem component_regroup {program : PeriodPrograms.ExteriorProgram lifted differential}
    (component : ExteriorProgram.SurfacePreparation regular domains program) (values : Data.Gaussian.Basic.Canonical →
      Stokes.PrimitivePoint) :
    PairedIncrementArea.area (program.cache.parents.map
      (parentIncrement values)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (component.occurrences.map (fun occurrence =>
        PairedIncrementArea.area (occurrence.compared.entered.cache.parents.map
          (parentIncrement values)))) +
      PairedIncrementArea.area (program.indexed.map (fun edge =>
        (values (lifted.vertices.coordinate edge.finish)).sub (values (lifted.vertices.coordinate edge.start)))) := by
  let blocks := component.occurrences.map (fun occurrence =>
    occurrence.compared.entered.cache.parents.map
      (parentIncrement values))
  have flat : blocks.flatten = program.cache.parents.map
    (parentIncrement values) := by
    rw [← component.parents_eq, Flatten.map_flatten, Map.map_map]
    rfl
  have totals : blocks.map PairedIncrementArea.total = program.indexed.map (fun edge =>
      (values (lifted.vertices.coordinate edge.finish)).sub (values (lifted.vertices.coordinate edge.start))) := by
    rw [← component.occurrences_eq]
    simp only [blocks, Map.map_map]
    apply Map.map_congr_left
    intro occurrence _
    obtain ⟨chain⟩ := occurrence.compared.entered.cache.chain
    have equal := parent_total values
      chain.toDirectPathChain
    exact equal.trans (congrArg₂ PrimitivePoint.sub
      (congrArg values occurrence.placement.finish_eq.symm)
      (congrArg values occurrence.placement.start_eq.symm))
  have grouped := PairedAreaBlocks.area_flatten blocks
  rw [flat, totals] at grouped
  simpa only [blocks, Map.map_map, Function.comp_def] using grouped

/-- Summing retained blockwise Gaussian values equals summing their exact flattened original list. -/
private theorem sum_flatMap {A : Type u} {B : Type v} (entries : List A) (blocks : A → List B) (value : B →
  Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((blocks entry).map value))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((entries.flatMap blocks).map value) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [Flatten.flatMap_cons, Map.map_append, IncrementArea.sum_append]
      exact congrArg (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((blocks head).map value) + ·) ih

/-- The Gaussian sum of pairwise added list readings equals the sum of the two original list totals. -/
private theorem sum_map_add {A : Type u} (entries : List A) (first last : A → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => first entry + last entry)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map first) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (entries.map last) := by
  induction entries with
  | nil => exact (add_zero _).symm
  | cons head tail ih =>
      change (_ + _) + _ = (_ + _) + (_ + _)
      rw [ih]
      ring1

namespace AllSurfacePreparation.CapAttachment

/-- Coarsening the parent polygons produces the joining polygon plus every internal occurrence polygon. Closure does not
discard those internal areas. -/
theorem conjugate_parent_polygons (attached : AllSurfacePreparation.CapAttachment prepared)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) :
    let values := fun point => ConjugateIncrementComparison.conjugateFirst (⟨sample.primitive.value.eval point⁻¹,
      otherSample.primitive.value.eval point⁻¹⟩ : Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      PairedIncrementArea.area (component.program.cache.parents.map (fun parent =>
        (values (parent.edge.point 1)).sub (values (parent.edge.point 0)))))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
        PairedIncrementArea.area (occurrence.compared.entered.cache.parents.map (fun parent =>
          (values (parent.edge.point 1)).sub (values (parent.edge.point 0)))))) +
      CapAttachment.conjugateJoiningArea attached sample otherSample := by
  intro values
  have components := Map.map_congr_left (fun component (_ : component ∈ prepared.components) =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons.component_regroup component.prepared
      values)
  have result := congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum components
  have splitSum := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons.sum_map_add (A :=
    ExteriorProgram.SurfaceComponent regular domains differential) prepared.components
    (fun component : ExteriorProgram.SurfaceComponent regular domains differential =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (component.prepared.occurrences.map (fun occurrence =>
      PairedIncrementArea.area (occurrence.compared.entered.cache.parents.map
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons.parentIncrement values)))))
    (fun component : ExteriorProgram.SurfaceComponent regular domains differential => PairedIncrementArea.area
      (component.program.indexed.map (fun edge =>
      (values (lifted.vertices.coordinate edge.finish)).sub (values (lifted.vertices.coordinate edge.start)))))
  have split := result.trans splitSum
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons.sum_flatMap, ← prepared.occurrences_eq]
    at split
  have wordOrder : attached.words = prepared.components.map (fun component => component.program.indexed) :=
    attached.words_eq.trans (Map.map_congr_left (fun component _ => component.prepared.occurrences_eq))
  have words := congrArg (fun words => Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.map (fun word =>
    PairedIncrementArea.area (word.map (fun edge =>
    (values (lifted.vertices.coordinate edge.finish)).sub (values (lifted.vertices.coordinate edge.start)))))))
      wordOrder
  rw [Map.map_map] at words
  exact split.trans (congrArg (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence
    =>
    PairedIncrementArea.area (occurrence.compared.entered.cache.parents.map
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons.parentIncrement values)))) + ·)
      words.symm)

end AllSurfacePreparation.CapAttachment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateParentPolygons

