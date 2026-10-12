module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

public section

/-! The restored cap chords form the full joining polygon on each retained
closed exterior component. Closure cancels the total, not the polygon area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Rat
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

/-- The complete paired increment total along a retained endpoint path equals its last primitive point minus its first.
-/
private theorem path_total {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    {edges : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges first last) :
    PairedIncrementArea.total (edges.map (fun edge => (values edge.finish).sub (values edge.start))) =
      (values last).sub (values first) := by
  induction path with
  | nil =>
      apply congrArg₂ PrimitivePoint.mk <;>
        simp only [List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, PrimitivePoint.sub, sub_self, -eq_self,
          -iff_self] <;> rfl
  | @cons edge tail last path ih =>
      change ((values edge.finish).sub (values edge.start)).add
        (PairedIncrementArea.total (tail.map (fun item => (values item.finish).sub (values item.start)))) = _
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp [PrimitivePoint.add, PrimitivePoint.sub] <;> ring1

/-- The trace area of an actual retained endpoint path is exactly its original polygon edge area. -/
private theorem path_trace {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    {edges : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges first last) :
    PairedIncrementArea.traceArea (values first) (edges.map (fun edge => (values edge.finish).sub (values edge.start)))
      =
      Stokes.edgeListArea values edges := by
  induction path with
  | nil => rfl
  | @cons edge tail last path ih =>
      have endpoint : (values edge.start).add ((values edge.finish).sub (values edge.start)) =
          values edge.finish := by
        cases values edge.finish
        apply congrArg₂ PrimitivePoint.mk <;> dsimp [PrimitivePoint.add, PrimitivePoint.sub] <;> ring1
      change Stokes.edgeArea (values edge.start) _ + PairedIncrementArea.traceArea _ _ = _
      rw [endpoint, ih]
      rfl

/-- A retained closed polygon's edge area equals the area of its actual paired increment list. -/
private theorem closed_polygon {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    {edges : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    Stokes.edgeListArea values edges =
      PairedIncrementArea.area (edges.map (fun edge => (values edge.finish).sub (values edge.start))) := by
  have result := (path_trace values
    closed).symm.trans
    (PairedIncrementArea.traceArea_eq (values anchor) _)
  rw [path_total values closed] at result
  simpa only [PrimitivePoint.sub, sub_self, Stokes.edgeArea, mul_zero, zero_mul, add_zero, -eq_self, -iff_self] using
    result

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {stage : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}

namespace CapAttachment

/-- The paired original cap primitive values at a retained physical vertex, conjugating only the first coordinate. -/
@[expose] def conjugateCapValues (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (vertex : Fin lifted.vertices.count) : PrimitivePoint :=
  ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval (lifted.vertices.coordinate vertex)⁻¹,
    otherSample.primitive.value.eval (lifted.vertices.coordinate vertex)⁻¹⟩

/-- The complete joining-polygon area summed over the actual retained closed exterior words.

Every increment uses the original cap primitive samples and the physical vertices of its retained edge occurrence. -/
@[expose] def conjugateJoiningArea (attached : AllSurfacePreparation.CapAttachment prepared)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) : Gaussian :=
  let values :=
    conjugateCapValues (lifted
    := lifted) sample otherSample
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (attached.words.map (fun word =>
    PairedIncrementArea.area (word.map (fun edge => (values edge.finish).sub (values edge.start)))))

/-- The polygon area of a flattened retained word family equals the sum of its individual word areas. -/
private theorem flattened_area {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    (words : List (List (Stokes.OrientedEdge count))) :
    Stokes.edgeListArea values words.flatten = Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.map
      (Stokes.edgeListArea values)) := by
  induction words with
  | nil => rfl
  | cons word tail ih =>
      rw [List.flatten_cons, Stokes.edgeListArea_append, ih]
      rfl

/-- The actual cap endpoint restoration is a sum of whole component polygons. -/
theorem conjugate_chords_eq_joining (attached : AllSurfacePreparation.CapAttachment prepared)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
        occurrence sample otherSample)) =
        conjugateJoiningArea
          attached sample otherSample := by
  let values :=
    conjugateCapValues (lifted
    := lifted) sample otherSample
  have chords : Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
      PairedArcRequest.conjugateChordValue occurrence sample otherSample)) =
      Stokes.edgeListArea values (prepared.occurrences.map (fun occurrence => occurrence.placement.indexed)) := by
    induction prepared.occurrences with
    | nil => rfl
    | cons occurrence tail ih =>
        change PairedArcRequest.conjugateChordValue occurrence sample otherSample + _ = _ + _
        apply congrArg₂ (· + ·) _ ih
        unfold PairedArcRequest.conjugateChordValue
        dsimp only [values,
          conjugateCapValues]
        rw [occurrence.placement.start_eq, occurrence.placement.finish_eq]
  rw [chords, prepared.indexed_eq, ← attached.words_flatten,
    flattened_area]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Map.map_congr_left
  intro word member
  obtain ⟨anchor, closed⟩ := attached.words_closed word member
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.closed_polygon values closed

end CapAttachment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
