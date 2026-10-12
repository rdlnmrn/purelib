module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily
import Purelib.Riemann.Integration.PreparedConjugateParentCapReadback
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Conjugate exterior-family comparison reuses the retained parent paths,
common stage and common depth, and keeps every endpoint chord. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace PairedArcRequest
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target : Fraction.Rational} {minimum stage depth : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared other target
  minimum}

/-- The endpoint chord of the original paired polynomial values with the first coordinate conjugated. -/
@[expose] def conjugateChordValue (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) : Gaussian :=
  Topology.Polygon.Stokes.edgeArea
    (Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
      otherSample.primitive.value.eval occurrence.start⁻¹⟩)
    (Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
      otherSample.primitive.value.eval occurrence.finish⁻¹⟩)

/-- The literal original inverse-arc area of the paired polynomial values with first-coordinate conjugation. -/
@[expose] def conjugateArcValue (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) :
      Gaussian :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
    (fun point => Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
      otherSample.primitive.value.eval point⟩)
    depth occurrence.start occurrence.finish

/-- The full conjugate paired area of the original retained source increment path. -/
@[expose] def Entry.conjugateSourceArea (entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample depth) :
  Gaussian :=
  Path.PairedIncrementArea.area ((entry.compared.pairs.map Prod.fst).flatten.map
    Path.ConjugateIncrementComparison.conjugateFirst)

/-- The synchronized occurrence keeps its actual source path and endpoint
chord when compared with the inverse arc. -/
theorem Entry.conjugate_arc_accurate (entry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample depth)
    (member : entry.plan ∈ request.plans) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.Entry.conjugateSourceArea entry)
      + Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
      entry.plan.occurrence sample otherSample -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue
        entry.plan.occurrence sample otherSample depth) < request.allowance := by
  have indexLe := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.le_maximum (fun plan =>
    plan.parents.index) member).trans (request.index_eq ▸ later)
  have bound := Integration.PreparedConjugateParentCapReadback.conjugate_arc_error entry.plan.occurrence entry.compared
    indexLe
  unfold Integration.PreparedConjugateParentCapReadback.ConjugateArcError at bound
  rw [entry.depth_eq] at bound
  change Data.Gaussian.Norm.Basic.normSq
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.Entry.conjugateSourceArea entry) -
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue
      entry.plan.occurrence sample otherSample depth -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
        entry.plan.occurrence sample otherSample)) < request.allowance at bound
  have rearrange (a b c : Gaussian.Basic.Canonical) : a + b - c = a - (c - b) := by ring1
  rw [rearrange]
  exact bound

/-- The complete exterior occurrence family has one paid conjugate-arc
comparison, at the existing shared model stage and spatial depth. -/
theorem Evaluation.conjugate_arc_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.Entry.conjugateSourceArea entry)
      +
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
        entry.plan.occurrence sample otherSample)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue occurrence
        sample otherSample depth))) < target := by
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (evaluated.retained.map (fun entry =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.Entry.conjugateSourceArea entry)
      +
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
        entry.plan.occurrence sample otherSample -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue
        entry.plan.occurrence sample otherSample depth)) request.allowance (by
        intro value member
        obtain ⟨entry, retained, rfl⟩ := Data.List.Map.mem_map.mp member
        exact
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.Entry.conjugate_arc_accurate
          entry)
          (evaluated.plans_eq ▸ Data.List.Map.mem_map_of_mem retained) later).le)
  have occurrences := (congrArg (List.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence) evaluated.plans_eq).trans
    request.occurrences_eq
  have count : evaluated.retained.length = prepared.occurrences.length := by
    have h := congrArg List.length occurrences
    simpa only [Data.List.Map.length_map] using h
  have arcs := congrArg (fun occurrences => Data.Gaussian.Norm.Sum.Basic.gaussianSum (occurrences.map
    (fun occurrence => Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue
      occurrence sample otherSample depth))) occurrences
  rw [Data.List.Map.map_map, Data.List.Map.map_map] at arcs
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue
      entry.plan.occurrence sample otherSample depth)) = _ at arcs
  rw [Data.List.Map.length_map, count, Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub, arcs] at bound
  exact bound.trans_lt request.paid

/-- The conjugate occurrence arc sum equals the literal forward inverse-arc sum on the exact original attachment words.
-/
theorem conjugate_attachment_arcs (attached :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue occurrence
      sample otherSample depth)) =
      Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => Path.ConjugateIncrementComparison.conjugateFirst (Periods.ReciprocalCapBilinearBounds.pairedValue
          sample otherSample point)) depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words := by
  rw [Geometry.Grid.CellBoundary.sumValues_flatten, attached.words_flatten, ← prepared.indexed_eq,
    Data.List.Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro occurrence _
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateArcValue,
    Function.comp_def]
  rw [occurrence.placement.start_eq, occurrence.placement.finish_eq]
  rfl

end PairedArcRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
