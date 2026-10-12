module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CorrectionReindex

public section

/-! Physical endpoint chords read the original period corner cache exactly.
Reindex that same cache over the actual exterior component. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage coarseDepth : Nat}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {previous : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {selected :
    BasisSourceCuts basis.preparations previous}
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet coarseDepth)
    fixed surfaceTarget}
  {request : PhysicalMeshRequest basis initial} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

section PhysicalMeshRequest

/-- Read the conjugated endpoint chord from the original corner cache of a specified face, sheet and side.

Horizontal and vertical sides keep the same directed corner ordering as their retained physical samples. -/
@[expose] def cachedConjugateEndpoint (cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (first second : Fin
  genus)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide) : Gaussian
      :=
  let value := fun corner => Path.ConjugateIncrementComparison.conjugateFirst
    ⟨(cache.atDomain position sheet first).corners.values corner,
      (cache.atDomain position sheet second).corners.values corner⟩
  match side with
  | .bottom => Topology.Polygon.Stokes.edgeArea (value 0) (value 1)
  | .right => Topology.Polygon.Stokes.edgeArea (value 1) (value 2)
  | .top => Topology.Polygon.Stokes.edgeArea (value 3) (value 2)
  | .left => Topology.Polygon.Stokes.edgeArea (value 0) (value 3)

/-- Subtracting the initial primitive value from the terminal one preserves its wedge with that initial value. -/
private theorem endpoint_chord (first last : Topology.Polygon.Stokes.PrimitivePoint) :
    Topology.Polygon.Stokes.edgeArea first (last.sub first) = Topology.Polygon.Stokes.edgeArea first last := by
  simp only [Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self]
  ring1

namespace OccurrenceReadings

/-- The physical occurrence endpoint chord equals the chord of its original cached face corners.

The proof uses the retained side trace and its exact endpoint readbacks, preserving both basis-row owners. -/
theorem endpoint_eq_cached {first second : Fin genus}
    {i : Fin (basis.preparations.get first).occurrences.length}
    (entry : request.OccurrenceReadings cache first second i) :
    entry.original.endpoint =
      let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
      cachedConjugateEndpoint cache
        first second occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side := by
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  let firstCached := cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet first
  let secondCached := cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet second
  have endpoints (side : Meshes.GridLiftedDualSteps.GridSide)
      (sample : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst

          (SharedPhysicalPerimeterReadings.values
          (occurrence := occurrence) entry.traces
          (cache.get first) (cache.get second) side vertex))) :
      sample.endpoint =
        cachedConjugateEndpoint
        cache first second
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet side := by
    rw [sample.endpoint_eq,
      endpoint_chord]
    cases side with
    | bottom =>
        have firstStart := firstCached.perimeter_bottom_first_eq entry.traces
        have secondStart := secondCached.perimeter_bottom_first_eq entry.traces
        have firstEnd := firstCached.perimeter_bottom_last_eq entry.traces
        have secondEnd := secondCached.perimeter_bottom_last_eq entry.traces
        rw [entry.traces.bottom.leftReadings_value] at firstStart secondStart firstEnd secondEnd
        exact congrArg₂ Topology.Polygon.Stokes.edgeArea
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstStart secondStart))
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstEnd secondEnd))
    | top =>
        have firstStart := firstCached.perimeter_top_first_eq entry.traces
        have secondStart := secondCached.perimeter_top_first_eq entry.traces
        have firstEnd := firstCached.perimeter_top_last_eq entry.traces
        have secondEnd := secondCached.perimeter_top_last_eq entry.traces
        rw [entry.traces.top.leftReadings_value] at firstStart secondStart firstEnd secondEnd
        exact congrArg₂ Topology.Polygon.Stokes.edgeArea
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstStart secondStart))
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstEnd secondEnd))
    | left =>
        have firstStart := firstCached.perimeter_left_first_eq entry.traces
        have secondStart := secondCached.perimeter_left_first_eq entry.traces
        have firstEnd := firstCached.perimeter_left_last_eq entry.traces
        have secondEnd := secondCached.perimeter_left_last_eq entry.traces
        rw [entry.traces.left.leftReadings_value] at firstStart secondStart firstEnd secondEnd
        exact congrArg₂ Topology.Polygon.Stokes.edgeArea
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstStart secondStart))
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstEnd secondEnd))
    | right =>
        have firstStart := firstCached.perimeter_right_first_eq entry.traces
        have secondStart := secondCached.perimeter_right_first_eq entry.traces
        have firstEnd := firstCached.perimeter_right_last_eq entry.traces
        have secondEnd := secondCached.perimeter_right_last_eq entry.traces
        rw [entry.traces.right.leftReadings_value] at firstStart secondStart firstEnd secondEnd
        exact congrArg₂ Topology.Polygon.Stokes.edgeArea
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstStart secondStart))
          (congrArg Path.ConjugateIncrementComparison.conjugateFirst (congrArg₂
            Topology.Polygon.Stokes.PrimitivePoint.mk firstEnd secondEnd))
  exact endpoints occurrence.sideOccurrence.side entry.original

end OccurrenceReadings

/-- The source-forward sign equals the original physical side occurrence orientation. -/
private theorem signed_endpoint (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (value : Gaussian.Basic.Canonical) :
    (if occurrence.sourceForward then value else -value) =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence value := by
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only
      [SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.sourceForward,
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented,
      side, backward,
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.top = .left),
      if_pos (by decide : Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.left = .left),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.bottom = .left)),
      if_neg (by decide : ¬ (Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .top ∨
        Riemann.Meshes.GridLiftedDualSteps.GridSide.right = .left)),
      if_pos (Eq.refl true), if_neg (by decide : ¬ false = true), -eq_self, -iff_self] <;>
      first | rfl | ring1

namespace Readings

/-- Every exterior occurrence uses the fixed period corner cache, with the
original face, sheet and boundary orientation preserved. -/
theorem physicalEndpoints_eq_component (entries : request.Readings cache)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces) (first second : Fin genus) :
    entries.physicalEndpoints first second =
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
        (fun side position => FiniteSum.Fin.sumFin (fun sheet =>
          cachedConjugateEndpoint
          cache first second position sheet side))
        .exterior := by
  apply Eq.trans _ ((basis.preparations.get first).oriented_sum_eq_component neighbors
    (fun position sheet side =>
      cachedConjugateEndpoint cache
      first second position sheet side))
  unfold physicalEndpoints
  apply FiniteSum.Fin.sumFin_congr
  intro i
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  have readback := (((entries.get first).get second).get i).endpoint_eq_cached
  exact (signed_endpoint occurrence
    _).trans
    (congrArg
      (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence) readback)

/-- The coefficient-weighted physical endpoint energy equals the exterior component selected from the original corner
cache. -/
theorem physicalEndpointEnergy_eq_cached (entries : request.Readings cache)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    entries.physicalEndpointEnergy coefficients =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
          Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
            (fun side position => FiniteSum.Fin.sumFin (fun sheet =>
              cachedConjugateEndpoint
              cache first second position sheet side))
            .exterior)) := by
  unfold
    physicalEndpointEnergy
  apply FiniteSum.Fin.sumFin_congr
  intro first
  apply FiniteSum.Fin.sumFin_congr
  intro second
  exact congrArg (fun value => Data.Gaussian.Basic.conj (coefficients first) * coefficients second * value)
    (entries.physicalEndpoints_eq_component neighbors first second)

end Readings

end PhysicalMeshRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
