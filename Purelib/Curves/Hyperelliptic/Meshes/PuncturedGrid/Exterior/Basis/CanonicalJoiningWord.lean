module
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalIncrements
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Topology.Polygon.Stokes

public section

/-! Read the complete retained component polygon on the canonical exterior word. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib

open Purelib.Data.Rat
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter (cachedIncrement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cornerValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter (cachedIncrement)

namespace SurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt)
variable {program : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
  differential}
  (prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program)
  (whole :
    AllSurfacePreparation
    regular domains differential)
  (member : ∀ outer, Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer ∈ whole.occurrences)
  {stage : Nat} (cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
    stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (readings : (row : Fin genus) → Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
    (cache.get row) lifted.mesh)

include member

/-- Corner increments reproduce the literal component edge word, in order. -/
theorem cached_increment_word :
    (List.ofFn fun outer =>
      let occurrence := ParentIndices.occurrenceAt prepared.occurrences outer
      let total := SharedPerimeter.cachedIncrement (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else PrimitivePoint.zero.sub total) =
      program.indexed.map (fun edge => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row =>
        coefficients row *
        CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge)) := by
  let value := fun edge => ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
    CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge)
  have entries := OfFn.Basic.ofFn_congr (fun outer =>
    whole.occurrence_cached_canonical (ParentIndices.occurrenceAt prepared.occurrences outer) (member outer) cache
      coefficients readings)
  apply entries.trans
  change (List.ofFn fun outer => value (ParentIndices.occurrenceAt prepared.occurrences outer).placement.indexed) = _
  rw [← prepared.occurrences_eq, Data.List.Map.map_map]
  have enumerated := congrArg (List.map (fun occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential
    =>
    value occurrence.placement.indexed)) (OfFn.Basic.ofFn_getElem prepared.occurrences)
  rw [OfFn.Basic.map_ofFn] at enumerated
  exact enumerated

/-- Equality of full increment words transports the polygon area without losing joins. -/
theorem cached_joining_area :
    PairedIncrementArea.area (List.ofFn fun outer =>
      let occurrence := ParentIndices.occurrenceAt prepared.occurrences outer
      let total := SharedPerimeter.cachedIncrement (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else PrimitivePoint.zero.sub total) =
      PairedIncrementArea.area (program.indexed.map (fun edge =>
        ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge))) :=
  congrArg PairedIncrementArea.area (prepared.cached_increment_word whole member cache coefficients readings)

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
