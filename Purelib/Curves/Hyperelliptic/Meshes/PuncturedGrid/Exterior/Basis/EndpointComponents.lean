module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CorrectionReindex
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Assemble original cached endpoint chords over every retained surface component. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents

open Purelib

open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cachedEndpoint)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {stage : Nat} {cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
    stage}

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- Read each component's original cached endpoint chords in its traversal order. -/
@[expose] def componentCachedEndpoints (component : ExteriorProgram.SurfaceComponent regular domains differential)
    (cache : RegularMeshes.Numerics domains stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
      : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (component.prepared.occurrences.map fun occurrence =>
    SideOccurrence.oriented occurrence.sideOccurrence
    (SharedPerimeter.cachedEndpoint cache coefficients occurrence.sideOccurrence.position
      occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))

/-- Sum disconnected component endpoint corrections onto the same exterior face/sheet cache used by the global Newton
boundary. -/
theorem componentCachedEndpoints_sum (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (neighbors : PuncturedFaces.NeighborBank base.faces) (cache : RegularMeshes.Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component =>
      componentCachedEndpoints component
      cache coefficients)) =
      SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
        (fun side position => FiniteSum.Fin.sumFin (fun sheet => SharedPerimeter.cachedEndpoint cache coefficients
          position sheet side)) .exterior := by
  have indexed := prepared.oriented_sum_eq_component neighbors (SharedPerimeter.cachedEndpoint cache coefficients)
  have mapped := Data.Gaussian.Norm.Sum.Indexed.sumFin_map prepared.occurrences (fun occurrence =>
    SideOccurrence.oriented occurrence.sideOccurrence
    (SharedPerimeter.cachedEndpoint cache coefficients occurrence.sideOccurrence.position
      occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))
  have all := (Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_flatMap prepared.components
    (fun component => component.prepared.occurrences) (fun occurrence => SideOccurrence.oriented
      occurrence.sideOccurrence
      (SharedPerimeter.cachedEndpoint cache coefficients occurrence.sideOccurrence.position
        occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side))).symm
  rw [← prepared.occurrences_eq] at all
  exact all.trans (mapped.symm.trans indexed)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointComponents
