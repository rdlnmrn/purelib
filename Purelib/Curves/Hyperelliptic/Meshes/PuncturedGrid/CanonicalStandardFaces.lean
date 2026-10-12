module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-! Canonical face lookup is certified at the constructors which select it,
without expanding the enclosing period-row preparation. -/

section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.LinearAlgebra.Alternating
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : LiftedMesh vertices edges base.faces} {first last : Gaussian.Basic.Canonical}
  {walk : Geometry.Grid.Walks.Walk base.bank.grid first last} {owner : Owner (curve.polynomial.eval first)}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces

/-- The retained original face geometry is exactly the canonical lookup on its actual sheet. -/
@[expose] def Canonical (faces :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner) : Prop :=
  faces.geometry = Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces mesh walk faces.sheet

/-- The original sheet-specific face constructor selects the canonical lookup. -/
theorem ofSheet_canonical (mesh : LiftedMesh vertices edges base.faces)
    (walk : Geometry.Grid.Walks.Walk base.bank.grid first last) (firstMember :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (sheet : Fin 2) (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent
      (ownerName owner) (ownerName ((frames.frameAt first firstMember).owners sheet)))) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.Canonical
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSheet mesh walk
      firstMember sheet aligned) := rfl

/-- The original owner-based face constructor selects the canonical lookup on its retained sheet. -/
theorem build_canonical (mesh : LiftedMesh vertices edges base.faces)
    (walk : Geometry.Grid.Walks.Walk base.bank.grid first last) (firstMember :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (owner : Owner (curve.polynomial.eval first)) :
      Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.Canonical
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.build mesh walk
      firstMember owner) :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSheet_canonical mesh walk
    firstMember _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.LinearAlgebra.Alternating
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Data.List

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {index : Fin genus}

/-- The source constructor selects canonical lookups for both actual tours. -/
theorem
  TourFaces.StandardTours.Pair.ofSource_a_canonical
  (lifted : LiftedPuncturedGrid base) (index : Fin genus)
    (source : Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair curve)
    (sourceEq : source = Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData curve branches index) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource lifted index source
      sourceEq).aFaces.Canonical :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.build_canonical _ _ _ _

/-- The original source-pair constructor selects canonical face geometry for its actual B tour. -/
theorem
  TourFaces.StandardTours.Pair.ofSource_b_canonical
  (lifted : LiftedPuncturedGrid base) (index : Fin genus)
    (source : Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair curve)
    (sourceEq : source = Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData curve branches index) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource lifted index source
      sourceEq).bFaces.Canonical :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSheet_canonical _ _ _ _ _

variable {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

/-- The actual A tour of the retained original period row has canonical face geometry. -/
theorem
  TourIntersection.IntersectionRow.ofPeriod_a_canonical
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
      branches).rows index) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal index
      period periodEq).pair.aFaces.Canonical :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource_a_canonical _ _ _ _

/-- The actual B tour of the retained original period row has canonical face geometry. -/
theorem
  TourIntersection.IntersectionRow.ofPeriod_b_canonical
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
      branches).rows index) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal index
      period periodEq).pair.bFaces.Canonical :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource_b_canonical _ _ _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
