module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Refinement-independent bounds on retained segment occurrences

The fixed reference uses the original covered segment, owner and parent
cache. Its bound applies to actual shared corner and triangle readings at
every later index, in the placement's orientation. This bounds increments;
it makes no normalization assumption on absolute primitive values.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences (Reference)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces} {ambient :
    Purelib.Geometry.Rational.Box}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : ClearSegment
    curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner}
  {placement : SegmentFace mesh segment} {differential :
    Differential genus} {parentSheet : Fin 2}
  {domains : FaceDomainBank frames faces.regulars}

/-- The actual retained segment-corner increment satisfies its original fixed primitive-reference target at every
sufficient shared stage. -/
theorem reference_accurate (compared : LiftedMesh.SegmentComparison placement piece differential parentSheet)
    (aligned : compared.domains = domains.atRoute placement.location)
    {target : InverseRootPolynomial.Coordinate} (reference : PrimitiveReferences.Reference compared.entered target)
    {index : Nat} (later : reference.budget.grid.index ≤ index) (shared : PrimitiveData.FacePrimitiveBank differential
      index domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location - reference.value) < target := by
  have coordinates := placement.location.corner_coordinates
  have bounded := PointReferences.point_accurate reference later
    (compared.sharedData shared aligned)
    (compared.sharedData shared aligned).corners placement.location.corners.start placement.location.corners.finish
    ((congrArg Prod.fst coordinates).trans placement.start_eq) ((congrArg Prod.snd coordinates).trans
      placement.finish_eq)
  rw [compared.sharedData_corners] at bounded
  exact bounded

/-- The actual retained segment-corner increment satisfies the original reference's fixed magnitude ceiling
independently of later refinement. -/
theorem reference_bounded (compared : LiftedMesh.SegmentComparison placement piece differential parentSheet)
    (aligned : compared.domains = domains.atRoute placement.location)
    {target : InverseRootPolynomial.Coordinate} (reference : PrimitiveReferences.Reference compared.entered target)
    {index : Nat} (later : reference.budget.grid.index ≤ index) (shared : PrimitiveData.FacePrimitiveBank differential
      index domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location) ≤ reference.bound := by
  have coordinates := placement.location.corner_coordinates
  have bounded := PointReferences.point_bounded reference later
    (compared.sharedData shared aligned)
    (compared.sharedData shared aligned).corners placement.location.corners.start placement.location.corners.finish
    ((congrArg Prod.fst coordinates).trans placement.start_eq) ((congrArg Prod.snd coordinates).trans
      placement.finish_eq)
  rw [compared.sharedData_corners] at bounded
  exact bounded

/-- The actual retained triangle source-edge reading satisfies the same original segment-reference magnitude ceiling in
its given orientation. -/
theorem triangle_reference_bounded (compared : LiftedMesh.SegmentComparison placement piece differential parentSheet)
    (aligned : compared.domains = domains.atRoute placement.location)
    {target : InverseRootPolynomial.Coordinate} (reference : PrimitiveReferences.Reference compared.entered target)
    {index : Nat} (later : reference.budget.grid.index ≤ index) {shared : PrimitiveData.FacePrimitiveBank differential
      index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values) ≤ reference.bound
      := by
  rw [readings.route_increment]
  exact reference_bounded compared aligned
    reference later shared

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
