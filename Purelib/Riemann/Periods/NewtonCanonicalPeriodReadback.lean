module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Riemann.Periods.NewtonCanonicalPeriodComparison
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Periods.NewtonPairedPeriodFragments
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.GridLiftedFaces
public import Purelib.Riemann.Periods.NewtonCanonicalPeriodData
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Mathlib.Order.Basic

public section

/-! The canonical A/B comparisons select one common incoming sheet on the
retained Newton mesh. Their indexed words are the actual resplit words. -/
namespace Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  anchor)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodData (ACanonicalPreparation BCanonicalPreparation aCanonicalAssigned
  bCanonicalAssigned aCanonicalFaces bCanonicalFaces)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {differential cycle : Fin genus}
  {target : Rational} {minimum : Nat}

section
open Purelib.Curves.Hyperelliptic
/-- Select the original anchor owner's sheet in the retained refined boundary frame.

The original lifted anchor and included grid vertex index the actual frame selection. -/
@[expose] def canonicalPeriodSheet
    (boundary : PeriodGeometry base.bank.toBranchCellBank) : Fin 2 :=
  ((boundary.lifted.frames.frameAt (lifted.vertices.coordinate
    (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))
    (boundary.grid.shrunk.included.vertex (lifted.vertices.coordinate_onGrid
      (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))).select
    (lifted.vertices.owner lifted.frames
      (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))).index

/-- The original canonical A-face assignment retains the selected anchor sheet. -/
theorem aCanonicalFaces_sheet (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :
    (aCanonicalFaces (cycle := cycle) prepared boundary).sheet = canonicalPeriodSheet (lifted := lifted) (sheet :=
      sheet) boundary := rfl

/-- The canonical A assignment reads back the original resplit closed walk's indexed edges. -/
theorem aCanonicalAssigned_indexed (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :
    (aCanonicalAssigned (cycle := cycle) prepared boundary).indexed =
      boundary.lifted.edges.indexedEdges boundary.lifted.vertices
        (boundary.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary) :=
  Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces_indexed _ _ _

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
open Purelib.Topology.Surface in
/-- The original canonical A-word meets the retained A-period sample target.

The actual numerical cache and triangle readings must meet the stored numerical floor; the original A-program stage must
meet the retained fragment floor. -/
theorem ACanonicalPreparation.word_accurate {prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    (data : ACanonicalPreparation prepared boundary differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains numericalIndex)
    (triangles : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get differential)
      boundary.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat) (after : data.request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values)
      (boundary.lifted.edges.indexedEdges boundary.lifted.vertices
        (boundary.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary)) -
      ((prepared.periodData.aProgram differential cycle).integral.model stage).integralSample) < target := by
  have accurate := NewtonCanonicalPeriodComparison.ACanonicalPreparation.accurate data positive numericalIndex cache
    triangles later stage after
  exact (congrArg (fun word => Data.Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
    (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values) word -
    ((prepared.periodData.aProgram differential cycle).integral.model stage).integralSample))
      (aCanonicalAssigned_indexed (cycle := cycle) prepared boundary)).symm.trans_lt accurate

section
open Purelib.Curves.Hyperelliptic
/-- The original canonical B-face assignment retains the selected anchor sheet. -/
theorem bCanonicalFaces_sheet (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :
    (bCanonicalFaces (cycle := cycle) prepared boundary).sheet = canonicalPeriodSheet (lifted := lifted) (sheet :=
      sheet) boundary := rfl

/-- The canonical B assignment reads back the original resplit closed walk's indexed edges. -/
theorem bCanonicalAssigned_indexed (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :
    (bCanonicalAssigned (cycle := cycle) prepared boundary).indexed =
      boundary.lifted.edges.indexedEdges boundary.lifted.vertices
        (boundary.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary) :=
  Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces_indexed _ _ _

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
open Purelib.Topology.Surface in
/-- The original canonical B-word meets the retained B-period sample target.

The actual numerical cache and triangle readings must meet the stored numerical floor; the original B-program stage must
meet the retained fragment floor. -/
theorem BCanonicalPreparation.word_accurate {prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    (data : BCanonicalPreparation prepared boundary differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains numericalIndex)
    (triangles : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get differential)
      boundary.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat) (after : data.request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values)
      (boundary.lifted.edges.indexedEdges boundary.lifted.vertices
        (boundary.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary)) -
      ((prepared.periodData.bProgram differential cycle).integral.model stage).integralSample) < target := by
  have accurate := NewtonCanonicalPeriodComparison.BCanonicalPreparation.accurate data positive numericalIndex cache
    triangles later stage after
  exact (congrArg (fun word => Data.Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
    (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh triangles.values) word -
    ((prepared.periodData.bProgram differential cycle).integral.model stage).integralSample))
      (bCanonicalAssigned_indexed (cycle := cycle) prepared boundary)).symm.trans_lt accurate

end Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
