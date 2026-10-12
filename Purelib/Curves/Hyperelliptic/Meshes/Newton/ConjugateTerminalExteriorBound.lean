module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct
import Purelib.Riemann.Periods.NewtonOriginalExteriorPeriods
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! The retained reciprocal request also bounds the conjugate terminal exterior product
on the actual ordered factor, for either displayed polynomial degree shape. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateTerminalExteriorBound

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Fraction.Rational} {i j : Fin genus} {floor : Nat}

/-- Bound the conjugate terminal exterior product on the retained ordered resplit factor.

The canonical exterior list and shared late cut readings use the same boundary refinement, differential magnitude banks
and endpoint request. Odd degree gives a zero product; even degree uses the two original exterior-period bounds. -/
theorem conjugate_terminal_exterior_bound (newSheet : Fin 2)
    (boundary : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation i j target radius floor)
    (canonical : boundary.exterior.prepared.components.map (fun component => component.program.indexed) =
      boundary.lifted.exteriorBoundaries)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank boundary.domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank boundary.domains
      (Periods.PeriodMatrix.standardDifferential j))
    {requested : Fraction.Rational} {referenceFloor : Nat} (result :
      RootContinuation.NewtonRequestedExteriorDepth.ExteriorSourceRequest boundary requested referenceFloor)
    {endpointTarget : Fraction.Rational}
    (endpoints :
      ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary
        result.depth).exterior.prepared (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
        boundary result.depth).paid.cut.fixed i j endpointTarget)
    {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      boundary.domains stage}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary result.depth).paid.cut cache)
    (later : result.index ≤ stage) (endpointLater : endpoints.endpoints.index ≤ stage)
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage) :
    let refined := RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary result.depth
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      refined.fine.family.single.grid.shrunk.included refined.lifted.edges refined.lifted.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
        refined.lifted.mesh readings.left.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values)
          coefficient))) ≤
      4 * max (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound
        (paired := paired) boundary.fine.family.single.grid.shrunk.included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
          paired) boundary.fine.family.single.grid.shrunk.included second) *
          (2 * (requested + endpointTarget)) := by
  intro refined
  cases curve.degreeShape with
  | odd degree =>
      have zero := Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.product_zero_of_odd (paired := paired)
        refined.fine.family.single.grid.shrunk.included degree newSheet
        (fun edge => Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          refined.lifted.mesh readings.left.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values)
      have magnitude : 0 ≤ max
          (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired
            := paired) boundary.fine.family.single.grid.shrunk.included first)
          (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired
            := paired) boundary.fine.family.single.grid.shrunk.included second) :=
            (PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
            (paired := paired)
        boundary.fine.family.single.grid.shrunk.included first).trans (Fraction.Order.Basic.le_max_left _ _)
      have positive : 0 < requested := (Gaussian.Norm.Basic.normSq_nonneg _).trans_lt result.bounded
      exact ((congrArg Data.Gaussian.Norm.Basic.normSq zero).trans Gaussian.Norm.Basic.normSq_zero).trans_le
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitude)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg positive.le endpoints.positive.le)))
  | even degree =>
      have totals := Periods.NewtonOriginalExteriorPeriods.original_exterior_periods_bound boundary canonical degree
        newSheet result endpoints readings later endpointLater
      exact Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct.conjugate_product_bound (paired :=
        paired) refined.fine.family.single.grid.shrunk.included
        first second newSheet readings.left readings.right firstLater secondLater totals.1 totals.2

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateTerminalExteriorBound
