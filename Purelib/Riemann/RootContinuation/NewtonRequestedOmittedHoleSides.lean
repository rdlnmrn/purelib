module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundaryInterfaces
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison

@[expose] public section

/-! Omitted hole-adjacent sides use the original annular preparation's radius,
endpoint allowance, sheet owners and perimeter traces. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedOmittedHoleSides
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests (InterfaceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- Allocate a retained interface where the original discarded face meets a physical hole.

The exact hole and side witnesses determine the retained annular entry and boundary certificate without replacing the
original preparation or trace owner. -/
def omittedHoleRequest (prepared : BoundaryPreparation preparation first second target radius floor)
    (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    (hole : Fin prepared.fine.family.single.grid.faces.holes.length) (side : GridSide)
    (matching : side.Matches
      (prepared.fine.family.single.grid.faces.regulars[position.val]'position.isLt).cell.box
      (prepared.fine.family.single.grid.faces.holes[hole.val]'hole.isLt).cell.box)
    (discarded : fineMask prepared.excision position = false) :
    InterfaceRequest prepared.excision prepared.traces first second position side :=
  let found := Meshes.Newton.AllHoles.Excision.AllHoleExcision.entryForHole prepared.excision hole
  NewtonSelectedInterfaceRequests.InterfaceRequest.ofBoundary prepared.excision prepared.traces first second position
    side
    found.val found.property.1 (Meshes.Newton.AllHoles.Excision.AllHoleExcision.omittedHole_boundary prepared.excision
      position hole side matching discarded)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The retained omitted-hole interface remainder is bounded by four times the original fine component allowance.

The original preparation and allocated interface both precede the supplied readings, retaining the same physical hole,
matched side and sheet. -/
theorem omittedHole_bound (prepared : BoundaryPreparation preparation first second target radius floor)
    (position : Fin prepared.fine.family.single.grid.faces.regulars.length)
    (hole : Fin prepared.fine.family.single.grid.faces.holes.length) (side : GridSide)
    (matching : side.Matches
      (prepared.fine.family.single.grid.faces.regulars[position.val]'position.isLt).cell.box
      (prepared.fine.family.single.grid.faces.holes[hole.val]'hole.isLt).cell.box)
    (discarded : fineMask prepared.excision position = false)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage)
    (sideLater : (omittedHoleRequest prepared position hole side matching discarded).index ≤ stage)
    (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder readings.normalized
      position
      sheet side) ≤ 4 * prepared.fine.fine.component :=
  NewtonRequestedBoundaryInterfaces.interface_bound prepared
    (omittedHoleRequest prepared position hole side matching discarded)
    readings later sideLater sheet

end Purelib.Riemann.RootContinuation.NewtonRequestedOmittedHoleSides
