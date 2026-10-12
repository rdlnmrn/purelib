module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The existing annular preparation pays the actual selected boundary-side
requests with its pre-grid Newton radius and endpoint allowance. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundaryInterfaces
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius :
    Rational} {floor : Nat}

/-- Allocate the original selected-to-discarded face interface from the retained boundary preparation.

The matched side and both selection certificates identify the exact face pair and annular entry; the request retains the
original trace bank and differential indices. -/
@[expose] def interfaceRequest (prepared : BoundaryPreparation preparation first second target radius floor)
    (position next : Fin prepared.fine.family.single.grid.faces.regulars.length) (side : GridSide)
    (matching : side.Matches
      (prepared.fine.family.single.grid.faces.regulars[position.val]'position.isLt).cell.box
      (prepared.fine.family.single.grid.faces.regulars[next.val]'next.isLt).cell.box)
    (selected : fineMask prepared.excision position = true)
    (discarded : fineMask prepared.excision next = false) :
    InterfaceRequest prepared.excision prepared.traces first second position side :=
  InterfaceRequest.build prepared.excision prepared.traces first second position next side matching selected discarded

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The exact retained interface remainder has squared norm at most four times the prepared fine component allowance.

Both the preparation and interface stages precede the supplied readings, so endpoint bounds and annular payment refer to
the same original cache and sheet. -/
theorem interface_bound (prepared : BoundaryPreparation preparation first second target radius floor)
    {position : Fin prepared.fine.family.single.grid.faces.regulars.length} {side : GridSide}
    (allocated : InterfaceRequest prepared.excision prepared.traces first second position side)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage)
    (interfaceLater : allocated.index ≤ stage) (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder readings.normalized
      position
      sheet side) ≤ 4 * prepared.fine.fine.component := by
  let samples := prepared.traces.samples cache first second
  let lengths := Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths.build samples
  have estimate := allocated.remainder_bound samples lengths interfaceLater prepared.sides.endpoints
    (prepared.sides.endpoints_le.trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)) readings.normalized
      sheet
  have paid : allocated.allowance ≤ prepared.fine.fine.component :=
    prepared.fine.fine.band_paid allocated.entry.hole.index
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) paid) (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq
      (by ring1))

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundaryInterfaces
