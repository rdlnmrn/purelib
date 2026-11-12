module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.FactorGeometry
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

/-! # Actual retained signed four-quarter detour construction

This ordinary-import client consumes the original producer's complete
numeric/reference cache and its actual signed cofold. It retains the
returned Owner beside the real closed-base trace and paid root comparison;
no desired final relation, Completion, Ready or Distinct is supplied.
-/
namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Hyperelliptic
open Steps.Acquisition.Quarter.Circuit.Execution

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre.Periods
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Riemann.Meshes
open Purelib.Polynomial.Geometry.Grid
open Purelib.RootIsolation.SquareRoot.Grid

/-- Construct the actual signed trace and root comparison through the original public cache owners. -/
private def retainedSignedTrace {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    Σ returned : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint,
      OwnerPath (Paths.polynomial parameter)
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) sourceOwner
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) returned ×
      NamedEquivalent (ownerName returned) (ownerName sourceOwner) :=
  let produced := Execution.Cache.prepareSignedDetour execution elimination clearances frame bank
  let retained := produced.1
  let cached := retained.val.2.1
  let references := cached.pointReferences retained.val.2.2
    (Cache.DetourReference.ambient_eq execution elimination clearances frame bank retained)
  let signed := produced.2
  ⟨Execution.Cache.Lines.DetourCache.Signed.returnOwner cached references signed,
    Execution.Cache.Lines.DetourCache.Signed.trace cached references signed,
    Execution.Cache.Lines.DetourCache.Signed.returnEquivalent cached references signed⟩

/-- The actual branch holes on the retained signed-detour grid all cross the same real axis.

This consumes the original framed-bank transport on the actual cached
detour grid. Its own selected-cell winding and clearance supply the
axis conclusion; no root/cycle correspondence or label order is given.
-/
private theorem retainedIncidence_axis {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (real : parameter.im = 0) (index : Branches.BranchIsolation.Data.Index branches) :
    let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank.toBranchCellBank
    let incidence := Cache.DetourReference.framedBank execution elimination clearances frame bank retained
    (incidence.val.cell index).box.yLower < 0 ∧ 0 < (incidence.val.cell index).box.yUpper := by
  intro retained incidence
  let cell := incidence.val.cell index
  have winding : Polynomial.Winding.Box.Basic.quadrupledBoxWinding (Paths.polynomial parameter) cell.box = 4 :=
    Hyperelliptic.Branches.BranchCellWinding.selected_winding_four incidence.val.toBranchCellBank index
  exact FactorGeometry.real_axis_of_winding real cell.box_proper cell.boundaryClearance
    (fun zero => (by decide +kernel : (4 : Int) ≠ 0) (winding.symm.trans zero))

/-- The actual old/new cell matching is derived on the same retained signed-detour grid.

Both finite matchings are checked from their own original winding cells.
The same-bank cell refinement in the retained incidence result proves
pointwise agreement, while keeping both complete finite bijections.
-/
private theorem retainedIncidence_labels {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (index : Branches.BranchIsolation.Data.Index branches) :
    let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank.toBranchCellBank
    let incidence := Cache.DetourReference.framedBank execution elimination clearances frame bank retained
    let oldLabels := Fibre.branchLabels frame bank.toBranchCellBank
    let currentLabels := Fibre.branchLabels frame incidence.val.toBranchCellBank
    oldLabels.val.forward index = currentLabels.val.forward index := by
  intro retained incidence oldLabels currentLabels
  exact Fibre.branchLabels_refines frame bank.toBranchCellBank incidence.val.toBranchCellBank
    oldLabels currentLabels incidence.property.2 index

/-- The retained real branch holes occupy the same actual horizontal grid band.

Both strict ordinate witnesses come from their own selected-cell winding
and clearance. Original grid-cell uniqueness retains the complete
vertical line interval, not just equal scalar endpoints.
-/
private theorem retainedIncidence_band {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (real : parameter.im = 0) (first last : Branches.BranchIsolation.Data.Index branches) :
    let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank.toBranchCellBank
    let incidence := Cache.DetourReference.framedBank execution elimination clearances frame bank retained
    (incidence.val.cell first).vertical = (incidence.val.cell last).vertical := by
  intro retained incidence
  have firstAxis := retainedIncidence_axis execution elimination clearances frame bank real first
  have lastAxis := retainedIncidence_axis execution elimination clearances frame bank real last
  exact Polynomial.Geometry.Grid.CellSeparation.vertical_eq_of_common_ordinate incidence.val.grid
    (incidence.val.cell_mem first) (incidence.val.cell_mem last)
    firstAxis ⟨lastAxis.1.le, lastAxis.2.le⟩

/-- The actual retained detour-grid window circuits contain exactly the moving and unit branch holes.

The same original execution supplies its refined framed bank. Its checked
logical matching and actual clear-side window construct the finite cell
circuits; their original membership law proves the pair selection. No
canonical row order, root-name correspondence or period identity is given.
-/
private theorem retainedIncidence_window {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1)
    (index : Branches.BranchIsolation.Data.Index branches) :
    let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank.toBranchCellBank
    let incidence := Cache.DetourReference.framedBank execution elimination clearances frame bank retained
    let labels := Fibre.branchLabels frame incidence.val.toBranchCellBank
    let window := Fibre.branchWindow incidence.val labels 1
    incidence.val.toBranchCellBank.cell index ∈ window.circuits.cells ↔ labels.val.forward index ≠ 0 := by
  intro retained incidence labels window
  have selected := Fibre.branchWindow_selected incidence.val labels real positive unit index
  constructor
  · intro member
    exact selected.mp (window.circuits_member.mp member).2
  · intro kept
    exact window.circuits_member.mpr ⟨incidence.val.toBranchCellBank.cell_mem index, selected.mpr kept⟩

/-- The original full-ambient branch preparation on the actual returned detour bank has its derived logical order.

The numerical detour retains its supplied branch labels and refined
framed bank. The original factories prepare that same grid's faces,
vertex/root/edge caches and full ambient window once. Its actual cached
partition then reads unit, moving and zero, without a supplied order or
any identification with the original source root channels or periods.
-/
private theorem retainedIncidence_order {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1) :
    let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank.toBranchCellBank
    let incidence := Cache.DetourReference.framedBank execution elimination clearances frame bank retained
    let labels := Fibre.branchLabels frame incidence.val.toBranchCellBank
    let faces := PuncturedGridFaces.PuncturedFaces.build incidence.val.toBranchCellBank
    let vertices := LiftedVertices.VertexBank.build incidence.val.grid
    let frames := RootFrames.build incidence.val.grid
    let edges := RootEdgeBank.build frames
    let window := WindowBoundary.Window.build incidence.val.grid (Cuts.Ambient (Fibre.frameCurve frame))
      incidence.val.frame.xLower incidence.val.frame.xUpper incidence.val.frame.yLower incidence.val.frame.yUpper
    let prepared := OrderedBranchCircuits.Window.prepareBranches faces window edges vertices 0
    prepared.labels.map labels.val.forward = [2, 1, 0] := by
  intro retained incidence labels faces vertices frames edges window prepared
  exact labels.window_labels real positive unit prepared

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
