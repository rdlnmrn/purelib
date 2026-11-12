module
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

/-! # The literal first middle of the complete signed detour

The original signed producer, labelled incidence and canonical lift are
retained once. The first source vertex comes from its stored line cache;
the original frame supplies its actual sheet and anchor connector.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
namespace Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts
  (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

variable {site : Fin 2} {parameter : Canonical} {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)

open Purelib.Curves.Legendre.Periods
open Execution.Cache
open Execution.Cache.Lines.DetourCache
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable (execution : Execution.Cache initial secondInput thirdInput fourthInput)
variable (frame : Paths.Frame parameter)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable (bank : FramedBranchCellBank (Fibre.frameCurve frame) branches higher)

/-- The exact original retained output type of the four-quarter signed producer. -/
private abbrev SignedResult :=
  Σ retained : { value : DetourReference execution elimination clearances frame bank.toBranchCellBank //
      value = execution.detourWithReference elimination clearances frame bank.toBranchCellBank },
    Signed retained.val.2.1
      (retained.val.2.1.pointReferences retained.val.2.2
        (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank retained))

/-- The original labelled branch-incidence result on the same retained numerical grid. -/
private abbrev Incidence (produced : SignedResult elimination clearances execution frame bank) :=
  { target : FramedBranchCellBank (Fibre.frameCurve frame) branches higher //
    target.grid = produced.1.val.2.1.val.1 ∧
      ∀ index, (target.cell index).box.Refines (bank.cell index).box }

/-- The same canonical lift retained with its complete original factory identity. -/
private abbrev CanonicalLift {produced : SignedResult elimination clearances execution frame bank}
    (incidence : Incidence elimination clearances execution frame bank produced) :=
  { value : LiftedPuncturedGrid (FramedPuncturedGrid.ofBank incidence.val) //
    value = LiftedPuncturedGrid.build (FramedPuncturedGrid.ofBank incidence.val) }

/-- The original signed producer and canonical incidence retain the actual first middle selection and anchor lift. -/
private abbrev FirstAnchor :=
  Σ produced : SignedResult elimination clearances execution frame bank,
  let vertex := Input.Realization.sourceVertex elimination clearances produced.1.val.2.1.val.1
    execution.first produced.1.val.1.val.1 produced.1.val.2.1.onGrid.1
  Σ incidence : { value : Incidence elimination clearances execution frame bank produced //
      value = DetourReference.framedBank execution elimination clearances frame bank produced.1.val },
  Σ lifted : CanonicalLift elimination clearances execution frame bank incidence.val,
  Σ selected : RootOwnerFrames.OwnerSelection
      (lifted.val.frames.frameAt vertex.val
        (Eq.mpr (congrArg (fun currentGrid => Grid.FromStates.ContainsVertex currentGrid vertex.val)
          incidence.val.property.1) vertex.property.2)).owners
      (castOwnerParameter (congrArg (Paths.polynomial parameter).eval vertex.property.1.symm)
        (Signed.middleSource produced.1.val.2.1
          (produced.1.val.2.1.pointReferences produced.1.val.2.2
            (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank
              produced.1)) produced.2)),
  Σ anchorSheet : Fin 2,
    RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk lifted.val.edges
      (Cuts.Ambient (Fibre.frameCurve frame)).anchor anchorSheet
      vertex.val selected.index

/-- Execute the original signed producer once and attach its literal first middle to its own canonical incidence frame.

The actual four-quarter result, original labelled refinement and canonical
lift are retained with their whole factory identities. The source vertex
proof is read directly from the same retained closed numerical Walk. One
original frame selection consumes the literal first signed middle Owner.
The original connector is retained on its backward-computed anchor sheet;
no canonical word identity, chosen sheet or physical cancellation is an
input.
-/
private def retainedCircuit_firstAnchor : FirstAnchor elimination clearances execution frame bank :=
  let produced := execution.prepareSignedDetour elimination clearances frame bank.toBranchCellBank
  let incidence := DetourReference.framedBank execution elimination clearances frame bank produced.1.val
  let lifted := LiftedPuncturedGrid.build (FramedPuncturedGrid.ofBank incidence.val)
  let middle := Signed.middleSource produced.1.val.2.1
    (produced.1.val.2.1.pointReferences produced.1.val.2.2
      (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank
        produced.1)) produced.2
  let vertex := Input.Realization.sourceVertex elimination clearances produced.1.val.2.1.val.1
    execution.first produced.1.val.1.val.1 produced.1.val.2.1.onGrid.1
  let firstOn := Eq.mpr (congrArg (fun currentGrid => Grid.FromStates.ContainsVertex currentGrid vertex.val)
      incidence.property.1) vertex.property.2
  let actualMiddle := castOwnerParameter
    (congrArg (Paths.polynomial parameter).eval vertex.property.1.symm) middle
  let selected := (lifted.frames.frameAt vertex.val firstOn).select actualMiddle
  let connector := LoopMonodromy.Grid.connect incidence.val.grid
    (Cuts.Ambient (Fibre.frameCurve frame)).anchor
    vertex.val
    (BasedBranchTours.FramedBranchCellBank.baseMember incidence.val) firstOn
  let anchorSheet := RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target
    lifted.edges connector.reverse selected.index
  ⟨produced, ⟨incidence, rfl⟩, ⟨lifted, rfl⟩, selected, anchorSheet, connector,
    BasedBranchTours.FramedBranchCellBank.baseMember incidence.val, firstOn,
    lifted.edges.target_reverse_right
      (fun point member => (LoopMonodromy.BranchCellBank.referenceAt
        incidence.val.toBranchCellBank point member).toLoop) connector selected.index⟩

end Circuit
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
