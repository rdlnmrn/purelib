module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources

/-! # One source family on the SAME four actual retained quarter producers

The original Execution.Cache retains the actual original Steps or genuine
fine Layer realization for each quarter. These four complete source families
follow those SAME parents and literal full-cubic seam Owner handoffs. They
are shared by all scalar/primitive rows. Source preparation runs once per
actual input; no initial Source, old Steps execution, Root, trace, observer
or closing comparison is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Input

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable (execution : Cache initial secondInput thirdInput fourthInput)
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Four complete original source families follow the SAME actual old-or-fine paid quarter realizations.

This is the existing fourfold Product of each original mathematical
parent's source family. Their endpoint/sheet indices are the actual stored
seam handoffs, independently of later primitive-row observations.
-/
abbrev Sources :=
  Realization.Sources (site := site) (parameter := parameter) (unitQuarter := .first)
      (leg := circuit.first) (input := firstInput)
      (sourceOwner := sourceOwner) (agreement := agreement)
      (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) execution.first ×
    (Realization.Sources (site := site) (parameter := parameter) (unitQuarter := .second)
      (leg := circuit.second) (input := secondInput)
      (sourceOwner := execution.second.seam.owner) (agreement := execution.second.seam.nextAgreement)
      (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) execution.second.paid ×
      (Realization.Sources (site := site) (parameter := parameter) (unitQuarter := .third)
      (leg := circuit.third) (input := thirdInput)
      (sourceOwner := execution.third.seam.owner) (agreement := execution.third.seam.nextAgreement)
      (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) execution.third.paid ×
        Realization.Sources (site := site) (parameter := parameter) (unitQuarter := .fourth)
      (leg := circuit.fourth) (input := fourthInput)
      (sourceOwner := execution.fourth.seam.owner) (agreement := execution.fourth.seam.nextAgreement)
      (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) execution.fourth.paid))

namespace Sources

/-- Prepare the four original actual source families once in their oriented circuit order, shared by all rows. -/
def build : Sources (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) execution :=
  let first := Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.first
  let second := Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.second.paid
  let third := Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.third.paid
  let fourth := Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.fourth.paid
  ⟨first, ⟨second, ⟨third, fourth⟩⟩⟩

/-- The producer retains the complete four original family factories in their exact order, without an exposed body. -/
theorem build_eq :
    build (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) execution =
      (Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
          (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.first,
        (Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
            (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.second.paid,
          (Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
              (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.third.paid,
            Realization.Sources.build (frame := frame) (basis := basis) (count := modelCount)
              (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution.fourth.paid))) := by
  unfold build
  rfl

end Sources

end Steps.Acquisition.Quarter.Circuit.Execution.Cache

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
