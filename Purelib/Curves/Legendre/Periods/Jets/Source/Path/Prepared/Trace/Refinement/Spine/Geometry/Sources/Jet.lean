module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Connection
public import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Stage
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Fin
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Actual child-bank sources attached to six adaptive programmes

One fixed geometry, its given closed child chain, actual request-bank rule
and complete occurrence rule supply every source stage and model list.
The original Source.Attachment and synchronized-jet constructors consume
them directly. Existing ofJet operations derive their original connection
and scalar residual certificates; no final comparison is an input.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive closed.traced.lineage inputCenters materialized factory)
variable (childChain : CenteredPathChain retained.parents (start := (⟨base, sheet⟩ : LiftedPoint 2))
  (finish := (⟨base, sheet⟩ : LiftedPoint 2)))

namespace Geometry.Sources

variable (precision : Nat → Nat)
variable (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
  value = CellEndpoints.Targets.build childChain.path (precision index) })
variable (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
  (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
variable {rootStage : Nat} {walkPositive : 0 < closed.walk.edgeCount}
variable (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
  owner closed retained childChain (precision index) rootStage
    (requested index).val (requested index).property (sourceBanks index) walkPositive)

/-- Attach the SAME actual occurrence stages to the six adaptive original-bank programmes and retained lifted cycle.

The given complete occurrence rule remains the owner of its original
attempt, bank, base Found and both old outcomes. Only Stage.lower changes
the programme index. Both source-list equations are derived internally
from those same completed stages and original-bank readbacks.

A function remains an executable rule. Independent programme and stage
callbacks may invoke their given rules independently; no memoization or
cross-callback acquisition sharing is asserted.
-/
def jet (precisionFloor : ∀ index, index ≤ precision index) : SynchronizedPeriodJet frame := by
  let programmes := certifiedAtPrecision (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) retained childChain precision requested sourceBanks precisionFloor
  let value : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter coordinate) (PreparedParents.constantCycle childChain) :=
    Fin.cases (programmes 0) (Fin.cases (programmes 1) (fun index => Fin.elim0 index))
  let first : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter coordinate) (PreparedParents.constantCycle childChain) :=
    Fin.cases (programmes 2) (Fin.cases (programmes 3) (fun index => Fin.elim0 index))
  let second : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter coordinate) (PreparedParents.constantCycle childChain) :=
    Fin.cases (programmes 4) (Fin.cases (programmes 5) (fun index => Fin.elim0 index))
  let stages := fun index => (completed index).stage.lower index (precisionFloor index)
  have stageCells (index : Nat) (channel : Fin 6) :
      (stages index).sources.cells channel = cells (count := count) (floor := floor)
        (original := childChain.path) (stage := precision index) (targets := (requested index).val)
        retained (sourceBanks index) channel := by
    have lowered := congrArg (fun actual : Path parameter childChain.path => actual.cells channel)
      (Stage.lower_sources (completed index).stage index (precisionFloor index))
    exact lowered.trans ((completed index).stage_cells channel)
  have modelCells (index : Nat) (channel : Fin 6) :
      ((programmes channel).integral.model index).cells = (stages index).sources.cells channel :=
    (certifiedAtPrecision_cells (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) retained childChain precision requested sourceBanks precisionFloor
      channel index).trans (stageCells index channel).symm
  let attached : Attachment frame (PreparedParents.constantCycle childChain) value first second :=
    { stages := stages
      valueZero_eq := fun index => modelCells index 0
      valueOne_eq := fun index => modelCells index 1
      firstZero_eq := fun index => modelCells index 2
      firstOne_eq := fun index => modelCells index 3
      secondZero_eq := fun index => modelCells index 4
      secondOne_eq := fun index => modelCells index 5 }
  exact SynchronizedPeriodJet.ofSource (PreparedParents.constantCycle childChain) value first second attached

/-- The actual synchronized jet retains the GIVEN closed child chain at every programme index. -/
theorem jet_cycle (precisionFloor : ∀ index, index ≤ precision index) :
    (jet owner closed retained childChain precision requested sourceBanks completed precisionFloor).cycle =
      PreparedParents.constantCycle childChain := by
  unfold jet
  rfl

/-- Every actual jet Stage is the SAME completed Stage lowered only to its programme index. -/
theorem jet_stages (precisionFloor : ∀ index, index ≤ precision index) (index : Nat) :
    HEq ((jet owner closed retained childChain precision requested sourceBanks completed precisionFloor).source.stages
      index) ((completed index).stage.lower index (precisionFloor index)) := by
  unfold jet
  rfl

/-- Each actual jet value retains the identical whole adaptive programme on its original bank channel. -/
theorem jet_value_integral (precisionFloor : ∀ index, index ≤ precision index) (coordinate : Fin 2) :
    (((jet owner closed retained childChain precision requested sourceBanks completed precisionFloor).value
      coordinate).integral) =
    (certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor
      (Specification.Table.valueIndex coordinate)).integral := by
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun empty => Fin.elim0 empty) index) coordinate
  · unfold jet
    rfl
  · unfold jet
    rfl

/-- Each actual first differential programme retains its SAME adaptive bank-channel owner. -/
theorem jet_first_integral (precisionFloor : ∀ index, index ≤ precision index) (coordinate : Fin 2) :
    (((jet owner closed retained childChain precision requested sourceBanks completed precisionFloor).first
      coordinate).integral) =
    (certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor
      (Specification.Table.firstIndex coordinate)).integral := by
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun empty => Fin.elim0 empty) index) coordinate
  · unfold jet
    rfl
  · unfold jet
    rfl

/-- Each actual second differential programme retains its SAME adaptive bank-channel owner. -/
theorem jet_second_integral (precisionFloor : ∀ index, index ≤ precision index) (coordinate : Fin 2) :
    (((jet owner closed retained childChain precision requested sourceBanks completed precisionFloor).second
      coordinate).integral) =
    (certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor
      (Specification.Table.secondIndex coordinate)).integral := by
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun empty => Fin.elim0 empty) index) coordinate
  · unfold jet
    rfl
  · unfold jet
    rfl

/-- Bind one actual jet and derive both original relation certificates from its SAME retained source attachment.

Connection.ofJet and PicardFuchs.ofJet keep the actual Stage-zero base
primitive owners and derive their all-later comparison fields internally.
The supplied completed rule remains available with its whole factories and
old outcomes; this operation creates no source, geometric or root producer.
-/
def jetWithRelations (precisionFloor : ∀ index, index ≤ precision index) :
    (actual : SynchronizedPeriodJet frame) × Connection.ConnectionCertificate actual ×
      PicardFuchs.PicardFuchsCertificate actual :=
  let actual := jet owner closed retained childChain precision requested sourceBanks completed precisionFloor
  let connection := Connection.ConnectionCertificate.ofJet actual
  let residual := PicardFuchs.PicardFuchsCertificate.ofJet actual
  ⟨actual, connection, residual⟩

/-- The retained relation bundle has that SAME whole synchronized-jet factory. -/
theorem jetWithRelations_jet (precisionFloor : ∀ index, index ≤ precision index) :
    (jetWithRelations owner closed retained childChain precision requested sourceBanks completed precisionFloor).1 =
      jet owner closed retained childChain precision requested sourceBanks completed precisionFloor := by
  unfold jetWithRelations
  rfl

/-- Construct the actual occurrence rule from the GIVEN banks, sharing one fixed original root-chain cache.

The rooted cache is bound before the programme-index rule. Each invocation
of that rule binds its actual bank and flattened preparation once, then
runs the original occurrence worker on those SAME caches. The Stage-zero
completion is bound once for the two relation constructors. The continuation
retains the whole rule and shared-root factory beside the actual jet and
both internally derived relation certificates. Independent invocations of
the supplied bank rule remain independent executions.
-/
def withJet (precisionFloor : ∀ index, index ≤ precision index) {Result : Type u}
    (consume :
      (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
        value = Geometry.closedRoots owner closed retained}) →
      (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
        owner closed retained childChain (precision index) rootStage
          (requested index).val (requested index).property (sourceBanks index) walkPositive) →
      (_shared : ∀ index, (completed index).2.1 = rooted) →
      (actual : SynchronizedPeriodJet frame) →
      (_jetFactory : actual =
        jet owner closed retained childChain precision requested sourceBanks completed precisionFloor) →
      Connection.ConnectionCertificate actual → PicardFuchs.PicardFuchsCertificate actual → Result) : Result := by
  let rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained} := ⟨Geometry.closedRoots owner closed retained, rfl⟩
  let atIndex := fun index =>
    let sourceBank := sourceBanks index
    let prepared : {value : PreparedParents retained.covered floor (requested index).val //
        value = preparations retained sourceBank} := ⟨preparations retained sourceBank, rfl⟩
    completeOccurrencesFromCaches (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (sheet := sheet) owner closed retained childChain
      (precision index) rootStage (requested index).val (requested index).property sourceBank walkPositive
      prepared rooted
  have sharedAt : ∀ index, (atIndex index).2.1 = rooted := by
    intro index
    dsimp only [atIndex]
    exact completeOccurrencesFromCaches_rooted (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (sheet := sheet) owner closed retained childChain
      (precision index) rootStage (requested index).val (requested index).property (sourceBanks index) walkPositive
      ⟨preparations retained (sourceBanks index), rfl⟩ rooted
  let zero := atIndex 0
  let completed : (index : Nat) → Occurrences (count := count) (floor := floor)
      owner closed retained childChain (precision index) rootStage
        (requested index).val (requested index).property (sourceBanks index) walkPositive := fun index =>
    Nat.casesOn index zero (fun previous => atIndex (previous + 1))
  have shared : ∀ index, (completed index).2.1 = rooted := by
    intro index
    cases index with
    | zero => exact sharedAt 0
    | succ previous => exact sharedAt (previous + 1)
  let actual := jetWithRelations owner closed retained childChain precision requested sourceBanks completed
    precisionFloor
  exact consume rooted completed shared actual.1
    (jetWithRelations_jet owner closed retained childChain precision requested sourceBanks completed precisionFloor)
    actual.2.1 actual.2.2

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
