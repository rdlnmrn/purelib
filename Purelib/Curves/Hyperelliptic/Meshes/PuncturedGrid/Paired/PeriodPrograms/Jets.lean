module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-! # Actual A/B positional jets from the retained ordered period bank

The original prepared row supplies each actual closed period walk, all root
links and its nonempty accepted integration spine. The already retained
polynomial value cache supplies its same spine. Source preparations remain
literal supplied caches; no period bank, old observation or value programme
is acquired again. Positional completion derives the source attachment and
the existing ofJet operations derive both relation certificates internally.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)

section

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}

/-- Construct the actual retained A row's same-spine six-channel jet and internally derived relations.

The nonempty certificate is derived from this very prepared row's original
zero-stage model. The supplied polynomial values, spine, root links and
source preparation family remain their original complete input owners.
-/
def aOccurrenceJet (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.aWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    (actual : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate actual × Jets.PicardFuchs.PicardFuchsCertificate actual :=
  values.1.occurrenceJet sourceFloor rootStage sources
    (values.1.nonempty_of_initial_cells_positive (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0))

/-- The whole A construction uses its original same-spine factory and internally recovered nonempty proof. -/
private theorem packaged_aOccurrenceJet_factory
    (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.aWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    prepared.aOccurrenceJet index values sourceFloor rootStage sources =
      values.1.occurrenceJet sourceFloor rootStage sources
        (values.1.nonempty_of_initial_cells_positive
          (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0)) := by rfl

/-- The whole A construction uses its original same-spine factory and internally recovered nonempty proof. -/
theorem aOccurrenceJet_factory
    (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.aWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    prepared.aOccurrenceJet index values sourceFloor rootStage sources =
      values.1.occurrenceJet sourceFloor rootStage sources
        (values.1.nonempty_of_initial_cells_positive
          (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0)) :=
  prepared.packaged_aOccurrenceJet_factory index values sourceFloor rootStage sources

/-- Construct the corrected retained B row's same-spine six-channel jet and internally derived relations.

The actual corrected walk's nonemptiness is recovered from its retained
zero-stage programme. Its preceding B corrections, ordered repeated visits,
original root links and supplied source preparations are not replaced.
-/
def bOccurrenceJet (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.bWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    (actual : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate actual × Jets.PicardFuchs.PicardFuchsCertificate actual :=
  values.1.occurrenceJet sourceFloor rootStage sources
    (values.1.nonempty_of_initial_cells_positive (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0))

/-- The whole B construction uses its original same-spine factory and internally recovered nonempty proof. -/
private theorem packaged_bOccurrenceJet_factory
    (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.bWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    prepared.bOccurrenceJet index values sourceFloor rootStage sources =
      values.1.occurrenceJet sourceFloor rootStage sources
        (values.1.nonempty_of_initial_cells_positive
          (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0)) := by rfl

/-- The whole B construction uses its original same-spine factory and internally recovered nonempty proof. -/
theorem bOccurrenceJet_factory
    (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.bWalk index) valueFloor) (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    prepared.bOccurrenceJet index values sourceFloor rootStage sources =
      values.1.occurrenceJet sourceFloor rootStage sources
        (values.1.nonempty_of_initial_cells_positive
          (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0)) :=
  prepared.packaged_bOccurrenceJet_factory index values sourceFloor rootStage sources

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
