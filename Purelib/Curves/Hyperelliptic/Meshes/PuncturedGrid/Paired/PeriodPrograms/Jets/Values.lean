module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Jets
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Values
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty

import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms

/-! # Both original canonical row values attached to their actual positional jet

The actual A or corrected B constructor executes once. Both comparisons
consume its same retained value programmes and the already supplied pair of
polynomial programmes. Nonemptiness comes from that very retained row's
original accepted cell count, rather than a new admission premise.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The exact retained positional jet factory and two original polynomial-value comparisons.

The original constructor value is an index, so each attachment retains its
same complete jet/relation bundle without replacing either programme owner.
-/
abbrev ValueAttachment {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {point : Canonical}
    {rootOwner : Owner ((Fibre.frameCurve frame).polynomial.eval point)} {source : Differential 1}
    {walk : PeriodWalk grid point rootOwner source} {valueFloor : Nat}
    (values : PolynomialValues walk valueFloor)
    (expected : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) : Type _ :=
  (actual : { value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet // value = expected }) ×
  NamedEquivalent values.2.1.2.val.integral.output.name (actual.val.1.value 0).integral.output.name ×
  NamedEquivalent values.2.2.1.2.val.integral.output.name (actual.val.1.value 1).integral.output.name

/-- Retain the actual A positional jet once and derive both original value-name attachments internally.

The subtype keeps the whole original jet/relation factory value. The two
comparisons preserve the polynomial programmes, source preparations and
same retained jet. They neither acquire another period bank nor assume
any final channel, connection or residual comparison.
-/
def aValueAttachment {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.aWalk index) valueFloor)
    (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    ValueAttachment (parameter := parameter) (frame := frame) (walk := prepared.aWalk index)
      values (prepared.aOccurrenceJet index values sourceFloor rootStage sources) :=
  let actual := prepared.aOccurrenceJet index values sourceFloor rootStage sources
  let nonempty := values.1.nonempty_of_initial_cells_positive
    (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0)
  have factory := congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
    (prepared.aOccurrenceJet_factory index values sourceFloor rootStage sources)
  let first := values.1.valueEquivalent values.2.1 sourceFloor rootStage sources nonempty actual.1 factory
  let second := values.1.valueEquivalent values.2.2.1 sourceFloor rootStage sources nonempty actual.1 factory
  ⟨⟨actual, rfl⟩, first, second⟩

/-- Retain the actual B positional jet once and derive both original value-name attachments internally.

The subtype keeps the whole original jet/relation factory value. The two
comparisons preserve the polynomial programmes, source preparations and
same retained jet. They neither acquire another period bank nor assume
any final channel, connection or residual comparison.
-/
def bValueAttachment {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.bWalk index) valueFloor)
    (sourceFloor rootStage : Nat)
    (sources : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path stage)) :
    ValueAttachment (parameter := parameter) (frame := frame) (walk := prepared.bWalk index)
      values (prepared.bOccurrenceJet index values sourceFloor rootStage sources) :=
  let actual := prepared.bOccurrenceJet index values sourceFloor rootStage sources
  let nonempty := values.1.nonempty_of_initial_cells_positive
    (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0)
  have factory := congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
    (prepared.bOccurrenceJet_factory index values sourceFloor rootStage sources)
  let first := values.1.valueEquivalent values.2.1 sourceFloor rootStage sources nonempty actual.1 factory
  let second := values.1.valueEquivalent values.2.2.1 sourceFloor rootStage sources nonempty actual.1 factory
  ⟨⟨actual, rfl⟩, first, second⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
