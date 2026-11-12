module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Jets.Values
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Requested
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.Periods.PreparedGridPeriodPrograms

/-! # Canonical A and corrected-B values on their actual retained source jets

The original accepted canonical row supplies nonemptiness and the exact
closed parent/root spine. One original Requested preparation precedes the
source endpoint construction. Value attachment consumes its retained
completed family and actual jet, without reconstructing either of them.
-/

public section

universe u

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The exact original value attachment and its three derived comparisons to one given source jet.

The retained constructor and attachment values are indices, not comparison
premises. The third comparison preserves the independent old holomorphic
value-zero programme; value one remains the original polynomial x dx/y
programme on its actual retained closed cycle.
-/
abbrev SourceValueAttachment {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {point : Canonical}
    {rootOwner : Owner ((Fibre.frameCurve frame).polynomial.eval point)} {source : Differential 1}
    {walk : PeriodWalk grid point rootOwner source} {valueFloor : Nat}
    (values : PolynomialValues walk valueFloor)
    (expected : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (attachment : ValueAttachment values expected) (actual : SynchronizedPeriodJet frame) : Type _ :=
  (_canonical : { value : ValueAttachment values expected // value = attachment }) ×
  NamedEquivalent values.2.1.2.val.integral.output.name (actual.value 0).integral.output.name ×
  NamedEquivalent values.2.2.1.2.val.integral.output.name (actual.value 1).integral.output.name ×
  NamedEquivalent values.2.2.2.val.integral.output.name (actual.value 0).integral.output.name

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}

/-- Prepare one original source request on the SAME retained canonical A parent/root spine.

Nonemptiness is derived from that row's actual accepted initial cells.
The original walk, signed occurrences, lifted vertices and root links
remain unchanged; no independent physical-cycle realization is assumed.
-/
def withASource (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.aWalk index) valueFloor) (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    {Result : Type u} (consume : values.1.RequestedConsumer current floor rootStage accuracy Result) : Result :=
  values.1.withRequested
    (values.1.nonempty_of_initial_cells_positive (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0))
    current floor rootStage accuracy consume

/-- Prepare one original source request on the SAME retained canonical corrected B parent/root spine.

Nonemptiness is derived from that row's actual accepted initial cells.
The original walk, signed occurrences, lifted vertices and root links
remain unchanged; no independent physical-cycle realization is assumed.
-/
def withBSource (values : PolynomialValues (parameter := parameter) (frame := frame)
      (prepared.bWalk index) valueFloor) (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    {Result : Type u} (consume : values.1.RequestedConsumer current floor rootStage accuracy Result) : Result :=
  values.1.withRequested
    (values.1.nonempty_of_initial_cells_positive (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0))
    current floor rootStage accuracy consume

/-- Attach both canonical A values to the SAME already-retained original source jet.

The actual original value attachment executes once and remains in the
result with its whole factory. Its independent canonical occurrence jet
and both comparisons are retained. Its separately stored old holomorphic
dx/y programme also has a derived comparison to source value zero. Original
preparation/model readbacks identify the source at every sample stage; no source family,
completion, source observation, connection trace or Frame is rebuilt.
-/
def aSourceValueAttachment
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.aWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val)) :
    SourceValueAttachment (parameter := parameter) (frame := frame) (walk := prepared.aWalk index)
      values (prepared.aOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.aValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      actual :=
  let sources := values.1.sourcePreparations same requested
  let canonical := prepared.aValueAttachment index values floor rootStage sources
  have nonempty := values.1.nonempty_of_initial_cells_positive
    (PeriodNonempty.Prepared.aProgram_cells_positive prepared 0 index 0)
  have canonicalFactory := (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
    canonical.1.property).trans
    (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
      (prepared.aOccurrenceJet_factory (parameter := parameter) (frame := frame)
        index values floor rootStage sources))
  let first := values.1.sourceValueEquivalent (parameter := parameter) (frame := frame)
    (walk := prepared.aWalk index) (parent := parent) (parents := parents)
    same requested completed actual factory nonempty canonical.1.val.1 canonicalFactory 0
  let second := values.1.sourceValueEquivalent (parameter := parameter) (frame := frame)
    (walk := prepared.aWalk index) (parent := parent) (parents := parents)
    same requested completed actual factory nonempty canonical.1.val.1 canonicalFactory 1
  let firstSource := canonical.2.1.trans first
  let old := (prepared.aWalk index).polynomialValues_valueZero_equivalent
    (parameter := parameter) (frame := frame) values
  ⟨⟨canonical, rfl⟩, firstSource, canonical.2.2.trans second, old.symm.trans firstSource⟩

/-- Attach both canonical corrected B values to the SAME already-retained original source jet.

The actual original value attachment executes once and remains in the
result with its whole factory. Its independent canonical occurrence jet
and both comparisons are retained. Its separately stored old holomorphic
dx/y programme also has a derived comparison to source value zero. Original
preparation/model readbacks identify the source at every sample stage; no source family,
completion, source observation, connection trace or Frame is rebuilt.
-/
def bSourceValueAttachment
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.bWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val)) :
    SourceValueAttachment (parameter := parameter) (frame := frame) (walk := prepared.bWalk index)
      values (prepared.bOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.bValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      actual :=
  let sources := values.1.sourcePreparations same requested
  let canonical := prepared.bValueAttachment index values floor rootStage sources
  have nonempty := values.1.nonempty_of_initial_cells_positive
    (PeriodNonempty.Prepared.bProgram_cells_positive prepared 0 index 0)
  have canonicalFactory := (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
    canonical.1.property).trans
    (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
      (prepared.bOccurrenceJet_factory (parameter := parameter) (frame := frame)
        index values floor rootStage sources))
  let first := values.1.sourceValueEquivalent (parameter := parameter) (frame := frame)
    (walk := prepared.bWalk index) (parent := parent) (parents := parents)
    same requested completed actual factory nonempty canonical.1.val.1 canonicalFactory 0
  let second := values.1.sourceValueEquivalent (parameter := parameter) (frame := frame)
    (walk := prepared.bWalk index) (parent := parent) (parents := parents)
    same requested completed actual factory nonempty canonical.1.val.1 canonicalFactory 1
  let firstSource := canonical.2.1.trans first
  let old := (prepared.bWalk index).polynomialValues_valueZero_equivalent
    (parameter := parameter) (frame := frame) values
  ⟨⟨canonical, rfl⟩, firstSource, canonical.2.2.trans second, old.symm.trans firstSource⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
