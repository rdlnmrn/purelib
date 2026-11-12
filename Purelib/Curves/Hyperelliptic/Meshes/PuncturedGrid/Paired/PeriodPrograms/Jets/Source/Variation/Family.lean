module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Jets.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Variation
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Jets.Values
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Differentials.Basic

/-! # Fixed transported families on the retained A and corrected-B source walks

A supplied complete source jet/connection/scalar-certificate bundle and its
whole original build factory precede all new derivative requests. One
original initial-walk value attachment then precedes one withVariationFamily
operation. That operation retains shared observations, one zero member and
an executable member rule before epsilon, and supplies the actual positive
radius, nonzero-increment/all-later bounds and signed strip transports.

The anchors are the two original PolynomialValues output programmes and
the separate old holomorphic value-zero programme. The second value is
x dx/y on this actual finite cycle. Reciprocal-cap identification, raw
canonical schedule realization, fresh endpoint bases and global geometric
monodromy are separate claims.
-/

public section

universe u

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (ParameterRange)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

section OriginalWalk

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {point : Canonical}
    {rootOwner : Owner ((Fibre.frameCurve frame).polynomial.eval point)} {source : Differential 1}
    {walk : PeriodWalk grid point rootOwner source} {valueFloor : Nat}
    (values : PolynomialValues walk valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (actual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- The original initial-walk attachment precedes the existing complete fixed-family continuation.

The actual source bundle stays the same given value. This exact function
type only composes its original value attachment with FamilyConsumer;
no callback payload, source, member or comparison certificate is copied.
-/
@[expose] def SourceFamilyConsumer
    (expected : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (attachment : ValueAttachment values expected) (originStart : Nat) (Result : Type u) : Type _ :=
  SourceValueAttachment (parameter := parameter) (frame := frame) (walk := walk)
    values expected attachment actual.1 →
  Requested.FamilyConsumer
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
    (chain := values.1.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
    (root := ownerName rootOwner) (roots := values.1.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    (sourceActual := actual) (originStart := originStart) Result

end OriginalWalk

/-- Anchor the given source bundle on its original A walk and construct its fixed transported family.

The whole source build factory gives only the original jet projection
readback. One original aSourceValueAttachment constructs its independent
canonical attachment; the given source bundle is not rebuilt. One existing
withVariationFamily then supplies shared observations, the zero member,
the member rule, strip transports and every epsilon's finite quotient
bounds. No increment or derivative accuracy is chosen by this constructor.
-/
def withASourceFamily {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.aWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (completed : requested.attempt.OccurrenceFamily)
    (actual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (factory : actual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : SourceFamilyConsumer (parameter := parameter) (frame := frame) (walk := prepared.aWalk index)
      (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) values same requested actual ranges allocation widths
      targetCurrent targetFloor targetRootStage
      (prepared.aOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.aValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      originStart Result) : Result :=
  have jetFactory : actual.1 = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val) :=
    (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
      factory).trans (OccurrenceCompletion.build_jet (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
        (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
  let anchored := aSourceValueAttachment (parameter := parameter) (frame := frame)
    (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
    (accuracy := reference) prepared index values same requested completed actual.1 jetFactory
  Requested.withVariationFamily
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
    (chain := values.1.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
    (roots := values.1.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    completed actual factory firstStart lastStart freshStart originStart spatial (consume anchored)

/-- Anchor the given source bundle on its original corrected-B walk and construct its fixed transported family.

The whole source build factory gives only the original jet projection
readback. One original bSourceValueAttachment constructs its independent
canonical attachment; the given source bundle is not rebuilt. One existing
withVariationFamily then supplies shared observations, the zero member,
the member rule, strip transports and every epsilon's finite quotient
bounds. No increment or derivative accuracy is chosen by this constructor.
-/
def withBSourceFamily {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : Prepared paired) (index : Fin 1) {valueFloor : Nat}
    (values : PolynomialValues (parameter := parameter) (frame := frame) (prepared.bWalk index) valueFloor)
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {reference : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage reference)
    (completed : requested.attempt.OccurrenceFamily)
    (actual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (factory : actual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
    (ranges : ParameterRange (values.1.sourceCovered same)) (allocation : ParameterRange.StripAllocation ranges)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : SourceFamilyConsumer (parameter := parameter) (frame := frame) (walk := prepared.bWalk index)
      (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) values same requested actual ranges allocation widths
      targetCurrent targetFloor targetRootStage
      (prepared.bOccurrenceJet index values floor rootStage (values.1.sourcePreparations same requested))
      (prepared.bValueAttachment index values floor rootStage (values.1.sourcePreparations same requested))
      originStart Result) : Result :=
  have jetFactory : actual.1 = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val) :=
    (congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => bundle.1)
      factory).trans (OccurrenceCompletion.build_jet (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
        (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))
  let anchored := bSourceValueAttachment (parameter := parameter) (frame := frame)
    (parent := parent) (parents := parents) (current := current) (floor := floor) (rootStage := rootStage)
    (accuracy := reference) prepared index values same requested completed actual.1 jetFactory
  Requested.withVariationFamily
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (parent := parent) (parents := parents) (covered := values.1.sourceCovered same)
    (chain := values.1.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
    (roots := values.1.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    completed actual factory firstStart lastStart freshStart originStart spatial (consume anchored)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
