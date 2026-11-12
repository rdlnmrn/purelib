module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients
public import Purelib.Curves.Legendre.Periods.Jets.Programs
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Data.Vector.Dependent
import Purelib.Calculus.Jet.DifferenceQuotient
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order

/-! # Actual model-stream source changes in the retained parameter quotients

The reference source, actual new source, whole reference completion factory
and genuine zero/increment member caches precede accuracy. Six executable
MODEL comparisons and the original paid quotient producer give independent
actual-source, reference-source and shifted floors. No derivative or final
closeness is assumed, and no original jet factory is identified with a
different source constructor.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent Comparison)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Specification
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (sourceCompleted : source.attempt.OccurrenceFamily) (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun stage => (sourceCompleted stage).val))
    {increment : Canonical}
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)

variable (actual : SynchronizedPeriodJet frame)
    (equivalent : (channel : Fin 6) →
      Equivalent (actual.programme channel).approximation (sourceJet.programme channel).approximation)

/-- Six actual model comparisons retain their original operators, increment-scaled target and complete factory.

Both input programme owners precede the target. The actual nonzero
increment pays division; the retained comparisons may select different
left and right stages and control all later original model samples.
-/
@[expose] def SourceComparisons (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (actualStart referenceStart : Nat) : Type _ :=
  { values : DependentVector (fun channel : Fin 6 =>
      Comparison (actual.programme channel).approximation (sourceJet.programme channel).approximation
        actualStart referenceStart ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)) //
    values = DependentVector.ofFn (fun channel : Fin 6 =>
      (equivalent channel).compare actualStart referenceStart
        ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
        (Order.Arithmetic.mul_pos_direct
          (accuracy.divide 16 (by decide +kernel)).positive (Norm.Basic.normSq_pos nonzero))) }

/-- Retain the actual six comparisons, original finite quotient cache and all three literal model floors.

The left floor reads the stored actual-source indices. The independent
reference floor pays both its original quotient and six right indices.
The shifted floor remains the one returned by the original quotient
producer. Only the first and third indices occur in the final quotient.
-/
@[expose] def ComparedSourceQuotientFloors (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (actualStart referenceStart originStart : Nat) : Type _ :=
  (compared : SourceComparisons (increment := increment) sourceJet actual equivalent
    accuracy nonzero actualStart referenceStart) ×
  (original : SourceQuotientFloors
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (increment := increment)
    (zeroAdmitted := zeroAdmitted) (admitted := admitted) sourceJet zero last
    (accuracy.divide 16 (by decide +kernel)) nonzero originStart) ×
  { floors : Nat × Nat × Nat //
    floors = (compared.val.maximum (fun _ value => value.leftIndex),
      Nat.max original.2.2.val.1 (compared.val.maximum (fun _ value => value.rightIndex)), original.2.2.val.2) ∧
    SourceQuotientBounds (parameter := parameter) (increment := increment) (frame := frame)
      (target := last.targetFrame) actual last.jet accuracy floors.1 floors.2.2 }

/-- Independent actual/reference indices and the original paid quotient imply each changed-source quotient.

The proof consumes the SAME stored comparison entries and reference
quotient certificate. Its reference index is independent of both visible
model indices. Existing perturbation_lt pays base division and slope
movement with their actual increment quadrance.
-/
private theorem source_quotientWithSource_lt (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1) {actualStart referenceStart originStart : Nat}
    (compared : SourceComparisons (increment := increment) sourceJet actual equivalent
      accuracy nonzero actualStart referenceStart)
    (original : SourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (increment := increment)
      (zeroAdmitted := zeroAdmitted) (admitted := admitted) sourceJet zero last
      (accuracy.divide 16 (by decide +kernel)) nonzero originStart)
    (order coordinate : Fin 2) (actualIndex referenceIndex lastIndex : Nat)
    (actualAfter : compared.val.maximum (fun _ value => value.leftIndex) ≤ actualIndex)
    (referenceAfter : Nat.max original.2.2.val.1
      (compared.val.maximum (fun _ value => value.rightIndex)) ≤ referenceIndex)
    (lastAfter : original.2.2.val.2 ≤ lastIndex) :
    Norm.Basic.normSq
      ((((last.jet.programme (Table.baseIndex order coordinate)).model lastIndex).integralSample -
        ((actual.programme (Table.baseIndex order coordinate)).model actualIndex).integralSample) / increment -
        ((actual.programme (Table.slopeIndex order coordinate)).model actualIndex).integralSample) <
      accuracy.tolerance := by
  have samplePaid (channel : Fin 6) :
      Norm.Basic.normSq
        (((actual.programme channel).model actualIndex).integralSample -
          ((sourceJet.programme channel).model referenceIndex).integralSample) <
        (accuracy.tolerance / 16) * Norm.Basic.normSq increment := by
    have leftAfter := (DependentVector.get_le_maximum (fun _ value => value.leftIndex)
      compared.val channel).trans actualAfter
    have rightAfter := (DependentVector.get_le_maximum (fun _ value => value.rightIndex)
      compared.val channel).trans ((Order.le_max_right _ _).trans referenceAfter)
    have paid := (compared.val.get channel).close leftAfter rightAfter
    exact (congrArg Norm.Basic.normSq (congrArg₂ (fun left right : Canonical => left - right)
      ((actual.programme channel).certifiedView_sample actualIndex)
      ((sourceJet.programme channel).certifiedView_sample referenceIndex))).symm.trans_lt paid
  have oldPaid := original.2.2.property.2 order coordinate referenceIndex lastIndex
    ((Order.le_max_left _ _).trans referenceAfter) lastAfter
  have oldPaid' : Norm.Basic.normSq
      ((((last.jet.programme (Table.baseIndex order coordinate)).model lastIndex).integralSample -
        ((sourceJet.programme (Table.baseIndex order coordinate)).model referenceIndex).integralSample) / increment -
        ((sourceJet.programme (Table.slopeIndex order coordinate)).model referenceIndex).integralSample) <
      accuracy.tolerance / 16 := by
    rewrite [last.jet.programme_base, sourceJet.programme_base, sourceJet.programme_slope]
    exact oldPaid
  exact Calculus.Jet.DifferenceQuotient.perturbation_lt accuracy increment
    ((actual.programme (Table.baseIndex order coordinate)).model actualIndex).integralSample
    ((last.jet.programme (Table.baseIndex order coordinate)).model lastIndex).integralSample
    ((actual.programme (Table.slopeIndex order coordinate)).model actualIndex).integralSample
    ((sourceJet.programme (Table.baseIndex order coordinate)).model referenceIndex).integralSample
    ((sourceJet.programme (Table.slopeIndex order coordinate)).model referenceIndex).integralSample
    nonzero unit (samplePaid (Table.baseIndex order coordinate))
      (samplePaid (Table.slopeIndex order coordinate)) oldPaid'

include sourceCompleted sourceFactory in
/-- Derive all four changed-source quotients from six-stream comparisons and one original quotient request.

All source/member owners and their whole factories are fixed before the
accuracy. The computed positive radius is sourceQuotientRequest at one
sixteenth accuracy. Every admitted nonzero increment below that radius
gets genuine increment-dependent comparisons BEFORE the original quotient
producer; the latter starts above their retained right maximum. The result
controls every later actual-source and shifted model pair, and retains an
independent sufficient reference stage. No new source or member is built.
-/
def sourceQuotientFloorsWithSource (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤
      (sourceQuotientRequest (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
        (accuracy.divide 16 (by decide +kernel))).tolerance)
    (actualStart firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) :
    ComparedSourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (increment := increment)
      (zeroAdmitted := zeroAdmitted) (admitted := admitted) sourceJet zero last actual equivalent accuracy nonzero
      actualStart firstStart originStart :=
  let share := accuracy.divide 16 (by decide +kernel)
  let compared : SourceComparisons (increment := increment) sourceJet actual equivalent
      accuracy nonzero actualStart firstStart :=
    ⟨DependentVector.ofFn (fun channel : Fin 6 => (equivalent channel).compare actualStart firstStart
      ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
      (Order.Arithmetic.mul_pos_direct share.positive (Norm.Basic.normSq_pos nonzero))), rfl⟩
  have referenceSmall := small.trans (sourceQuotientRequest_le_reference
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation) share)
  have unit := referenceSmall.trans (ShiftedGeometry.BetweenRows.referenceRequest_le_unit
    (covered := covered) (share.divide 16 (by decide +kernel)))
  let original := sourceQuotientFloors
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (increment := increment)
    (zeroAdmitted := zeroAdmitted) (admitted := admitted)
    sourceCompleted sourceJet sourceFactory zero last share nonzero referenceSmall
    (Nat.max firstStart (compared.val.maximum (fun _ value => value.rightIndex)))
    lastStart freshStart originStart spatial
  let floors := (compared.val.maximum (fun _ value => value.leftIndex),
    Nat.max original.2.2.val.1 (compared.val.maximum (fun _ value => value.rightIndex)), original.2.2.val.2)
  have accurate : SourceQuotientBounds (parameter := parameter) (increment := increment) (frame := frame)
      (target := last.targetFrame) actual last.jet accuracy floors.1 floors.2.2 := by
    intro order coordinate actualIndex lastIndex actualAfter lastAfter
    have paid := source_quotientWithSource_lt
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (increment := increment) (zeroAdmitted := zeroAdmitted)
      (admitted := admitted) sourceJet zero last actual equivalent accuracy nonzero unit compared original
      order coordinate actualIndex floors.2.1 lastIndex actualAfter (Nat.le_refl _) lastAfter
    rewrite [last.jet.programme_base, actual.programme_base, actual.programme_slope] at paid
    exact paid
  ⟨compared, original, ⟨floors, rfl, accurate⟩⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
