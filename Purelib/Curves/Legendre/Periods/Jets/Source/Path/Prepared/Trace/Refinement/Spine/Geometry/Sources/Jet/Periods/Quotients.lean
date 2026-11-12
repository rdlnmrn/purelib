module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Periods
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Variation
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries.Periods
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Accuracy

import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Actual canonical-origin quotients on the retained adaptive local family

The original family selector runs at one-sixteenth requested accuracy.
Its same radius/member/paid h-result precedes two genuine canonical MODEL
comparisons at increment-paid tolerance. All later source, canonical and
shifted readings retain independent indices and their actual owners.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent Comparison)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order.Arithmetic (instZeroLEOneClass)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- The two actual fixed-source/canonical MODEL comparisons and their exact increment-paid factory.

Each comparison keeps its own canonical start and right index. The source
start is the original paid adaptive floor, so comparison construction
consumes that actual h-result rather than an unrelated guessed schedule.
-/
@[expose] def OriginComparisons {parameter : Canonical} {frame : Paths.Frame parameter}
    (actual : SynchronizedPeriodJet frame) (base : Fin 2 → RefinementProgram)
    (equivalent : (coordinate : Fin 2) →
      Equivalent (actual.value coordinate).integral.approximation (base coordinate).approximation)
    (increment : Canonical) (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (sourceStart : Nat) (periodStart : Fin 2 → Nat) : Type _ :=
  { compared : DependentVector (fun coordinate : Fin 2 =>
      Comparison (actual.value coordinate).integral.approximation (base coordinate).approximation
        sourceStart (periodStart coordinate) ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)) //
    compared = DependentVector.ofFn (fun coordinate : Fin 2 =>
      (equivalent coordinate).compare sourceStart (periodStart coordinate)
        ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
        (Arithmetic.mul_pos_direct (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).positive
          (Norm.Basic.normSq_pos nonzero))) }

section Family

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
    (sourceActual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (equivalent : (channel : Fin 6) →
      Equivalent (adaptive.1.programme channel).approximation (sourceActual.1.programme channel).approximation)
    (observed : EndpointObservations source.prepared
      ⟨Fraction.Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩
      ⟨instZeroLEOneClass.zero_le_one, Fraction.Order.Basic.le_refl 1⟩)
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    (zero : StripMember roots widths targetCurrent targetFloor targetRootStage observed 0 zeroPaid)
    (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.bound) →
      StripMember roots widths targetCurrent targetFloor targetRootStage observed offset admitted)
    (base : Fin 2 → RefinementProgram)
    (canonical : (coordinate : Fin 2) →
      Equivalent (adaptive.1.value coordinate).integral.approximation (base coordinate).approximation)

/-- One actual original family accuracy run and its h-dependent canonical-origin comparison caches.

The existing h-result and both whole factories are retained unchanged.
Literal floors keep adaptive, independent reference, two canonical and
shifted stages separate. The final all-later claim concerns the actual
same-member StageData and its original completion equation.
-/
@[expose] def OriginFamilyAccuracy (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (selectAccuracy : (accuracy : AccuracyRequest) →
      ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy)
    (accuracy : AccuracyRequest) : Type _ :=
  (original : { value : ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))) //
    value = selectAccuracy (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))) }) ×
  ((increment : Canonical) → (nonzero : increment ≠ 0) →
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) →
    (given : {value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed increment admitted // value = members increment admitted}) →
    (small : Norm.Basic.normSq increment ≤ original.val.1.val.tolerance) →
    (old : {value : ComparedMemberAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart (accuracy.divide 16
        (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))) increment nonzero admitted given //
      value = original.val.2 increment nonzero admitted given small}) ×
    (compared : OriginComparisons adaptive.1 base canonical increment accuracy nonzero
      old.val.2.val.2.2.val.1 periodStart) ×
    { floors : Nat × Nat × (Fin 2 → Nat) × Nat //
      floors = (Nat.max old.val.2.val.2.2.val.1 (compared.val.maximum (fun _ value => value.leftIndex)),
        old.val.2.val.2.2.val.2.1, (fun coordinate => (compared.val.get coordinate).rightIndex),
        old.val.2.val.2.2.val.2.2) ∧
      LocalMember.OriginQuotientBounds old.val.1.val.member adaptive.1 base accuracy
        floors.1 floors.2.2.1 floors.2.2.2 })

/-- Run the SAME original selector at share accuracy, then derive both canonical comparisons before later readings.

The actual selected h-member and original paid cache are inputs to the
comparison start; no source, member, StageData, observation or quotient
factory is replayed. The original positive radius pays the unit bound,
and existing quotient perturbation derives the final four-row accuracy.
-/
def selectOriginFamily (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (selectAccuracy : (accuracy : AccuracyRequest) → ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy)
    (accuracy : AccuracyRequest) :
    OriginFamilyAccuracy (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members base canonical
      actualStart firstStart originStart periodStart selectAccuracy accuracy :=
  let original := selectAccuracy (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))
  ⟨⟨original, rfl⟩, fun increment nonzero admitted given small =>
    let old := original.2 increment nonzero admitted given small
    let sourceStart := old.2.val.2.2.val.1
    let compared : OriginComparisons adaptive.1 base canonical increment accuracy nonzero sourceStart periodStart :=
      ⟨DependentVector.ofFn (fun coordinate : Fin 2 =>
        (canonical coordinate).compare sourceStart (periodStart coordinate)
          ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
          (Arithmetic.mul_pos_direct (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).positive
            (Norm.Basic.normSq_pos nonzero))), rfl⟩
    let floors := (Nat.max sourceStart (compared.val.maximum (fun _ value => value.leftIndex)),
      old.2.val.2.2.val.2.1, (fun coordinate => (compared.val.get coordinate).rightIndex),
      old.2.val.2.2.val.2.2)
    have actualSmall := small.trans_eq (congrArg AccuracyRequest.tolerance original.1.property)
    have referenceSmall := actualSmall.trans (LocalMember.sourceQuotientRequest_le_reference
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
      ((accuracy.divide 16
        (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).divide 16
          (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))))
    have unit := referenceSmall.trans
      (ShiftedGeometry.BetweenRows.referenceRequest_le_unit (covered := covered)
        (((accuracy.divide 16
          (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).divide 16
            (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).divide 16
              (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))))
    have accurate := LocalMember.originQuotient_accurate
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (offset := increment) (admitted := admitted)
      old.1.val.member adaptive.1 base accuracy nonzero unit old.2.property compared.val
    ⟨⟨old, rfl⟩, compared, ⟨floors, rfl, accurate⟩⟩⟩

/-- The fixed original family has a computed positive radius and all later canonical-origin MODEL bounds.

The programme and geometry owners precede epsilon. Each actual admitted
nonzero increment gets independent sufficient adaptive/reference/canonical/
shifted floors, and the given member/completion factories remain literal.
-/
@[expose] def OriginFamilyBounds : Prop :=
  ∀ accuracy : AccuracyRequest,
    ∃ radius : {value : AccuracyRequest // value = LocalMember.sourceQuotientRequest
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
      ((accuracy.divide 16
        (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).divide 16
          (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))},
      0 < radius.val.tolerance ∧
      ∀ (increment : Canonical) (_nonzero : increment ≠ 0)
        (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
        (given : {value : StripMember roots widths targetCurrent targetFloor targetRootStage
          observed increment admitted // value = members increment admitted}),
        Norm.Basic.normSq increment ≤ radius.val.tolerance →
        ∃ retained : StripMember roots widths targetCurrent targetFloor targetRootStage observed increment admitted,
          retained = given.val ∧
          ∃ floors : Nat × Nat × (Fin 2 → Nat) × Nat,
            LocalMember.OriginQuotientBounds retained.member adaptive.1 base accuracy
              floors.1 floors.2.2.1 floors.2.2.2

/-- A family of retained accuracy certificates supplies its original radii and later bounds.

Each certificate retains its same-member evidence and sufficient source,
canonical and shifted floors. Projection preserves those witnesses.
-/
private theorem OriginFamilyAccuracy.bounds (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (selectAccuracy : (accuracy : AccuracyRequest) → ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy)
    (selected : (accuracy : AccuracyRequest) →
      OriginFamilyAccuracy
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
        (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
        (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
        (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members base canonical
        actualStart firstStart originStart periodStart selectAccuracy accuracy) :
    OriginFamilyBounds (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) adaptive observed members base := by
  intro accuracy
  rcases selected accuracy with ⟨original, certify⟩
  refine ⟨original.val.1, original.val.1.val.positive, ?_⟩
  intro increment nonzero admitted given small
  rcases certify increment nonzero admitted given small with
    ⟨old, _compared, floors, _sameFloors, accurate⟩
  exact ⟨old.val.1.val, old.val.1.property, floors, accurate⟩

include canonical in
/-- Project the actual original-selector radius and same h-result from the operational canonical-origin selector. -/
theorem originFamily_accurate (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (selectAccuracy : (accuracy : AccuracyRequest) → ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy) :
    OriginFamilyBounds (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) adaptive observed members base := by
  exact OriginFamilyAccuracy.bounds
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members base canonical
    actualStart firstStart originStart periodStart selectAccuracy
    (fun accuracy => selectOriginFamily
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members base canonical
    actualStart firstStart originStart periodStart selectAccuracy accuracy)

end Family

namespace Reference

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}

section Head

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent))
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    {current floor rootStage : Nat} {referenceAccuracy : AccuracyRequest}
    (retained : Reference covered chain roots adaptive.1 current floor rootStage referenceAccuracy)
    (base : Fin 2 → RefinementProgram)
    (canonical : (coordinate : Fin 2) →
      Equivalent (adaptive.1.value coordinate).integral.approximation (base coordinate).approximation)

/-- The complete original family consumer followed by actual canonical-origin selections on its SAME caches.

The owned dependent tail includes the actual original selector function,
so each retained accuracy factory refers to that SAME run. All original
endpoint/interior/root witnesses and both source bundles precede the tail.
-/
@[expose] def OriginVariationConsumer (actualStart firstStart originStart : Nat)
    (periodStart : Fin 2 → Nat) (spatial : AccuracyRequest) (Result : Type u) : Type _ :=
  VariationConsumerWith
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
      (rootStage := rootStage) (referenceAccuracy := referenceAccuracy) covered chain roots adaptive retained
    actualStart firstStart originStart spatial
    (fun ranges allocation keptSource observed zero members comparisons selectAccuracy =>
      ((accuracy : AccuracyRequest) → OriginFamilyAccuracy
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := retained.1.val) (ranges := ranges.val) (allocation := allocation.val)
          (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) keptSource.val adaptive
          (fun channel => comparisons.get channel) observed zero members base canonical
          actualStart firstStart originStart periodStart selectAccuracy accuracy) →
      OriginFamilyBounds
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := retained.1.val) (ranges := ranges.val) (allocation := allocation.val)
          (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) adaptive observed members base → Result)

/-- Invoke the existing original family producer once and append the paid canonical-origin service and theorem.

The original Reference.withVariation body remains the only producer.
The same actual selector function is used at share accuracy, and the new
comparisons consume its retained h-result before any later model reading.
-/
def withOriginVariation (actualStart firstStart lastStart freshStart originStart : Nat)
    (periodStart : Fin 2 → Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : OriginVariationConsumer (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
      (rootStage := rootStage) (referenceAccuracy := referenceAccuracy)
      covered chain roots adaptive retained base canonical
      actualStart firstStart originStart periodStart spatial Result) : Result :=
  withVariation (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
      (rootStage := rootStage) (referenceAccuracy := referenceAccuracy) covered chain roots adaptive retained
    actualStart firstStart lastStart freshStart originStart spatial
    (fun ranges allocation keptSource observed zero members membersFactory endpoints queries oldSelect oldBounds
        comparisons selectAccuracy allBounds =>
      consume ranges allocation keptSource observed zero members membersFactory endpoints queries oldSelect oldBounds
        comparisons selectAccuracy allBounds
        (fun accuracy => selectOriginFamily
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := retained.1.val) (ranges := ranges.val) (allocation := allocation.val)
          (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) keptSource.val adaptive
          (fun channel => comparisons.get channel) observed zero members base canonical
          actualStart firstStart originStart periodStart selectAccuracy accuracy)
        (originFamily_accurate
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := retained.1.val) (ranges := ranges.val) (allocation := allocation.val)
          (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) keptSource.val adaptive
          (fun channel => comparisons.get channel) observed zero members base canonical
          actualStart firstStart originStart periodStart selectAccuracy))

end Head

/-- The original free-parent/full-point AtPoint transport for the dependent canonical-origin consumer.

Only the existing joint index equality moves. The whole supplied reference,
source bundle, programme operators and caches remain unchanged.
-/
@[expose] def OriginVariationConsumerAtPoint
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (retained : AtPoint covered chain roots nonempty adaptive.1 current floor rootStage accuracy)
    (base : Fin 2 → RefinementProgram)
    (canonical : (coordinate : Fin 2) →
      Equivalent (adaptive.1.value coordinate).integral.approximation (base coordinate).approximation)
    (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (spatial : AccuracyRequest) (Result : Type u) : Type _ := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : startPoint parent = point := chain.start_eq
      cases same
      exact OriginVariationConsumer
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := remaining) (root := root) (current := current) (floor := floor)
        (rootStage := rootStage) (referenceAccuracy := accuracy) covered chain roots adaptive retained base canonical
        actualStart firstStart originStart periodStart spatial Result

/-- Consume the SAME complete AtPoint reference through its original joint head/start-point transport. -/
def withOriginVariationAtPoint {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (retained : AtPoint covered chain roots nonempty adaptive.1 current floor rootStage accuracy)
    (base : Fin 2 → RefinementProgram)
    (canonical : (coordinate : Fin 2) →
      Equivalent (adaptive.1.value coordinate).integral.approximation (base coordinate).approximation)
    (actualStart firstStart lastStart freshStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (spatial : AccuracyRequest) {Result : Type u}
    (consume : OriginVariationConsumerAtPoint covered chain roots nonempty adaptive current floor rootStage accuracy
      retained base canonical actualStart firstStart originStart periodStart spatial Result) : Result := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : startPoint parent = point := chain.start_eq
      cases same
      exact withOriginVariation
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := remaining) (root := root) (current := current) (floor := floor)
        (rootStage := rootStage) (referenceAccuracy := accuracy) covered chain roots adaptive retained base canonical
        actualStart firstStart lastStart freshStart originStart periodStart spatial consume

end Reference

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk (PolynomialValues)
open Purelib.Riemann.Periods
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {ambient : Purelib.Geometry.Rational.Box}
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base))
    (period : PeriodWalk (curve := Fibre.frameCurve frame) grid base owner basis)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
    {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive period.closed.traced.lineage inputCenters materialized factory)
    (childChain : CenteredPathChain retained.parents
      (start := (⟨base, 0⟩ : LiftedPoint 2)) (finish := (⟨base, 0⟩ : LiftedPoint 2)))

namespace Geometry.Sources

variable (precision : Nat → Nat)
    (requested : (index : Nat) → { value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index) })
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    {rootStage : Nat} {walkPositive : 0 < period.closed.walk.edgeCount}
    (completed : (index : Nat) → Occurrences (count := count) (floor := floor)
      owner period.closed retained childChain (precision index) rootStage (requested index).val
        (requested index).property (sourceBanks index) walkPositive)

/-- Read the two retained original origin programmes without constructing either programme again.

The first is the supplied old ordered holomorphic programme cache. The
second is the supplied x dx/y polynomial programme on its original initial
closed path. Their separate differential and cycle owners remain unchanged.
-/
@[expose] def originPrograms {polynomialFloor : Nat} (values : PolynomialValues period polynomialFloor) :
    Fin 2 → RefinementProgram :=
  Fin.cases values.2.2.2.val.integral
    (Fin.cases values.2.2.1.2.val.integral (fun index => Fin.elim0 index))

/-- Derive both fixed-source/original-programme MODEL operators from the SAME given jet and programme caches.

The old programme's whole factory only reindexes its same-model sample
readback. No output name is sampled, and no source, member, value programme,
period bank or primitive request is rebuilt. Requested comparisons remain
future work in the returned original executable operators.
-/
def originEquivalents {polynomialFloor : Nat} (values : PolynomialValues period polynomialFloor)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (precisionPaid : ∀ index, index ≤ precision index) (actual : SynchronizedPeriodJet frame)
    (actualFactory : actual =
      jet owner period.closed retained childChain precision requested sourceBanks completed precisionPaid) :
    DependentVector (fun coordinate : Fin 2 =>
      Equivalent (actual.value coordinate).integral.approximation
        (originPrograms (owner := owner) (period := period) values coordinate).approximation) :=
  let first := (valueZero_periodEquivalent owner period retained childChain precision requested sourceBanks completed
      canonical precisionPaid actual actualFactory).withSamples
    (actual.value 0).integral.approximation values.2.2.2.val.integral.approximation
    (fun _index => rfl)
    (fun index => congrArg
      (fun value : Basis.CertifiedPeriodProgram (Fibre.frameCurve frame)
          (PeriodMatrix.standardDifferential (0 : Fin 1)) period.cycle =>
        value.integral.approximation.sample index) values.2.2.2.property)
  let second := valueOne_periodEquivalent owner period retained childChain precision requested sourceBanks completed
    values canonical precisionPaid actual actualFactory
  DependentVector.ofFn (fun coordinate : Fin 2 =>
    Fin.cases first (Fin.cases second (fun index => Fin.elim0 index)) coordinate)

/-- The actual two derived operators precede the complete retained-family canonical-origin consumer.

The subtype retains their whole factory on the original bundle and values.
The existing AtPoint reference transports the same root/point/source caches;
the dependent tail supplies the actual per-accuracy selector and full
radius/nonzero-increment/all-later quotient assertion.
-/
@[expose] def OriginConsumer {polynomialFloor : Nat} (values : PolynomialValues period polynomialFloor)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (precisionPaid : ∀ index, index ≤ precision index)
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner period.closed retained})
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet)
    (actualFactory : adaptive.1 =
      jet owner period.closed retained childChain precision requested sourceBanks completed precisionPaid)
    (referenceCurrent referenceFloor referenceRootStage : Nat) (referenceAccuracy : AccuracyRequest)
    (reference : StageAttempt.Requested.Reference.AtPoint
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
      retained.covered childChain rooted.val
      (Geometry.parents_nonempty_of_walk owner period.closed retained walkPositive)
      adaptive.1 referenceCurrent referenceFloor referenceRootStage referenceAccuracy)
    (actualStart firstStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (spatial : AccuracyRequest) (Result : Type u) : Type _ :=
  (operators : {value : DependentVector (fun coordinate : Fin 2 =>
      Equivalent (adaptive.1.value coordinate).integral.approximation
        (originPrograms (owner := owner) (period := period) values coordinate).approximation) //
    value = originEquivalents owner period retained childChain precision requested sourceBanks completed
      values canonical precisionPaid adaptive.1 actualFactory}) →
  StageAttempt.Requested.Reference.OriginVariationConsumerAtPoint
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
    retained.covered childChain rooted.val
      (Geometry.parents_nonempty_of_walk owner period.closed retained walkPositive)
    adaptive referenceCurrent referenceFloor referenceRootStage referenceAccuracy reference
    (originPrograms (owner := owner) (period := period) values) (fun coordinate => operators.val.get coordinate)
    actualStart firstStart originStart periodStart spatial Result

/-- Build canonical-origin finite quotient evidence from the SAME original geometry, bundle, values and family.

Both operators are derived once before the original family producer runs
once. The whole reference, observations, zero/member rule, all-time geometry
and old selector remain those actual retained values. Each epsilon and h
executes its genuine numerical selection and two increment-paid canonical
comparisons. No final closeness, Frame identity or canonical derivative
programme is supplied by the caller.
-/
def withOriginVariation {polynomialFloor : Nat} (values : PolynomialValues period polynomialFloor)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage)
    (precisionPaid : ∀ index, index ≤ precision index)
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner period.closed retained})
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet)
    (actualFactory : adaptive.1 =
      jet owner period.closed retained childChain precision requested sourceBanks completed precisionPaid)
    (referenceCurrent referenceFloor referenceRootStage : Nat) (referenceAccuracy : AccuracyRequest)
    (reference : StageAttempt.Requested.Reference.AtPoint
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
      retained.covered childChain rooted.val
      (Geometry.parents_nonempty_of_walk owner period.closed retained walkPositive)
      adaptive.1 referenceCurrent referenceFloor referenceRootStage referenceAccuracy)
    (actualStart firstStart lastStart freshStart originStart : Nat) (periodStart : Fin 2 → Nat)
    (spatial : AccuracyRequest) {Result : Type u}
    (consume : OriginConsumer owner period retained childChain precision requested sourceBanks completed
      values canonical precisionPaid rooted adaptive actualFactory referenceCurrent referenceFloor referenceRootStage
      referenceAccuracy reference actualStart firstStart originStart periodStart spatial Result) : Result :=
  let operators := originEquivalents owner period retained childChain precision requested sourceBanks completed
    values canonical precisionPaid adaptive.1 actualFactory
  StageAttempt.Requested.Reference.withOriginVariationAtPoint
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
    retained.covered childChain rooted.val
      (Geometry.parents_nonempty_of_walk owner period.closed retained walkPositive)
    adaptive referenceCurrent referenceFloor referenceRootStage referenceAccuracy reference
    (originPrograms (owner := owner) (period := period) values) (fun coordinate => operators.get coordinate)
    actualStart firstStart lastStart freshStart originStart periodStart spatial (consume ⟨operators, rfl⟩)

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
