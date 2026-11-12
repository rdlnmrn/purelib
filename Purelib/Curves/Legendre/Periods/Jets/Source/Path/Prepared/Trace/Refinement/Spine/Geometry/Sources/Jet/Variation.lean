module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Jet.Reference
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Variation
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic

import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Adaptive source derivatives on the same actual transported child-cycle family

The fixed adaptive bundle and retained original reference precede the
intrinsic range, strip allocation and actual shared-observation family.
The original family producer runs once. Its same members, endpoint/query
transport and whole source factories support every epsilon, every admitted
nonzero increment and all later actual model readings.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order.Arithmetic (instZeroLEOneClass)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

section Compared

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
    (completed : source.attempt.OccurrenceFamily)
    (sourceActual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (sourceFactory : sourceActual = OccurrenceCompletion.build (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun index => (completed index).val))
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

/-- The actual given h-member and original paid six-channel quotient result, without a new acquisition.

The member equality keeps the given whole cache. The subtype contains its
existing complete comparison/quotient run and the derived all-later stage
bound; it introduces no alternate derivative or source owner.
-/
@[expose] def ComparedMemberAccuracy (actualStart firstStart originStart : Nat)
    (accuracy : AccuracyRequest) (increment : Canonical) (nonzero : increment ≠ 0)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (given : {value : StripMember roots widths targetCurrent targetFloor targetRootStage observed increment admitted //
      value = members increment admitted}) : Type _ :=
  (retained : {value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed increment admitted // value = given.val}) ×
    {paid : LocalMember.ComparedSourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (increment := increment) (zeroAdmitted := zeroPaid) (admitted := admitted)
      sourceActual.1 zero.member retained.val.member adaptive.1 equivalent accuracy nonzero
      actualStart firstStart originStart //
      LocalMember.StageQuotientBounds retained.val.member adaptive.1 accuracy paid.2.2.val.1 paid.2.2.val.2.2}

/-- One actual adaptive-source accuracy selection on the fixed original member rule.

The radius is computed before h. Each given h-member is returned unchanged
beside its original six model comparisons, independent source/reference/
shifted floors and stage-model bound. New requested work remains explicit.
-/
@[expose] def ComparedFamilyAccuracy (actualStart firstStart originStart : Nat)
    (accuracy : AccuracyRequest) : Type _ :=
  (radius : {value : AccuracyRequest // value = LocalMember.sourceQuotientRequest
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
      (accuracy.divide 16 (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))}) ×
  ((increment : Canonical) → (nonzero : increment ≠ 0) →
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound) →
    (given : {value : StripMember roots widths targetCurrent targetFloor targetRootStage
      observed increment admitted // value = members increment admitted}) →
    (_small : Norm.Basic.normSq increment ≤ radius.val.tolerance) →
      ComparedMemberAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy increment nonzero admitted given)

include completed sourceFactory in
/-- Select all four adaptive-source quotient bounds using the SAME supplied reference and actual member caches.

The given member and six fixed comparison operators are consumed directly.
The original quotient run pays its fresh numerical requests; only scalar
model readbacks transfer its derived bound to each later given stage cache.
-/
def selectComparedFamily (actualStart firstStart lastStart freshStart originStart : Nat)
    (spatial accuracy : AccuracyRequest) : ComparedFamilyAccuracy
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceActual adaptive equivalent observed zero members
      actualStart firstStart originStart accuracy :=
  let radius : AccuracyRequest := LocalMember.sourceQuotientRequest
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
      (accuracy.divide 16 (by decide +kernel))
  ⟨⟨radius, rfl⟩, fun increment nonzero admitted given small =>
    let retained := given.val
    have jetFactory : sourceActual.1 = OccurrenceCompletion.jet
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (floor := floor) (rootStage := rootStage) covered chain (fun index => (completed index).val) :=
      (congrArg (fun value : (jet : SynchronizedPeriodJet frame) ×
        Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet => value.1)
        sourceFactory).trans (OccurrenceCompletion.build_jet (parameter := parameter) (frame := frame)
          (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
          covered chain (fun index => (completed index).val))
    let paid := LocalMember.sourceQuotientFloorsWithSource
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (increment := increment) (zeroAdmitted := zeroPaid) (admitted := admitted)
      completed sourceActual.1 jetFactory zero.member retained.member adaptive.1 equivalent accuracy nonzero small
      actualStart firstStart lastStart freshStart originStart spatial
    have staged := LocalMember.stageQuotient_of_source
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (offset := increment) (admitted := admitted)
      retained.member adaptive.1 accuracy paid.2.2.val.1 paid.2.2.val.2.2 paid.2.2.property.2
    ⟨⟨retained, rfl⟩, ⟨paid, staged⟩⟩⟩

include completed sourceFactory zero equivalent in
/-- The fixed adaptive source and actual transported member family satisfy the full finite derivative quantifiers.

For every positive requested error one executable positive quadrance radius
works for every admitted nonzero h. Its finite model floors may depend on
h, and every later source/shifted pair and given whole stage cache is paid.
-/
theorem comparedFamily_accurate (actualStart firstStart lastStart freshStart originStart : Nat)
    (spatial : AccuracyRequest) : FamilyBoundsWith
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (sourceActual := adaptive)
      (observed := observed) (members := members)
      (fun accuracy => LocalMember.sourceQuotientRequest
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (ranges := ranges) (allocation := allocation)
      (accuracy.divide 16 (by decide +kernel))) := by
  intro accuracy
  let selected := selectComparedFamily
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage)
      completed sourceActual sourceFactory adaptive equivalent observed zero members
    actualStart firstStart lastStart freshStart originStart spatial accuracy
  refine ⟨selected.1, selected.1.val.positive, ?_⟩
  intro increment nonzero admitted given small
  let actual := selected.2 increment nonzero admitted given small
  exact ⟨actual.1.val, actual.1.property, actual.2.val.2.2.val.1,
    actual.2.val.2.2.val.2.2, actual.2.property⟩

end Compared

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

/-- The exact actual range/family/comparison/selector values indexing a dependent continuation.

The original scalar factories and four family caches remain unchanged.
The six retained comparison operators and existing selector function are
also inputs, so a dependent result can retain their actual factory run
without reconstructing a function or asserting function equality.
-/
@[expose] def VariationTail (actualStart firstStart originStart : Nat) (spatial : AccuracyRequest) : Type _ :=
  let source := retained.1.val
  let sourceActual := retained.2.2.2.1.val
  (ranges : {value : ParameterRange covered // value = ParameterRange.build
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) covered}) →
  (allocation : {value : ParameterRange.StripAllocation ranges.val //
    value = ParameterRange.StripAllocation.build ranges.val}) →
  (keptSource : { value : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
    value = sourceActual }) →
  (observed : EndpointObservations source.prepared
      ⟨Fraction.Order.Basic.le_refl 0, instZeroLEOneClass.zero_le_one⟩
      ⟨instZeroLEOneClass.zero_le_one, Fraction.Order.Basic.le_refl 1⟩) →
  let zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.val.bound :=
    (Norm.Basic.normSq_zero).trans_le allocation.val.bound_positive.le
  (zero : StripMember roots (fun _ => spatial) current floor rootStage observed 0 zeroPaid) →
  (members : (offset : Canonical) → (admitted : Norm.Basic.normSq offset ≤ allocation.val.bound) →
    StripMember roots (fun _ => spatial) current floor rootStage observed offset admitted) →
  (comparisons : DependentVector (fun channel : Fin 6 =>
    Equivalent (adaptive.1.programme channel).approximation (keptSource.val.1.programme channel).approximation)) →
  ((accuracy : AccuracyRequest) → ComparedFamilyAccuracy
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
    (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
    (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor) (targetRootStage := rootStage)
    keptSource.val adaptive (fun channel => comparisons.get channel) observed zero members
    actualStart firstStart originStart accuracy) → Type u

/-- The unchanged complete family interface followed by a tail on its SAME retained actual data.

All original root/endpoint/query witnesses, selections and all-later bounds
precede this tail. Only its exact output type is parameterized; the old
constant-result consumer and the period-origin consumer use this same type.
-/
@[expose] def VariationConsumerWith (actualStart firstStart originStart : Nat)
    (spatial : AccuracyRequest)
    (Finish : VariationTail (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
      (rootStage := rootStage) (referenceAccuracy := referenceAccuracy) covered chain roots adaptive retained
      actualStart firstStart originStart spatial) : Type _ :=
  let source := retained.1.val
  let sourceActual := retained.2.2.2.1.val
  (ranges : {value : ParameterRange covered // value = ParameterRange.build
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) covered}) →
  (allocation : {value : ParameterRange.StripAllocation ranges.val //
    value = ParameterRange.StripAllocation.build ranges.val}) →
  FamilyConsumerWith
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
      (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
      (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
      (targetRootStage := rootStage) (sourceActual := sourceActual) (originStart := originStart)
    (fun keptSource observed zero members =>
      (comparisons : DependentVector (fun channel : Fin 6 =>
        Equivalent (adaptive.1.programme channel).approximation (keptSource.val.1.programme channel).approximation)) →
      (selectAccuracy : (accuracy : AccuracyRequest) → ComparedFamilyAccuracy
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
        (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
        (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
        (targetRootStage := rootStage) keptSource.val adaptive (fun channel => comparisons.get channel)
        observed zero members actualStart firstStart originStart accuracy) →
      FamilyBoundsWith
        (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := parents) (covered := covered) (chain := chain)
        (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
        (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
        (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
        (targetRootStage := rootStage) (sourceActual := adaptive) (observed := observed) (members := members)
        (fun accuracy => LocalMember.sourceQuotientRequest
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered)
          (ranges := ranges.val) (allocation := allocation.val) (accuracy.divide 16
            (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15)))) →
        Finish ranges allocation keptSource observed zero members comparisons selectAccuracy)

/-- The original full family interface followed by actual adaptive selections and its complete derivative theorem.

The SAME four cache values index the owned dependent tail. Original
endpoint/query transport and old paid fields stay in the shared consumer.
Both range/strip factories and the new six-operator cache are retained.
-/
@[expose] def VariationConsumer (actualStart firstStart _lastStart _freshStart originStart : Nat)
    (spatial : AccuracyRequest) (Result : Type u) : Type _ :=
  VariationConsumerWith
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
    (rootStage := rootStage) (referenceAccuracy := referenceAccuracy) covered chain roots adaptive retained
    actualStart firstStart originStart spatial
    (fun _ranges _allocation _keptSource _observed _zero _members _comparisons _selectAccuracy => Result)

/-- Build the intrinsic allocation and one original observation/member family, then derive adaptive finite derivatives.

The request, raw/cached completion rules, old bundle and all six original
comparison operators are the GIVEN reference. Only range/strip caches and
the original family producer execute. The adaptive source is unchanged;
all new tolerance-dependent work consumes those same callback caches.
-/
def withVariation (actualStart firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest)
    {Result : Type u}
    (consume : VariationConsumer (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (root := root) (current := current) (floor := floor)
      (rootStage := rootStage) (referenceAccuracy := referenceAccuracy) covered chain roots adaptive retained
      actualStart firstStart lastStart freshStart originStart spatial Result) : Result :=
  let source := retained.1.val
  let completed := retained.2.2.1.val
  let sourceActual := retained.2.2.2.1.val
  let ranges : {value : ParameterRange covered // value = ParameterRange.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) covered} :=
    ⟨ParameterRange.build (parameter := parameter) (frame := frame) (basis := basis) (count := count) covered, rfl⟩
  let allocation : {value : ParameterRange.StripAllocation ranges.val //
      value = ParameterRange.StripAllocation.build ranges.val} :=
    ⟨ParameterRange.StripAllocation.build ranges.val, rfl⟩
  Requested.withVariationFamily
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
      (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
      (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
      (targetRootStage := rootStage)
      completed sourceActual retained.2.2.2.1.property firstStart lastStart freshStart originStart spatial
    (fun keptSource observed zero members membersFactory endpoints queries oldSelect oldBounds =>
      let comparisons := DependentVector.ofFn (fun channel : Fin 6 =>
        (retained.2.2.2.2.get channel).withSamples
          (adaptive.1.programme channel).approximation (keptSource.val.1.programme channel).approximation
          (fun _index => rfl)
          (fun index => congrArg (fun value : (jet : SynchronizedPeriodJet frame) ×
            Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet =>
              (value.1.programme channel).approximation.sample index) keptSource.property))
      have keptFactory := keptSource.property.trans retained.2.2.2.1.property
      consume ranges allocation keptSource observed zero members membersFactory endpoints queries oldSelect oldBounds
        comparisons
        (fun accuracy => selectComparedFamily
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) completed keptSource.val keptFactory adaptive
          (fun channel => comparisons.get channel) observed zero members
          actualStart firstStart lastStart freshStart originStart spatial accuracy)
        (comparedFamily_accurate
          (parameter := parameter) (frame := frame) (basis := basis) (count := count)
          (parent := parent) (parents := parents) (covered := covered) (chain := chain)
          (current := current) (floor := floor) (rootStage := rootStage) (reference := referenceAccuracy)
          (source := source) (ranges := ranges.val) (allocation := allocation.val) (root := root) (roots := roots)
          (widths := fun _ => spatial) (targetCurrent := current) (targetFloor := floor)
          (targetRootStage := rootStage) completed keptSource.val keptFactory adaptive
          (fun channel => comparisons.get channel) observed zero members
          actualStart firstStart lastStart freshStart originStart spatial))

end Head

/-- The exact original-head variation consumer transported jointly over FREE parent and full-point indices. -/
@[expose] def VariationConsumerAtPoint
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (retained : AtPoint covered chain roots nonempty adaptive.1 current floor rootStage accuracy)
    (actualStart firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) (Result : Type u) :
    Type _ := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : startPoint parent = point := chain.start_eq
      cases same
      exact VariationConsumer (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := remaining) (root := root) (current := current) (floor := floor)
        (rootStage := rootStage) (referenceAccuracy := accuracy) covered chain roots adaptive retained
        actualStart firstStart lastStart freshStart originStart spatial Result

/-- Consume the GIVEN whole AtPoint reference through its actual free-parent/full-point transport.

The given request, source completion, root and jet values are transported
unchanged. The full start equality changes all dependent types together;
the head operation builds the shared family from that SAME payload.
-/
def withVariationAtPoint {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet)
    (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (retained : AtPoint covered chain roots nonempty adaptive.1 current floor rootStage accuracy)
    (actualStart firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : VariationConsumerAtPoint covered chain roots nonempty adaptive current floor rootStage accuracy
      retained actualStart firstStart lastStart freshStart originStart spatial Result) : Result := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent remaining =>
      have same : startPoint parent = point := chain.start_eq
      cases same
      exact withVariation (parameter := parameter) (frame := frame) (basis := basis) (count := count)
        (parent := parent) (parents := remaining) (root := root) (current := current) (floor := floor)
        (rootStage := rootStage) (referenceAccuracy := accuracy) covered chain roots adaptive retained
        actualStart firstStart lastStart freshStart originStart spatial consume

end Reference

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation (AccuracyRequest)
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

/-- Consume the actual retained reference on the SAME physical child cycle with its concrete transported family.

No request, occurrence completion, root chain or jet is reconstructed.
The owned free-parent/full-point eliminator transports the entire given
reference and invokes the intrinsic range/allocation/family construction.
The continuation receives its genuine geometry plus the adaptive selector
and full epsilon/h/all-later derivative assertion on the given source.
-/
def withVariation (walkPositive : 0 < closed.walk.edgeCount)
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained})
    (adaptive : (jet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate jet × PicardFuchs.PicardFuchsCertificate jet)
    (referenceCurrent referenceFloor referenceRootStage : Nat) (referenceAccuracy : AccuracyRequest)
    (reference : StageAttempt.Requested.Reference.AtPoint
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
      retained.covered childChain rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
      adaptive.1 referenceCurrent referenceFloor referenceRootStage referenceAccuracy)
    (actualStart firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) {Result : Type u}
    (consume : StageAttempt.Requested.Reference.VariationConsumerAtPoint
      (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
      retained.covered childChain rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
      adaptive referenceCurrent referenceFloor referenceRootStage referenceAccuracy reference
      actualStart firstStart lastStart freshStart originStart spatial Result) : Result :=
  StageAttempt.Requested.Reference.withVariationAtPoint
    (parameter := parameter) (frame := frame) (basis := basis) (count := count) (root := ownerName owner)
    retained.covered childChain rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
    adaptive referenceCurrent referenceFloor referenceRootStage referenceAccuracy reference
    actualStart firstStart lastStart freshStart originStart spatial consume

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
