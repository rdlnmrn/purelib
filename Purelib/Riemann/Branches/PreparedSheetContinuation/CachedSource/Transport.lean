module

public import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Observation
public import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual cached root advancement compared with a paid moving channel

The original cached prepared source, retained source reading and retained
target state pay a signed sum floor on the actual reserved transport. Its
square certificate then compares that genuine target Owner with the moving
channel. Original reserve-retention comparison transfers the result to the
actual advanceCached endpoint, retaining the source reconditioning step.

The quantitative payment is separate evidence about the actual preparation
diameter, observation radii and channel movement. This module does not assert
that every existing covered subdivision already pays that certificate.
-/

public section

namespace Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {current : Endpoint}
variable {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} {request : StepRequest}

/-- The exact scalar budget for a retained source-reading comparison, preparation diameter and target movement. -/
@[expose] def advancePayment {sourceChannel : CoherentNamed}
    (sourceReading : Equivalence.Observation.Reading sourceChannel)
    {sourceParameter : Canonical} {root : CertifiedSquareRoot.Certificate sourceParameter}
    (preparedReading : Equivalence.Observation.Reading root.value)
    (comparisonTarget diameter movement : Fraction.Rational) : Fraction.Rational :=
  4 * (16 * (sourceReading.radius + preparedReading.radius) + 4 * comparisonTarget) +
    4 * diameter + 2 * movement

/-- The two paid source discrepancies and actual target movement preserve the original source norm as a sum floor. -/
theorem sum_lower {source prepared target candidate : Canonical}
    {floor comparisonBound diameter movement : Fraction.Rational}
    (sourceLower : floor ≤ Norm.Basic.normSq source)
    (sourceClose : Norm.Basic.normSq (source - prepared) ≤ comparisonBound)
    (candidateClose : Norm.Basic.normSq (candidate - prepared) ≤ diameter)
    (targetClose : Norm.Basic.normSq (source - target) ≤ movement)
    (paid : 4 * comparisonBound + 4 * diameter + 2 * movement ≤ floor) :
    floor ≤ Norm.Basic.normSq (candidate + target) := by
  have candidateSource := Norm.Bounds.normSq_sub_le_via candidate prepared source
  rewrite [Norm.Bounds.normSq_sub_symm prepared source] at candidateSource
  have candidateBound : Norm.Basic.normSq (candidate - source) ≤ 2 * (diameter + comparisonBound) :=
    candidateSource.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct candidateClose sourceClose) (by decide +kernel))
  have difference : (source + source) - (candidate + target) =
      (source - candidate) + (source - target) := by ring1
  have close : Norm.Basic.normSq ((source + source) - (candidate + target)) ≤
      Norm.Basic.normSq (source + source) / 4 := by
    rewrite [difference, Norm.Basic.normSq_double]
    have total := Norm.Bounds.normSq_add_le_two (source - candidate) (source - target)
    rewrite [Norm.Bounds.normSq_sub_symm source candidate] at total
    have upper := total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct candidateBound targetClose) (by decide +kernel))
    have scalar : 2 * (2 * (diameter + comparisonBound) + movement) =
        4 * comparisonBound + 4 * diameter + 2 * movement := by ring1
    have quotient : (4 * Norm.Basic.normSq source) / 4 = Norm.Basic.normSq source := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = Norm.Basic.normSq source * ((4 : Fraction.Rational) * (4 : Fraction.Rational)⁻¹) := by ring1
        _ = _ := by
          rewrite [Fraction.Field.mul_inv_cancel _ (by decide +kernel), Fraction.Field.mul_one_direct]
          rfl
    rewrite [quotient]
    exact (upper.trans_eq scalar).trans (paid.trans sourceLower)
  have lower := Norm.Bounds.quarter_normSq_le_of_close (source + source) (candidate + target) close
  rewrite [Norm.Basic.normSq_double] at lower
  have quotient : (4 * Norm.Basic.normSq source) / 4 = Norm.Basic.normSq source := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = Norm.Basic.normSq source * ((4 : Fraction.Rational) * (4 : Fraction.Rational)⁻¹) := by ring1
      _ = _ := by
        rewrite [Fraction.Field.mul_inv_cancel _ (by decide +kernel), Fraction.Field.mul_one_direct]
        rfl
  rewrite [quotient] at lower
  exact sourceLower.trans lower

/-- The complete original source comparison cache and the derived operational target agreement for an actual advance.

The exact comparison factory retains both actual observations and the
original composed source relation. The endpoint relation refers to the
original advanceCached result; no common target Owner replaces either input.
-/
@[expose] def AdvanceAgreement (cached : CachedSource segment current owner request)
    (within : segment.WithinAmbient)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceChannel targetChannel : CoherentNamed)
    (sourceReading : Equivalence.Observation.Reading sourceChannel)
    (targetReading : Equivalence.Observation.Reading targetChannel)
    (sourceAgreement : NamedEquivalent sourceChannel.name (owner.certificate owner.parameterNonzero).value.name)
    (root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (preparedReading : Equivalence.Observation.Reading root.value)
    (comparisonTarget : Fraction.Rational) (comparisonPositive : 0 < comparisonTarget) :=
  Σ _targetBased : { retained : CoherentNamed // retained = targetChannel.based targetReading.state },
    { compared : Equivalence.Observation.Comparison sourceReading preparedReading comparisonTarget //
        compared = Equivalence.Observation.Comparison.build sourceReading preparedReading
          (cached.channelEquivalent root root_eq sourceChannel sourceAgreement) comparisonTarget comparisonPositive } ×
      NamedEquivalent
      ((advanceCached segment within current owner request cached small).certificate
        (advanceCached segment within current owner request cached small).parameterNonzero).value.name
      targetChannel.name

/-- Derive agreement of the actual cached advance endpoint with a moving target channel from paid original observations.

Source agreement is at the original current Owner, before preparation. The
existing source reconditioning comparison is composed internally. Both
observations remain actual original states; target samples use the finite
refinement future of that same retained target state. The preparation's
diameter and independently proved movement pay the sum floor, so no target
equivalence or common target owner is among the inputs.
-/
def advanceAgreement (cached : CachedSource segment current owner request)
    (within : segment.WithinAmbient)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (sourceChannel targetChannel : CoherentNamed)
    (sourceReading : Equivalence.Observation.Reading sourceChannel)
    (targetReading : Equivalence.Observation.Reading targetChannel)
    (sourceAgreement : NamedEquivalent sourceChannel.name (owner.certificate owner.parameterNonzero).value.name)
    (root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (preparedReading : Equivalence.Observation.Reading root.value)
    (targetSquare : SquareRootProvenance.SquareIdentity targetChannel
      (polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (floor : Fraction.Rational) (positive : 0 < floor)
    (sourceLower : floor ≤ Norm.Basic.normSq sourceReading.value)
    (movement comparisonTarget : Fraction.Rational) (comparisonPositive : 0 < comparisonTarget)
    (targetMovement : ∀ {candidate : Canonical}, targetChannel.name.process.Possible targetReading.state candidate →
      Norm.Basic.normSq (sourceReading.value - candidate) ≤ movement)
    (payment : advancePayment sourceReading preparedReading comparisonTarget
      cached.preparedOwner.track.initial.box.diagonalSq movement ≤ floor) :
    AdvanceAgreement cached within small sourceChannel targetChannel sourceReading targetReading sourceAgreement
      root root_eq preparedReading comparisonTarget comparisonPositive := by
  let compared := Equivalence.Observation.Comparison.build sourceReading preparedReading
    (cached.channelEquivalent root root_eq sourceChannel sourceAgreement) comparisonTarget comparisonPositive
  have sourceClose := compared.residual_le
  rewrite [compared.residual_eq, compared.bound_eq] at sourceClose
  have preparedInside := CertifiedSquareRoot.Sampling.candidate_in_initial_box cached.preparedOwner
    root_eq preparedReading.possible
  let nonzero := segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside
  let pointSmall := (ClearSheetContinuation.evaluation_variation_le segment within
    current.parameter request.endpoint.parameter current.inside request.endpoint.inside).trans_lt small
  let transported := reservedTransport cached.preparedOwner nonzero pointSmall
    (transportReserve segment current request)
  let transportedRoot := transported.certificate transported.parameterNonzero
  let targetBased := targetChannel.based targetReading.state
  have targetEquivalent := targetChannel.basedEquivalent targetReading.state
  have basedSquare : SquareRootProvenance.SquareIdentity targetBased
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects targetBased targetChannel
      targetBased targetChannel targetEquivalent.symm targetEquivalent.symm).trans targetSquare
  have sumLower : ∀ leftIndex rightIndex,
      floor ≤ Canonical.normSq ((Name.Sampling.approximation transportedRoot.value.name).sample leftIndex +
        (Name.Sampling.approximation targetBased.name).sample rightIndex) := by
    intro leftIndex rightIndex
    have firstPossible := Process.Sampling.witnessAt_possible transportedRoot.value.name.process
      transportedRoot.value.name.state leftIndex
    have firstInside := transported.certificate_candidate_in_initial_box transported.parameterNonzero _ firstPossible
    have nested := reservedTransport_initial_box_refines cached.preparedOwner nonzero pointSmall
      (transportReserve segment current request)
    have commonInside := nested.contains firstInside
    have distance := cached.preparedOwner.track.initial.box.normSq_sub_le_diagonalSq commonInside preparedInside
    have lastPossible := Process.Based.based_initial_persists targetChannel.name.process targetReading.state
      (Process.Sampling.witnessAt_possible targetBased.name.process targetBased.name.state rightIndex)
    have floorLower := sum_lower sourceLower sourceClose distance
      (targetMovement lastPossible) payment
    rewrite [Norm.Basic.normSq_eq_canonical] at floorLower
    exact floorLower
  let transportedEquivalent := SquareRootProvenance.equivalent_of_sum_lower
    transportedRoot.square basedSquare floor positive sumLower
  have resetEquivalent := retainedAtReserveRootEquivalent transported (preparedClearanceLower segment current request)
  exact ⟨⟨targetBased, rfl⟩, ⟨compared, rfl⟩,
    resetEquivalent.symm.trans (transportedEquivalent.trans targetEquivalent.symm)⟩

namespace AdvanceAgreement

variable {cached : CachedSource segment current owner request} {within : segment.WithinAmbient}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  cached.preparedOwner.track.initial.clearance.bound}
variable {sourceChannel targetChannel : CoherentNamed}
variable {sourceReading : Equivalence.Observation.Reading sourceChannel}
variable {targetReading : Equivalence.Observation.Reading targetChannel}
variable {sourceAgreement : NamedEquivalent sourceChannel.name (owner.certificate owner.parameterNonzero).value.name}
variable {root : CertifiedSquareRoot.Certificate (polynomial.eval (segment.pointAt current.parameter))}
variable {root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero}
variable {preparedReading : Equivalence.Observation.Reading root.value}
variable {comparisonTarget : Fraction.Rational} {comparisonPositive : 0 < comparisonTarget}

/-- Read the entire original finite refinement-future cache on the identical retained target state. -/
@[expose] def targetBased (result : AdvanceAgreement cached within small sourceChannel targetChannel
    sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive) :=
  result.1.val

/-- The retained target future is the original complete factory on the same original target state. -/
theorem targetBased_eq (result : AdvanceAgreement cached within small sourceChannel targetChannel
    sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive) :
    result.targetBased = targetChannel.based targetReading.state := result.1.property

/-- Read the actual complete original source/prepared observation comparison and its chosen finite evidence. -/
@[expose] def comparison (result : AdvanceAgreement cached within small sourceChannel targetChannel
    sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive) :=
  result.2.1.val

/-- The original source comparison is the exact completed factory on those same observations and source relation. -/
theorem comparison_eq (result : AdvanceAgreement cached within small sourceChannel targetChannel
    sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive) :
    result.comparison = Equivalence.Observation.Comparison.build sourceReading preparedReading
      (cached.channelEquivalent root root_eq sourceChannel sourceAgreement) comparisonTarget comparisonPositive :=
  result.2.1.property

/-- Read the derived endpoint relation, retaining the original cached advance Owner and independent target channel. -/
@[expose] def equivalent (result : AdvanceAgreement cached within small sourceChannel targetChannel
    sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive) :
    NamedEquivalent
      ((advanceCached segment within current owner request cached small).certificate
        (advanceCached segment within current owner request cached small).parameterNonzero).value.name
      targetChannel.name := result.2.2

/-- Transport the retained cached-advance relation to the exact original canonical advancement Owner.

The original cached/canonical Owner equality changes only the endpoint name.
The supplied complete comparison and independent target channel remain the
same inputs; no comparison, observation or advancement factory is rerun.
-/
def canonicalEquivalent
    (result : AdvanceAgreement cached within small sourceChannel targetChannel
      sourceReading targetReading sourceAgreement root root_eq preparedReading comparisonTarget comparisonPositive)
    (canonicalSmall : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound) :
    NamedEquivalent
      ((advance segment within current owner request canonicalSmall).certificate
        (advance segment within current owner request canonicalSmall).parameterNonzero).value.name
      targetChannel.name := by
  have names := congrArg
    (fun next : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)) =>
      (next.certificate next.parameterNonzero).value.name)
    (advanceCached_eq_advance segment within current owner request cached small canonicalSmall)
  exact NamedEquivalent.transport names rfl result.equivalent

end AdvanceAgreement

end Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource
