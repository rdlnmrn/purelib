module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
public import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
public import Purelib.Approximation.Gaussian.Sequence.Preparation
public import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
public import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Separation at original cached root stages

Coefficient-derived residual requests select states from both original root
caches. A finite coordinate-gap certificate links those exact retained states
to their later samples and excludes original-channel operational equivalence.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Rational
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_neg)
open Purelib.Data.Gaussian.Field (sub_eq_neg_sub)
open Purelib.Data.Rat

set_option genInjectivity false in
/-- Two original root requests, their retained cache reads and a positive gap between their actual boxes.

Each selected index is paid by its own approximation's refiner from its own
starting stage. The state identities and diagonal bounds refer to those same
original cache reads; the gap is a certificate at precisely those two states.
-/
structure PairSeparation
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (firstStart secondStart : Nat) where
  /-- The retained squared-diagonal request for the original first root. -/
  leftTargetSq : Coordinate
  /-- The original first request is positive. -/
  leftTarget_positive : 0 < leftTargetSq
  /-- The retained squared-diagonal request for the original second root. -/
  rightTargetSq : Coordinate
  /-- The original second request is positive. -/
  rightTarget_positive : 0 < rightTargetSq
  /-- The retained first request start, following the original caller's stage. -/
  leftRequestStart : Nat
  /-- The retained first request start follows the original caller's stage. -/
  leftRequest_ge : firstStart ≤ leftRequestStart
  /-- The retained second request start, following the original caller's stage. -/
  rightRequestStart : Nat
  /-- The retained second request start follows the original caller's stage. -/
  rightRequest_ge : secondStart ≤ rightRequestStart
  /-- The actual index computed by the first original refiner. -/
  leftIndex : Nat
  /-- The actual index computed by the second original refiner. -/
  rightIndex : Nat
  /-- The first original refiner consumes this same request and start. -/
  leftIndex_eq : leftIndex = first.approximation.refineIndex leftRequestStart leftTargetSq leftTarget_positive
  /-- The second original refiner consumes this same request and start. -/
  rightIndex_eq : rightIndex = second.approximation.refineIndex rightRequestStart rightTargetSq rightTarget_positive
  /-- The first selected index follows its original starting stage. -/
  left_ge : firstStart ≤ leftIndex
  /-- The second selected index follows its original starting stage. -/
  right_ge : secondStart ≤ rightIndex
  /-- The actual retained cache read of the first selected state. -/
  leftState : WindingOneState firstPolynomial firstAmbient
  /-- The actual retained cache read of the second selected state. -/
  rightState : WindingOneState secondPolynomial secondAmbient
  /-- The first state is the original cache read at its same selected index. -/
  leftState_eq : leftState = first.stateAt leftIndex
  /-- The second state is the original cache read at its same selected index. -/
  rightState_eq : rightState = second.stateAt rightIndex
  /-- The actual first state meets its original squared-diagonal request. -/
  left_diagonal_lt : leftState.box.diagonalSq < leftTargetSq
  /-- The actual second state meets its original squared-diagonal request. -/
  right_diagonal_lt : rightState.box.diagonalSq < rightTargetSq
  /-- The computed coordinate gap belongs to these actual retained original states. -/
  separation : Box.SeparationCertificate leftState.box rightState.box

constructive_injectivity PairSeparation

namespace PairSeparation

open Purelib.Data.Rat.Fraction.Order

/-- Retain checked coordinate separation of actual original cache reads at both requested floors.

The original quarter-radius refiner is paid with each same starting radius
plus one, so it returns exactly that floor. The supplied complete states are
consumed literally; this constructor does not perform the finite separation
check or infer separation from coefficients or matching observations.
-/
@[expose] def ofStates
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (firstStart secondStart : Nat)
    (left : WindingOneState firstPolynomial firstAmbient)
    (right : WindingOneState secondPolynomial secondAmbient)
    (leftEq : left = first.stateAt firstStart) (rightEq : right = second.stateAt secondStart)
    (separated : left.box.Separated right.box) : PairSeparation first second firstStart secondStart := by
  let leftPaid := Refinement.atFloor first firstStart left leftEq
  let rightPaid := Refinement.atFloor second secondStart right rightEq
  exact
    { leftTargetSq := leftPaid.targetSq
      leftTarget_positive := leftPaid.positive
      rightTargetSq := rightPaid.targetSq
      rightTarget_positive := rightPaid.positive
      leftRequestStart := firstStart
      leftRequest_ge := Nat.le_refl _
      rightRequestStart := secondStart
      rightRequest_ge := Nat.le_refl _
      leftIndex := firstStart
      rightIndex := secondStart
      leftIndex_eq := leftPaid.maxIndex_eq
      rightIndex_eq := rightPaid.maxIndex_eq
      left_ge := Nat.le_refl _
      right_ge := Nat.le_refl _
      leftState := left
      rightState := right
      leftState_eq := leftEq
      rightState_eq := rightEq
      left_diagonal_lt := leftPaid.diagonal_lt
      right_diagonal_lt := rightPaid.diagonal_lt
      separation := Box.separationCertificate separated }

/-- The original separated-state constructor consumes the literal supplied complete left cache state. -/
theorem ofStates_leftState
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (left : WindingOneState firstPolynomial firstAmbient) (right : WindingOneState secondPolynomial secondAmbient)
    (leftEq : left = first.stateAt firstStart) (rightEq : right = second.stateAt secondStart)
    (separated : left.box.Separated right.box) :
    (ofStates first second firstStart secondStart left right leftEq rightEq separated).leftState = left := rfl

/-- The original separated-state constructor consumes the literal supplied complete right cache state. -/
theorem ofStates_rightState
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (left : WindingOneState firstPolynomial firstAmbient) (right : WindingOneState secondPolynomial secondAmbient)
    (leftEq : left = first.stateAt firstStart) (rightEq : right = second.stateAt secondStart)
    (separated : left.box.Separated right.box) :
    (ofStates first second firstStart secondStart left right leftEq rightEq separated).rightState = right := rfl

/-- Separate two original roots using their retained coefficient-derived maximum-stage payments.

Both payments keep the original coprime thresholds and sufficient refiner
stages. Their actual cached states determine the same finite coordinate gap;
this constructor performs no original root-state reads or refinement work.
-/
@[expose] def ofCoprimeWithRefinements
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (coprime : Coprime.Basic.CoprimeCertificate firstPolynomial secondPolynomial)
    (firstStart secondStart : Nat) (left : Refinement first firstStart) (right : Refinement second secondStart)
    (leftRequest : left.targetSq = Bounds.Box.Target.uniformResidualRadius
      firstPolynomial firstAmbient (Coprime.Bounds.Box.leftThreshold coprime firstAmbient) ^ 2)
    (rightRequest : right.targetSq = Bounds.Box.Target.uniformResidualRadius
      secondPolynomial secondAmbient (Coprime.Bounds.Box.rightMargin coprime firstAmbient) ^ 2)
    (leftMaximum : left.index = left.maxIndex) (rightMaximum : right.index = right.maxIndex) :
    PairSeparation first second firstStart secondStart := by
  let threshold := Coprime.Bounds.Box.leftThreshold coprime firstAmbient
  have thresholdPositive := Coprime.Bounds.Box.leftThreshold_pos coprime firstAmbient
  let margin := Coprime.Bounds.Box.rightMargin coprime firstAmbient
  have marginPositive := Coprime.Bounds.Box.rightMargin_pos coprime firstAmbient
  have leftDiagonal := left.diagonal_lt.trans_eq leftRequest
  have rightDiagonal := right.diagonal_lt.trans_eq rightRequest
  have separated : left.current.box.Separated right.current.box := by
    by_cases separated : left.current.box.Separated right.current.box
    · exact separated
    · let point := Box.overlapPoint left.current.box right.current.box
      have inside : left.current.box.Contains point ∧ right.current.box.Contains point :=
        Box.contains_overlapPoint_of_not_separated separated
      have leftSmall := Winding.Bounds.Residual.normSq_eval_lt_of_diagonal first.degreePositive left.current
        thresholdPositive leftDiagonal.le inside.1
      have lower := Coprime.Bounds.Box.rightMargin_le_of_left_small coprime firstAmbient
        (left.current.refinesAmbient.contains inside.1) leftSmall.le
      have upper := Winding.Bounds.Residual.normSq_eval_lt_of_diagonal second.degreePositive right.current
        marginPositive rightDiagonal.le inside.2
      exact (not_lt_of_ge lower upper).elim
  exact
    { leftTargetSq := left.targetSq
      leftTarget_positive := left.positive
      rightTargetSq := right.targetSq
      rightTarget_positive := right.positive
      leftRequestStart := firstStart
      leftRequest_ge := Nat.le_refl _
      rightRequestStart := secondStart
      rightRequest_ge := Nat.le_refl _
      leftIndex := left.index
      rightIndex := right.index
      leftIndex_eq := leftMaximum.trans left.maxIndex_eq
      rightIndex_eq := rightMaximum.trans right.maxIndex_eq
      left_ge := left.index_ge
      right_ge := right.index_ge
      leftState := left.current
      rightState := right.current
      leftState_eq := left.current_eq
      rightState_eq := right.current_eq
      left_diagonal_lt := left.diagonal_lt
      right_diagonal_lt := right.diagonal_lt
      separation := Box.separationCertificate separated }

/-- Compute finite separation of two original cached root channels from their coprime defining polynomials.

The retained Bézout coefficients determine a left residual threshold and a
positive right margin. Each root's own refiner pays the corresponding uniform
residual request; overlap of the actual retained boxes contradicts those two
scalar bounds. No caller-supplied gap or successful search is required.
-/
@[expose] def ofCoprime
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (coprime : Coprime.Basic.CoprimeCertificate firstPolynomial secondPolynomial)
    (firstStart secondStart : Nat) : PairSeparation first second firstStart secondStart := by
  let threshold := Coprime.Bounds.Box.leftThreshold coprime firstAmbient
  have thresholdPositive := Coprime.Bounds.Box.leftThreshold_pos coprime firstAmbient
  let margin := Coprime.Bounds.Box.rightMargin coprime firstAmbient
  have marginPositive := Coprime.Bounds.Box.rightMargin_pos coprime firstAmbient
  let leftRadius := Bounds.Box.Target.uniformResidualRadius firstPolynomial firstAmbient threshold
  let rightRadius := Bounds.Box.Target.uniformResidualRadius secondPolynomial secondAmbient margin
  let leftTarget := leftRadius ^ 2
  let rightTarget := rightRadius ^ 2
  have leftPositive : 0 < leftTarget := Arithmetic.pow_pos_direct
    (Bounds.Box.Target.uniformResidualRadius_pos firstPolynomial firstAmbient thresholdPositive) 2
  have rightPositive : 0 < rightTarget := Arithmetic.pow_pos_direct
    (Bounds.Box.Target.uniformResidualRadius_pos secondPolynomial secondAmbient marginPositive) 2
  let leftIndex := first.approximation.refineIndex firstStart leftTarget leftPositive
  let rightIndex := second.approximation.refineIndex secondStart rightTarget rightPositive
  let leftState := first.stateAt leftIndex
  let rightState := second.stateAt rightIndex
  have leftDiagonal := first.stateAt_refineIndex_diagonal_lt firstStart leftTarget leftPositive
  have rightDiagonal := second.stateAt_refineIndex_diagonal_lt secondStart rightTarget rightPositive
  exact ofCoprimeWithRefinements first second coprime firstStart secondStart
    (Refinement.atState first firstStart leftTarget leftPositive leftIndex rfl leftIndex
      (first.approximation.refineIndex_ge firstStart leftTarget leftPositive) (Nat.le_refl leftIndex)
      leftState rfl leftDiagonal)
    (Refinement.atState second secondStart rightTarget rightPositive rightIndex rfl rightIndex
      (second.approximation.refineIndex_ge secondStart rightTarget rightPositive) (Nat.le_refl rightIndex)
      rightState rfl rightDiagonal)
    rfl rfl rfl rfl

/-- Retained exact requests and maximum-stage payments preserve the complete original coprime separation.

The two original roots, starts, targets, selected stages, cached states and
coordinate-gap certificate all agree with the default constructor.
-/
theorem ofCoprimeWithRefinements_eq
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (coprime : Coprime.Basic.CoprimeCertificate firstPolynomial secondPolynomial)
    (firstStart secondStart : Nat) (left : Refinement first firstStart) (right : Refinement second secondStart)
    (leftRequest : left.targetSq = Bounds.Box.Target.uniformResidualRadius
      firstPolynomial firstAmbient (Coprime.Bounds.Box.leftThreshold coprime firstAmbient) ^ 2)
    (rightRequest : right.targetSq = Bounds.Box.Target.uniformResidualRadius
      secondPolynomial secondAmbient (Coprime.Bounds.Box.rightMargin coprime firstAmbient) ^ 2)
    (leftMaximum : left.index = left.maxIndex) (rightMaximum : right.index = right.maxIndex) :
    ofCoprimeWithRefinements first second coprime firstStart secondStart left right leftRequest rightRequest
      leftMaximum rightMaximum = ofCoprime first second coprime firstStart secondStart := by
  rcases left with ⟨leftTarget, leftPositive, leftIndex, leftMax, leftMaxEq, leftLe, leftGe,
    leftState, leftStateEq, leftDiagonal⟩
  rcases right with ⟨rightTarget, rightPositive, rightIndex, rightMax, rightMaxEq, rightLe, rightGe,
    rightState, rightStateEq, rightDiagonal⟩
  dsimp only [] at leftRequest rightRequest leftMaximum rightMaximum
  cases leftRequest
  cases rightRequest
  cases leftMaxEq
  cases rightMaxEq
  cases leftMaximum
  cases rightMaximum
  cases leftStateEq
  cases rightStateEq
  rfl

/-- Restore the complete original coprime-root separation from both actual maximum-stage cache reads.

The same ordered Bézout certificate computes the original two requests and
sufficient stages. Left and right readers run once in that order, consuming
their original states; a failed left read never invokes the right reader.
-/
def ofCoprimeWithStates {m : Type → Type} [Monad m]
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (coprime : Coprime.Basic.CoprimeCertificate firstPolynomial secondPolynomial) (firstStart secondStart : Nat)
    (firstStates : (index : Nat) →
      m {current : WindingOneState firstPolynomial firstAmbient // current = first.stateAt index})
    (secondStates : (index : Nat) →
      m {current : WindingOneState secondPolynomial secondAmbient // current = second.stateAt index}) :
    m {certificate : PairSeparation first second firstStart secondStart //
      certificate = ofCoprime first second coprime firstStart secondStart} := do
  let threshold := Coprime.Bounds.Box.leftThreshold coprime firstAmbient
  have thresholdPositive := Coprime.Bounds.Box.leftThreshold_pos coprime firstAmbient
  let margin := Coprime.Bounds.Box.rightMargin coprime firstAmbient
  have marginPositive := Coprime.Bounds.Box.rightMargin_pos coprime firstAmbient
  let leftRadius := Bounds.Box.Target.uniformResidualRadius firstPolynomial firstAmbient threshold
  let rightRadius := Bounds.Box.Target.uniformResidualRadius secondPolynomial secondAmbient margin
  let leftTarget := leftRadius ^ 2
  let rightTarget := rightRadius ^ 2
  have leftPositive := Arithmetic.pow_pos_direct
    (Bounds.Box.Target.uniformResidualRadius_pos firstPolynomial firstAmbient thresholdPositive) 2
  have rightPositive := Arithmetic.pow_pos_direct
    (Bounds.Box.Target.uniformResidualRadius_pos secondPolynomial secondAmbient marginPositive) 2
  let leftIndex := first.approximation.refineIndex firstStart leftTarget leftPositive
  let rightIndex := second.approximation.refineIndex secondStart rightTarget rightPositive
  let left ← firstStates leftIndex
  let right ← secondStates rightIndex
  have leftAccurate : left.val.box.diagonalSq < leftTarget := by
    rewrite [left.property]
    exact first.stateAt_refineIndex_diagonal_lt firstStart leftTarget leftPositive
  have rightAccurate : right.val.box.diagonalSq < rightTarget := by
    rewrite [right.property]
    exact second.stateAt_refineIndex_diagonal_lt secondStart rightTarget rightPositive
  let leftPaid := Refinement.atState first firstStart leftTarget leftPositive leftIndex rfl leftIndex
    (first.approximation.refineIndex_ge firstStart leftTarget leftPositive) (Nat.le_refl leftIndex)
    left.val left.property leftAccurate
  let rightPaid := Refinement.atState second secondStart rightTarget rightPositive rightIndex rfl rightIndex
    (second.approximation.refineIndex_ge secondStart rightTarget rightPositive) (Nat.le_refl rightIndex)
    right.val right.property rightAccurate
  return ⟨ofCoprimeWithRefinements first second coprime firstStart secondStart
      leftPaid rightPaid rfl rfl rfl rfl,
    ofCoprimeWithRefinements_eq first second coprime firstStart secondStart
      leftPaid rightPaid rfl rfl rfl rfl⟩

/-- Every pair of later original samples retains the computed squared coordinate-gap bound. -/
theorem samples_lower
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack} {firstStart secondStart : Nat}
    (certificate : PairSeparation first second firstStart secondStart)
    {firstLater secondLater : Nat} (firstOrder : certificate.leftIndex ≤ firstLater)
    (secondOrder : certificate.rightIndex ≤ secondLater) :
    certificate.separation.gap ^ 2 ≤
      normSq (first.approximation.sample firstLater - second.approximation.sample secondLater) := by
  have leftRefines := state_refines_of_le firstTrack firstOrder
  have rightRefines := state_refines_of_le secondTrack secondOrder
  rewrite [← first.stateAt_eq firstLater, ← first.stateAt_eq certificate.leftIndex,
    ← certificate.leftState_eq] at leftRefines
  rewrite [← second.stateAt_eq secondLater, ← second.stateAt_eq certificate.rightIndex,
    ← certificate.rightState_eq] at rightRefines
  have leftInside := leftRefines.contains (first.stateAt firstLater).box.contains_anchor
  have rightInside := rightRefines.contains (second.stateAt secondLater).box.contains_anchor
  rewrite [first.sample_stateAt firstLater, second.sample_stateAt secondLater]
  exact certificate.separation.lower leftInside rightInside

/-- Retain this same original root-pair separation inside an original indexed candidate family.

The two readback identities preserve both original approximation programs.
The field reads the same certified starts and squared gap, with no new root
construction, refinement or coprime producer invocation.
-/
@[expose] def toPairBound
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack} {firstStart secondStart : Nat}
    (certificate : PairSeparation first second firstStart secondStart)
    {count : Nat} (candidates : Fin count → Sequence.ApproximationData) (left right : Fin count)
    (left_eq : candidates left = first.approximation) (right_eq : candidates right = second.approximation) :
    Sequence.Selection.PairBound candidates left right :=
  { leftIndex := certificate.leftIndex
    rightIndex := certificate.rightIndex
    gap := certificate.separation.gap ^ 2
    positive := Arithmetic.pow_pos_direct certificate.separation.positive 2
    lower := by
      intro different leftLater rightLater leftOrder rightOrder
      rewrite [left_eq, right_eq]
      exact certificate.samples_lower leftOrder rightOrder }

/-- The computed positive gap excludes operational equivalence between the two original coherent root channels. -/
theorem rejects
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack} {firstStart secondStart : Nat}
    (certificate : PairSeparation first second firstStart secondStart) :
    (Equivalence.NamedEquivalent first.value.name second.value.name → False) := by
  intro equivalent
  let comparison := (first.approximation_equivalent second equivalent).compare
    certificate.leftIndex certificate.rightIndex (certificate.separation.gap ^ 2)
    (Arithmetic.pow_pos_direct certificate.separation.positive 2)
  have lower := certificate.samples_lower comparison.left_ge comparison.right_ge
  have upper := comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  exact not_lt_of_ge lower upper

/-- Prepare the original ordered root difference using the same retained gap and original sample stages. -/
@[expose] def prepareSubtraction
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack} {firstStart secondStart : Nat}
    (certificate : PairSeparation first second firstStart secondStart) :
    Division.Prepared (CoherentNamed.add first.value (CoherentNamed.neg second.value)) := by
  rewrite [first.value_approximation, second.value_approximation]
  exact first.approximation.prepareSubtraction second.approximation certificate.leftIndex certificate.rightIndex
    (certificate.separation.gap ^ 2) (Arithmetic.pow_pos_direct certificate.separation.positive 2)
    (fun _ _ firstOrder secondOrder => certificate.samples_lower firstOrder secondOrder)

/-- Prepare the reversed original root difference from the same retained pair gap and paid sample stages.

The original second channel is the left subtraction operand. Both original
root caches, paid requests, stages and positive squared gap are reused; only
squared-distance symmetry reverses the existing sample bound.
-/
@[expose] def prepareDifference
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack} {firstStart secondStart : Nat}
    (certificate : PairSeparation first second firstStart secondStart) :
    Division.Prepared (CoherentNamed.add second.value (CoherentNamed.neg first.value)) := by
  rewrite [first.value_approximation, second.value_approximation]
  exact second.approximation.prepareSubtraction first.approximation certificate.rightIndex certificate.leftIndex
    (certificate.separation.gap ^ 2) (Arithmetic.pow_pos_direct certificate.separation.positive 2)
    (by
      intro secondLater firstLater secondOrder firstOrder
      have lower := certificate.samples_lower firstOrder secondOrder
      exact lower.trans_eq ((congrArg normSq (sub_eq_neg_sub
        (first.approximation.sample firstLater) (second.approximation.sample secondLater))).trans (normSq_neg _)))

end PairSeparation

end Purelib.Riemann.RootContinuation.CoherentRoot

end
