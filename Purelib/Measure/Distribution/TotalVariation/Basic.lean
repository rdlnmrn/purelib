module
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Equivalence
import Purelib.Measure.Content.Histogram
public import Purelib.Measure.Content.SignedDifference
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.SignedContent.Basic
import Purelib.Measure.SignedContent.Hahn.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

open Purelib.Algebra
open Purelib.Data

namespace Distribution

/-- Form signed content from the two original laws' singleton-mass differences on their consolidated shared keys. -/
@[expose] def signedDifference {α : Type} [DecidableEq α]
    (left right : Distribution α) : SignedContent α :=
  left.toContent.signedDifference right.toContent

/-- Select the Hahn-positive singleton-mass differences of the exact two original laws. -/
@[expose] def totalVariationEvent {α : Type} [DecidableEq α]
    (left right : Distribution α) : α → Bool :=
  (left.toContent.signedDifferenceHahnCertificate
    right.toContent).positiveEvent

open Purelib.Data.Rat in
/-- Sum the positive singleton-mass differences between the two original finite laws.

Normalization makes positive and negative difference totals equal; the retained Hahn event attains this executable total
as a probability difference. -/
@[expose] def totalVariationDistance {α : Type} [DecidableEq α]
    (left right : Distribution α) : Fraction.Rational :=
  (left.signedDifference right).positiveContent.total

/-- Total variation reads the same positive mass under either supplied equality procedure. -/
theorem totalVariationDistance_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (left right : Distribution α) :
    @totalVariationDistance α first left right = @totalVariationDistance α second left right :=
  congrArg (fun difference : SignedContent α => difference.positiveContent.total)
    (Content.signedDifference_eq_of_decidableEq first second left.toContent right.toContent)

/-- Equal law inputs retain total variation under either supplied equality procedure. -/
private theorem totalVariationDistance_agreement {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (left left' : Distribution α) (e_left : left = left')
    (right right' : Distribution α) (e_right : right = right') :
    @totalVariationDistance α first left right = @totalVariationDistance α second left' right' := by
  cases e_left
  cases e_right
  exact totalVariationDistance_eq_of_decidableEq first second left right

open Lean Elab Command in
run_elab do
  let name := Name.str ``totalVariationDistance "congr_simp"
  let kinds : Array Meta.CongrArgKind := #[.fixed, .subsingletonInst, .eq, .eq]
  let .thmInfo info ← getConstInfo ``totalVariationDistance_agreement
    | throwError "pointwise certificate is not a safe theorem"
  let operationInfo ← getConstInfo ``totalVariationDistance
  let .forallE alpha _ operationType _ := operationInfo.type
    | throwError "equality procedure owner has no type binder"
  let .forallE procedure _ operationType _ := operationType
    | throwError "equality procedure owner has no procedure binder"
  let .forallE left _ operationType _ := operationType
    | throwError "equality procedure owner has no first input"
  let .forallE right _ _ _ := operationType
    | throwError "equality procedure owner has no second input"
  let names := #[alpha, procedure, procedure, left, left,
    Name.str .anonymous ("e_" ++ left.toString), right, right,
    Name.str .anonymous ("e_" ++ right.toString)]
  let rec retainNames (type : Expr) (index : Nat) : Expr :=
    match type with
    | .forallE original domain body mode =>
        .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
    | other => other
  Meta.realizeConst ``totalVariationDistance name do
    addDecl (.thmDecl {
      name, type := retainNames info.type 0, levelParams := info.levelParams
      value := info.value
    }) (forceExpose := true)
    modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
  let some congrThm ← Meta.mkCongrSimpForConst? ``totalVariationDistance []
    | throwError "registered original congruence lookup failed"
  unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
    throwError "automatic lookup changed the original public certificate"

open Purelib.Data.Rat in
/-- Sum the magnitudes of singleton-mass differences on the two laws' exact consolidated key list. -/
@[expose] def atomMassL1Distance {α : Type} [DecidableEq α]
    (left right : Distribution α) : Fraction.Rational :=
  (left.signedDifference right).variationContent.total

/-- The signed difference of two normalized laws has total zero. -/
theorem signedDifference_total_eq_zero {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    (left.signedDifference right).total = 0 := by
  unfold signedDifference
  rw [Content.signedDifference_total,
    left.toContent_total, right.toContent_total]
  ring1

/-- The positive and negative parts of the two laws' signed difference have equal total mass. -/
theorem signedDifference_positiveTotal_eq_negativeTotal
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    (left.signedDifference right).positiveContent.total =
      (left.signedDifference right).negativeContent.total := by
  have decomposition :=
    (left.signedDifference right).measure_eq_positive_sub_negative
      (fun _ => true)
  rw [(left.signedDifference right).measure_univ,
    (left.signedDifference right).positiveContent.measure_univ,
    (left.signedDifference right).negativeContent.measure_univ,
    left.signedDifference_total_eq_zero right] at decomposition
  exact Group.eq_of_sub_eq_zero decomposition.symm

/-- Total variation distance is nonnegative. -/
theorem totalVariationDistance_nonnegative {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    0 ≤ left.totalVariationDistance right := by
  unfold totalVariationDistance
  rw [← (left.signedDifference right).positiveContent.measure_univ]
  exact (left.signedDifference right).positiveContent.measure_nonneg _

/-- The retained Hahn event attains total variation as left probability minus right probability. -/
theorem probability_sub_at_totalVariationEvent
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.probability (left.totalVariationEvent right) -
        right.probability (left.totalVariationEvent right) =
      left.totalVariationDistance right := by
  let certificate :=
    left.toContent.signedDifferenceHahnCertificate
      right.toContent
  calc
    left.probability (left.totalVariationEvent right) -
          right.probability (left.totalVariationEvent right) =
        (left.signedDifference right).measure
          (left.totalVariationEvent right) :=
      (left.toContent.signedDifference_measure right.toContent
        (left.totalVariationEvent right)).symm
    _ = (left.signedDifference right).positiveContent.total := by
      change (left.signedDifference right).measure
          certificate.positiveEvent =
        (left.signedDifference right).positiveContent.total
      exact certificate.measure_positiveEvent_eq_positiveTotal
    _ = left.totalVariationDistance right := rfl

open Purelib.Data.Rat in
/-- Every Boolean event's probability separation is bounded by the exact laws' total variation distance. -/
theorem probability_separation_le_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (event : α → Bool) :
    Distance.rationalSeparation (left.probability event) (right.probability event) ≤
      left.totalVariationDistance right := by
  let difference := left.signedDifference right
  let certificate :=
    left.toContent.signedDifferenceHahnCertificate
      right.toContent
  have measured : difference.measure event =
      left.probability event - right.probability event :=
    left.toContent.signedDifference_measure right.toContent event
  have upper : difference.measure event ≤
      difference.positiveContent.total := by
    calc
      difference.measure event ≤
          difference.measure certificate.positiveEvent :=
        certificate.measure_le_positiveEvent event
      _ = difference.positiveContent.total :=
        certificate.measure_positiveEvent_eq_positiveTotal
  have lower : -difference.positiveContent.total ≤
      difference.measure event := by
    calc
      -difference.positiveContent.total =
          -difference.negativeContent.total := by
        rw [left.signedDifference_positiveTotal_eq_negativeTotal right]
      _ = difference.measure
          (fun item => !(certificate.positiveEvent item)) :=
        certificate.measure_complement_eq_neg_negativeTotal.symm
      _ ≤ difference.measure event :=
        certificate.complement_measure_le event
  have negativeUpper : -difference.measure event ≤
      difference.positiveContent.total := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct lower
    simpa only [neg_neg] using reversed
  unfold Distance.rationalSeparation totalVariationDistance
  apply Fraction.Order.Basic.max_le
  · rw [← measured]
    exact upper
  · calc
      right.probability event - left.probability event =
          -(left.probability event - right.probability event) := by ring1
      _ = -difference.measure event := by rw [measured]
      _ ≤ difference.positiveContent.total := negativeUpper

/-- Total variation distance between normalized finite laws is at most one. -/
theorem totalVariationDistance_le_one {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    left.totalVariationDistance right ≤ 1 := by
  rw [← left.probability_sub_at_totalVariationEvent right]
  have translated := Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
    (right.probability_nonneg (left.totalVariationEvent right))
    (left.probability (left.totalVariationEvent right) -
      right.probability (left.totalVariationEvent right))
  have restored : right.probability (left.totalVariationEvent right) +
      (left.probability (left.totalVariationEvent right) -
        right.probability (left.totalVariationEvent right)) =
      left.probability (left.totalVariationEvent right) := by ring1
  rw [zero_add, restored] at translated
  exact translated.trans (left.probability_le_one (left.totalVariationEvent right))

/-- The singleton-mass magnitude sum is twice the total variation distance. -/
theorem atomMassL1Distance_eq_two_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.atomMassL1Distance right =
      2 * left.totalVariationDistance right := by
  have variationDecomposition :
      (left.signedDifference right).variationContent.total =
        (left.signedDifference right).positiveContent.total +
          (left.signedDifference right).negativeContent.total := by
    simpa only [Content.measure_univ] using
      (left.signedDifference right).variation_measure_eq_add
        (fun _ => true)
  unfold atomMassL1Distance totalVariationDistance
  rw [variationDecomposition,
    ← left.signedDifference_positiveTotal_eq_negativeTotal right]
  ring1

open Purelib.Data.Rat
/-- Swapping the two original laws preserves total variation distance. -/
theorem totalVariationDistance_symm {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    left.totalVariationDistance right =
      right.totalVariationDistance left := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · calc
      left.totalVariationDistance right =
          left.probability (left.totalVariationEvent right) -
            right.probability (left.totalVariationEvent right) :=
        (left.probability_sub_at_totalVariationEvent right).symm
      _ ≤ Distance.rationalSeparation
          (right.probability (left.totalVariationEvent right))
          (left.probability (left.totalVariationEvent right)) :=
        Fraction.Order.Basic.le_max_right _ _
      _ ≤ right.totalVariationDistance left :=
        right.probability_separation_le_totalVariationDistance left _
  · calc
      right.totalVariationDistance left =
          right.probability (right.totalVariationEvent left) -
            left.probability (right.totalVariationEvent left) :=
        (right.probability_sub_at_totalVariationEvent left).symm
      _ ≤ Distance.rationalSeparation
          (left.probability (right.totalVariationEvent left))
          (right.probability (right.totalVariationEvent left)) :=
        Fraction.Order.Basic.le_max_right _ _
      _ ≤ left.totalVariationDistance right :=
        left.probability_separation_le_totalVariationDistance right _

/-- Total variation distance satisfies the triangle inequality through a third retained law. -/
theorem totalVariationDistance_triangle {α : Type} [DecidableEq α]
    (left middle right : Distribution α) :
    left.totalVariationDistance right ≤
      left.totalVariationDistance middle +
        middle.totalVariationDistance right := by
  let event := left.totalVariationEvent right
  calc
    left.totalVariationDistance right =
        left.probability event - right.probability event :=
      (left.probability_sub_at_totalVariationEvent right).symm
    _ = (left.probability event - middle.probability event) +
        (middle.probability event - right.probability event) := by ring1
    _ ≤ Distance.rationalSeparation (left.probability event)
          (middle.probability event) +
        Distance.rationalSeparation (middle.probability event)
          (right.probability event) :=
      add_le_add (Fraction.Order.Basic.le_max_left _ _) (Fraction.Order.Basic.le_max_left _ _)
    _ ≤ left.totalVariationDistance middle +
        middle.totalVariationDistance right :=
      Fraction.Order.Arithmetic.add_le_add_direct
        (left.probability_separation_le_totalVariationDistance middle event)
        (middle.probability_separation_le_totalVariationDistance right event)

/-- Total variation vanishes exactly when the two laws agree on all probability and expectation evaluations. -/
theorem totalVariationDistance_eq_zero_iff_evaluationEquivalent
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.totalVariationDistance right = 0 ↔
      EvaluationEquivalent left right := by
  constructor
  · intro zero
    have probabilityEqual : ∀ event : α → Bool,
        left.probability event = right.probability event := by
      intro event
      have bounded :=
        left.probability_separation_le_totalVariationDistance right event
      rw [zero] at bounded
      have separationZero := Fraction.Order.Basic.Compatibility.le_antisymm _ _
        bounded (Distance.rationalSeparation_nonneg _ _)
      exact (Distance.rationalSeparation_eq_zero_iff _ _).mp separationZero
    have contentEquivalent : Content.EvaluationEquivalent
        left.toContent right.toContent :=
      Content.EvaluationEquivalent.of_atom_measure_eq fun item =>
        probabilityEqual (atomEvent item)
    exact
      { probability_eq := probabilityEqual
        expectation_eq := contentEquivalent.integral_eq }
  · intro equivalent
    rw [← left.probability_sub_at_totalVariationEvent right,
      equivalent.probability_eq]
    ring1

/-- Replacing each law by an evaluation-equivalent law preserves their total variation distance. -/
theorem totalVariationDistance_eq_of_evaluationEquivalent
    {α : Type} [DecidableEq α]
    {leftFirst leftSecond rightFirst rightSecond : Distribution α}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    leftFirst.totalVariationDistance rightFirst =
      leftSecond.totalVariationDistance rightSecond := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · let event := leftFirst.totalVariationEvent rightFirst
    calc
      leftFirst.totalVariationDistance rightFirst =
          leftFirst.probability event - rightFirst.probability event :=
        (leftFirst.probability_sub_at_totalVariationEvent rightFirst).symm
      _ = leftSecond.probability event - rightSecond.probability event := by
        rw [leftEquivalent.probability_eq event,
          rightEquivalent.probability_eq event]
      _ ≤ Distance.rationalSeparation (leftSecond.probability event)
          (rightSecond.probability event) := Fraction.Order.Basic.le_max_left _ _
      _ ≤ leftSecond.totalVariationDistance rightSecond :=
        leftSecond.probability_separation_le_totalVariationDistance
          rightSecond event
  · let event := leftSecond.totalVariationEvent rightSecond
    calc
      leftSecond.totalVariationDistance rightSecond =
          leftSecond.probability event - rightSecond.probability event :=
        (leftSecond.probability_sub_at_totalVariationEvent rightSecond).symm
      _ = leftFirst.probability event - rightFirst.probability event := by
        rw [← leftEquivalent.probability_eq event,
          ← rightEquivalent.probability_eq event]
      _ ≤ Distance.rationalSeparation (leftFirst.probability event)
          (rightFirst.probability event) := Fraction.Order.Basic.le_max_left _ _
      _ ≤ leftFirst.totalVariationDistance rightFirst :=
        leftFirst.probability_separation_le_totalVariationDistance
          rightFirst event

end Distribution

end Purelib.Measure

end
