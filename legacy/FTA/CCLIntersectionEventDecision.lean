import FTA.CCLIntersectionSharedFactors

/-!
# Closed box decisions on CCL intersection-event branches

The shared-factor tree labels every condition on an event branch as either
identically zero at that event or coprime to the branch factor.  This module
combines those labels with the common coprime sign refinement.  Equality
labels satisfy a closed inequality automatically; every other label is
decided by one exact rational midpoint sign.  The resulting Boolean is proved
equivalent to all four closed box conditions on the refined count-one event
cell.
-/

namespace FTA
namespace CCLIntersectionEventDecision

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLIntersectionEventSigns
open FTA.CCLIntersectionGuard
open FTA.CCLIntersectionSharedFactors
open FTA.CCLPathIntersection
open FTA.RationalPolynomialBounds
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

/-- Ordered conjunction of nonnegative polynomial signs. -/
def ConditionsHoldAt : List RatPolynomial → ℚ → Prop
  | [], _ => True
  | polynomial :: conditions, t =>
      0 ≤ polynomial.eval t ∧ ConditionsHoldAt conditions t

/-- Forget the first coprime condition while retaining the same refined
event interval and every remaining sign certificate. -/
def CommonEventSigns.dropHead
    {p : RatPolynomial} {input : SquarefreeInput p}
    {head : CoprimeCondition p} {tail : List (CoprimeCondition p)}
    {parent : CountOneInterval p}
    (result : CommonEventSigns input (head :: tail) parent) :
    CommonEventSigns input tail parent where
  refined := result.refined
  refines := result.refines
  crossing := result.crossing
  signs := by
    intro condition member
    exact result.signs condition (List.mem_cons_of_mem head member)

/-- Closed-sign Boolean aligned with the original condition list.  Equality
conditions need no sign sample; coprime conditions consume the corresponding
entry of the common event-sign result. -/
def ConditionRelations.closedCheck {p : RatPolynomial}
    (input : SquarefreeInput p) (parent : CountOneInterval p) :
    {conditions : List RatPolynomial} →
      (relations : ConditionRelations p conditions) →
      CommonEventSigns input relations.coprimeConditions parent → Bool
  | [], .nil, _result => true
  | _ :: _, .cons (.equality _) tail, result =>
      ConditionRelations.closedCheck input parent tail result
  | q :: _, .cons (.coprime certificate) tail, result =>
      let condition : CoprimeCondition p :=
        { polynomial := q, coprime := certificate }
      result.nonnegative condition (by
        simp [ConditionRelations.coprimeConditions, condition]) &&
        ConditionRelations.closedCheck input parent tail
          (CommonEventSigns.dropHead result)

/-- If all original closed conditions hold at a rational point of the common
sign interval, the executable closed-sign check succeeds.  Equality-labelled
conditions are harmless here; every coprime condition uses its stored strict
whole-interval sign. -/
theorem ConditionRelations.closedCheck_eq_true_of_conditionsHoldAt
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper)
    (holds : ConditionsHoldAt conditions t) :
    ConditionRelations.closedCheck input parent relations result = true := by
  induction relations with
  | nil => rfl
  | @cons q conditions relation tail inductionHypothesis =>
      rcases holds with ⟨headNonnegative, tailHolds⟩
      cases relation with
      | equality divides =>
          exact inductionHypothesis result lower upper tailHolds
      | coprime certificate =>
          let condition : CoprimeCondition p :=
            { polynomial := q, coprime := certificate }
          have conditionMember : condition ∈
              (ConditionRelations.cons (.coprime certificate)
                tail).coprimeConditions := by
            simp [ConditionRelations.coprimeConditions, condition]
          have headTrue : result.nonnegative condition conditionMember = true :=
            (result.nonnegative_eq_true_iff condition conditionMember
              lower upper).mpr headNonnegative
          let tailResult :
              CommonEventSigns input tail.coprimeConditions parent :=
            CommonEventSigns.dropHead result
          have tailLower : tailResult.refined.interval.lower ≤ t := by
            simpa [tailResult, CommonEventSigns.dropHead] using lower
          have tailUpper : t ≤ tailResult.refined.interval.upper := by
            simpa [tailResult, CommonEventSigns.dropHead] using upper
          have tailTrue := inductionHypothesis tailResult tailLower tailUpper
            tailHolds
          simpa [ConditionRelations.closedCheck, condition, conditionMember,
            tailResult, headTrue] using tailTrue

/-- A failed closed-sign check therefore excludes every rational point of
the common sign interval, not merely the (possibly irrational) exact event
root. -/
theorem ConditionRelations.not_conditionsHoldAt_of_closedCheck_eq_false
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    (check :
      ConditionRelations.closedCheck input parent relations result = false)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    ¬ConditionsHoldAt conditions t := by
  intro holds
  have checkTrue := closedCheck_eq_true_of_conditionsHoldAt
    input parent relations result lower upper holds
  rw [check] at checkTrue
  contradiction

/-- A successful closed-sign check has a direct pointwise interpretation even
away from an exact event zero: each displayed condition is either an exact
polynomial multiple of the event factor or is nonnegative throughout the
common refined interval. -/
theorem ConditionRelations.dvd_or_nonnegative_of_closedCheck
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    (check : ConditionRelations.closedCheck input parent relations result = true)
    {q : RatPolynomial} (member : q ∈ conditions)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    p.toPolynomial ∣ q.toPolynomial ∨ 0 ≤ q.eval t := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons polynomial conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides => exact Or.inl divides
        | coprime certificate =>
            right
            let condition : CoprimeCondition p :=
              { polynomial := _, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            change (result.nonnegative condition conditionMember &&
              ConditionRelations.closedCheck input parent tail
                (CommonEventSigns.dropHead result)) = true at check
            rw [Bool.and_eq_true] at check
            exact (result.nonnegative_eq_true_iff condition conditionMember
              lower upper).mp check.1
      · cases relation with
        | equality divides =>
            apply inductionHypothesis result check tailMember lower upper
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := _, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            change (result.nonnegative condition conditionMember &&
              ConditionRelations.closedCheck input parent tail
                tailResult) = true at check
            rw [Bool.and_eq_true] at check
            have tailLower : tailResult.refined.interval.lower ≤ t := by
              simpa [tailResult, CommonEventSigns.dropHead] using lower
            have tailUpper : t ≤ tailResult.refined.interval.upper := by
              simpa [tailResult, CommonEventSigns.dropHead] using upper
            exact inductionHypothesis tailResult check.2 tailMember
              tailLower tailUpper

/-- The closed-sign Boolean has exactly the intended simultaneous semantics
at any rational event zero in the refined interval. -/
theorem ConditionRelations.closedCheck_eq_true_iff
    {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper)
    (eventZero : p.eval t = 0) :
    ConditionRelations.closedCheck input parent relations result = true ↔
      ConditionsHoldAt conditions t := by
  induction relations with
  | nil => simp [ConditionRelations.closedCheck, ConditionsHoldAt]
  | @cons q conditions relation tail ih =>
      cases relation with
      | equality divides =>
          let equalityRelation : ConditionRelation p q := .equality divides
          have conditionZero : q.eval t = 0 :=
            equalityRelation.eval_eq_zero_of_isEquality eventZero rfl
          have tailIff := ih result lower upper
          simpa [ConditionRelations.closedCheck, ConditionsHoldAt,
            conditionZero] using tailIff
      | coprime certificate =>
          let condition : CoprimeCondition p :=
            { polynomial := q, coprime := certificate }
          have member : condition ∈
              (ConditionRelations.cons (.coprime certificate) tail).coprimeConditions := by
            simp [ConditionRelations.coprimeConditions, condition]
          have headIff := result.nonnegative_eq_true_iff condition member lower upper
          let tailResult :
              CommonEventSigns input tail.coprimeConditions parent :=
            CommonEventSigns.dropHead result
          have tailLower : tailResult.refined.interval.lower ≤ t := by
            simpa [tailResult, CommonEventSigns.dropHead] using lower
          have tailUpper : t ≤ tailResult.refined.interval.upper := by
            simpa [tailResult, CommonEventSigns.dropHead] using upper
          have tailIff := ih tailResult tailLower tailUpper
          simpa [ConditionRelations.closedCheck, ConditionsHoldAt, condition,
            member, tailResult] using and_congr headIff tailIff

theorem conditionPolynomials_holdAt_iff
    (conditions : BoxConditions) (t : ℚ) :
    ConditionsHoldAt (conditionPolynomials conditions) t ↔
      conditions.HoldsAt t := by
  simp [ConditionsHoldAt, conditionPolynomials, BoxConditions.HoldsAt]

/-- Finite event-factor branches for the four closed box conditions. -/
def boxEventBranches (p : RatPolynomial) (input : SquarefreeInput p)
    (conditions : BoxConditions) :
    List (ClassifiedEventFactor (conditionPolynomials conditions)) :=
  classifyEventConditions input (conditionPolynomials conditions)

theorem boxEventBranches_nonempty
    (p : RatPolynomial) (input : SquarefreeInput p)
    (conditions : BoxConditions) :
    boxEventBranches p input conditions ≠ [] :=
  classifyEventConditions_nonempty input (conditionPolynomials conditions)

theorem boxEventBranches_cover
    (p : RatPolynomial) (input : SquarefreeInput p)
    (conditions : BoxConditions) {t : ℚ} (eventZero : p.eval t = 0) :
    ∃ branch ∈ boxEventBranches p input conditions,
      branch.factor.polynomial.eval t = 0 :=
  classifyEventConditions_covers input (conditionPolynomials conditions)
    eventZero

/-- Executable closed-box bit on one classified count-one event branch. -/
def boxEventCheck
    {conditions : BoxConditions}
    (branch : ClassifiedEventFactor (conditionPolynomials conditions))
    (parent : CountOneInterval branch.factor.polynomial) : Bool :=
  ConditionRelations.closedCheck branch.factor.input parent branch.relations
    (branch.computeEventSigns parent)

/-- The branch bit is exactly closed box membership at every rational event
zero in the computed refined interval. -/
theorem boxEventCheck_eq_true_iff
    {conditions : BoxConditions}
    (branch : ClassifiedEventFactor (conditionPolynomials conditions))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤ (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0) :
    boxEventCheck branch parent = true ↔ conditions.HoldsAt t := by
  rw [boxEventCheck]
  exact (ConditionRelations.closedCheck_eq_true_iff branch.factor.input parent
    branch.relations
    (branch.computeEventSigns parent) lower upper eventZero).trans
      (conditionPolynomials_holdAt_iff conditions t)

/-- Equivalent formulation against the existing exact four-sign evaluator. -/
theorem boxEventCheck_eq_check
    {conditions : BoxConditions}
    (branch : ClassifiedEventFactor (conditionPolynomials conditions))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤ (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0) :
    boxEventCheck branch parent = true ↔ conditions.check t = true := by
  rw [boxEventCheck_eq_true_iff branch parent lower upper eventZero]
  exact (BoxConditions.check_eq_true_iff conditions t).symm

end CCLIntersectionEventDecision
end FTA
