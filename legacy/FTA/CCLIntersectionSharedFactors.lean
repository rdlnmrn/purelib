import FTA.CCLIntersectionEventSigns

/-!
# Shared-factor splits for CCL intersection conditions

At a squarefree event polynomial `p`, a closed condition `q` is either
coprime to `p`, or the executable gcd splits the event set into two disjoint
branches.  The gcd branch consists of equality events for `q`; the residual
`p/gcd(p,q)` branch is coprime to `q` and therefore uses
`CCLIntersectionEventSigns` for a bounded strict-sign decision.  This module
constructs both squarefree transducer inputs and proves the exact zero/equality
dichotomy without factoring over unnamed real or complex roots.
-/

namespace FTA
namespace CCLIntersectionSharedFactors

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLIntersectionEventSigns
open FTA.DenseDerivative
open FTA.DenseGCD
open FTA.DenseSquarefree
open FTA.SquarefreeFactorization
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

/-- Package any represented nonzero nonconstant squarefree polynomial as the
fully executable squarefree Sturm input used by the event layer. -/
def squarefreeInputOfSparseSquarefree (p : RatPolynomial)
    (nonzero : p.isZero = false) (nonconstant : p.natDegree ≠ 0)
    (squarefree : Squarefree p.toPolynomial) : SquarefreeInput p where
  nonzero := nonzero
  nonconstant := nonconstant
  squarefree := certificateOfSparseSquarefree p nonzero squarefree

/-- The residual quotient is either a nonzero constant, carrying no event,
or another proof-bearing squarefree event polynomial. -/
inductive ResidualEventFactor (p : RatPolynomial) where
  | constant (degreeZero : p.natDegree = 0)
  | nonconstant (input : SquarefreeInput p)

/-- Complete nontrivial gcd branch for one event polynomial and one closed
condition. -/
structure SharedFactorBranch (p q : RatPolynomial)
    (input : SquarefreeInput p) where
  sharedNonconstant : (FTA.DenseGCD.gcd p q).natDegree ≠ 0
  sharedInput : SquarefreeInput (FTA.DenseGCD.gcd p q)
  residualNonzero : (leftFactor p q).isZero = false
  residual : ResidualEventFactor (leftFactor p q)
  residualCoprime : CoprimeCertificate (leftFactor p q) q

/-- Total exact outcome: either the condition is coprime to the whole event
polynomial or a shared-factor split is returned. -/
inductive EventConditionSplit (p q : RatPolynomial)
    (input : SquarefreeInput p) where
  | coprime (certificate : CoprimeCertificate p q)
  | shared (branch : SharedFactorBranch p q input)

/-- Squarefreeness of `p` makes its gcd and residual quotient squarefree and
relatively prime to each other.  Combining that fact with the usual coprimality of the
two gcd quotients proves that the residual is coprime to the original `q`,
not merely to `q/gcd(p,q)`. -/
def splitCondition {p : RatPolynomial} (input : SquarefreeInput p)
    (q : RatPolynomial) : EventConditionSplit p q input := by
  have gcdNonzero : (FTA.DenseGCD.gcd p q).isZero = false :=
    gcd_isZero_false_of_nonzero p q (Or.inl input.nonzero)
  if gcdConstant : (FTA.DenseGCD.gcd p q).natDegree = 0 then
    exact .coprime (certificateOfConstantGCD (extendedGCD p q)
      (by simpa only [FTA.DenseGCD.gcd] using gcdNonzero)
      (by simpa only [FTA.DenseGCD.gcd] using gcdConstant))
  else
    have eventSquarefree : Squarefree p.toPolynomial :=
      input.squarefree.sparseSquarefree
    have sharedSquarefree :
        Squarefree (FTA.DenseGCD.gcd p q).toPolynomial :=
      eventSquarefree.squarefree_of_dvd (gcd_toPolynomial_dvd_left p q)
    have residualNonzero : (leftFactor p q).isZero = false :=
      leftFactor_isZero_false input.nonzero
    have residualDivides : (leftFactor p q).toPolynomial ∣ p.toPolynomial := by
      refine ⟨(FTA.DenseGCD.gcd p q).toPolynomial, ?_⟩
      calc
        p.toPolynomial = (FTA.DenseGCD.gcd p q).toPolynomial *
            (leftFactor p q).toPolynomial :=
          leftFactor_toPolynomial_identity p q
        _ = (leftFactor p q).toPolynomial *
            (FTA.DenseGCD.gcd p q).toPolynomial := mul_comm _ _
    have residualSquarefree : Squarefree (leftFactor p q).toPolynomial :=
      eventSquarefree.squarefree_of_dvd residualDivides
    have productSquarefree : Squarefree
        ((FTA.DenseGCD.gcd p q).toPolynomial *
          (leftFactor p q).toPolynomial) := by
      rw [← leftFactor_toPolynomial_identity p q]
      exact eventSquarefree
    have residualRelPrime :
        IsRelPrime (leftFactor p q).toPolynomial q.toPolynomial := by
      have sharedResidualRelPrime := IsRelPrime.of_squarefree_mul productSquarefree
      have residualQuotientCoprime :=
        reducedFactors_isCoprime p q (Or.inl input.nonzero)
      have residualProductRelPrime : IsRelPrime
          (leftFactor p q).toPolynomial
          ((FTA.DenseGCD.gcd p q).toPolynomial *
            (rightFactor p q).toPolynomial) :=
        sharedResidualRelPrime.symm.mul_right residualQuotientCoprime.isRelPrime
      rw [rightFactor_toPolynomial_identity p q]
      exact residualProductRelPrime
    let residualCoprime : CoprimeCertificate (leftFactor p q) q :=
      certificateOfIsRelPrimeNonzero (leftFactor p q) q (Or.inl residualNonzero)
        residualRelPrime
    let sharedInput : SquarefreeInput (FTA.DenseGCD.gcd p q) :=
      squarefreeInputOfSparseSquarefree (FTA.DenseGCD.gcd p q) gcdNonzero gcdConstant
        sharedSquarefree
    let residual : ResidualEventFactor (leftFactor p q) :=
      if residualConstant : (leftFactor p q).natDegree = 0 then
        .constant residualConstant
      else
        .nonconstant (squarefreeInputOfSparseSquarefree (leftFactor p q)
          residualNonzero residualConstant residualSquarefree)
    exact .shared
      { sharedNonconstant := gcdConstant
        sharedInput
        residualNonzero
        residual
        residualCoprime }

namespace SharedFactorBranch

theorem event_eval_identity {p q : RatPolynomial} {input : SquarefreeInput p}
    (_branch : SharedFactorBranch p q input) (t : ℚ) :
    p.eval t = (FTA.DenseGCD.gcd p q).eval t *
      (leftFactor p q).eval t := by
  change p.eval t = (extendedGCD p q).gcd.eval t *
    (extendedGCD p q).pFactor.eval t
  exact (extendedGCD p q).pIdentity t

theorem condition_eval_identity
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (_branch : SharedFactorBranch p q input) (t : ℚ) :
    q.eval t = (FTA.DenseGCD.gcd p q).eval t *
      (rightFactor p q).eval t := by
  change q.eval t = (extendedGCD p q).gcd.eval t *
    (extendedGCD p q).qFactor.eval t
  exact (extendedGCD p q).qIdentity t

/-- A shared-factor zero is exactly an equality event for the condition. -/
theorem condition_eq_zero_of_shared_eq_zero
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) {t : ℚ}
    (sharedZero : (FTA.DenseGCD.gcd p q).eval t = 0) : q.eval t = 0 := by
  rw [branch.condition_eval_identity, sharedZero, zero_mul]

/-- The residual and the original condition have no common rational zero;
the stronger sparse Bézout identity is retained in `residualCoprime`. -/
theorem condition_ne_zero_of_residual_eq_zero
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) {t : ℚ}
    (residualZero : (leftFactor p q).eval t = 0) : q.eval t ≠ 0 := by
  intro conditionZero
  have identity := branch.residualCoprime.identity t
  rw [residualZero, conditionZero] at identity
  norm_num at identity

theorem shared_ne_zero_of_residual_eq_zero
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) {t : ℚ}
    (residualZero : (leftFactor p q).eval t = 0) :
    (FTA.DenseGCD.gcd p q).eval t ≠ 0 := by
  intro sharedZero
  exact branch.condition_ne_zero_of_residual_eq_zero residualZero
    (branch.condition_eq_zero_of_shared_eq_zero sharedZero)

theorem residual_ne_zero_of_shared_eq_zero
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) {t : ℚ}
    (sharedZero : (FTA.DenseGCD.gcd p q).eval t = 0) :
    (leftFactor p q).eval t ≠ 0 := by
  intro residualZero
  exact branch.shared_ne_zero_of_residual_eq_zero residualZero sharedZero

/-- Every exact event zero lies in exactly one computable branch: a shared
equality event, or a residual nonvanishing event. -/
theorem event_zero_split
    {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) {t : ℚ}
    (eventZero : p.eval t = 0) :
    ((FTA.DenseGCD.gcd p q).eval t = 0 ∧
        (leftFactor p q).eval t ≠ 0 ∧ q.eval t = 0) ∨
      ((FTA.DenseGCD.gcd p q).eval t ≠ 0 ∧
        (leftFactor p q).eval t = 0 ∧ q.eval t ≠ 0) := by
  rw [branch.event_eval_identity] at eventZero
  rcases mul_eq_zero.mp eventZero with sharedZero | residualZero
  · exact .inl ⟨sharedZero,
      branch.residual_ne_zero_of_shared_eq_zero sharedZero,
      branch.condition_eq_zero_of_shared_eq_zero sharedZero⟩
  · exact .inr ⟨branch.shared_ne_zero_of_residual_eq_zero residualZero,
      residualZero,
      branch.condition_ne_zero_of_residual_eq_zero residualZero⟩

/-- The residual branch is immediately consumable by the common event-sign
refinement from `CCLIntersectionEventSigns`. -/
def residualCondition {p q : RatPolynomial} {input : SquarefreeInput p}
    (branch : SharedFactorBranch p q input) :
    CoprimeCondition (leftFactor p q) where
  polynomial := q
  coprime := branch.residualCoprime

end SharedFactorBranch

/-! ## Simultaneous finite condition splitting -/

/-- Exact relation of one condition to one squarefree event factor. -/
inductive ConditionRelation (p q : RatPolynomial) where
  | equality (divides : p.toPolynomial ∣ q.toPolynomial)
  | coprime (certificate : CoprimeCertificate p q)

def ConditionRelation.isEquality {p q : RatPolynomial} :
    ConditionRelation p q → Bool
  | .equality _ => true
  | .coprime _ => false

private theorem eval_eq_zero_of_toPolynomial_dvd
    {p q : RatPolynomial} (divides : p.toPolynomial ∣ q.toPolynomial)
    {t : ℚ} (eventZero : p.eval t = 0) : q.eval t = 0 := by
  rcases divides with ⟨quotient, identity⟩
  calc
    q.eval t = Polynomial.eval t q.toPolynomial := (eval_toPolynomial q t).symm
    _ = Polynomial.eval t (p.toPolynomial * quotient) := by rw [identity]
    _ = p.eval t * Polynomial.eval t quotient := by
      rw [Polynomial.eval_mul, eval_toPolynomial]
    _ = 0 := by rw [eventZero, zero_mul]

theorem ConditionRelation.eval_eq_zero_of_isEquality
    {p q : RatPolynomial} (relation : ConditionRelation p q) {t : ℚ}
    (eventZero : p.eval t = 0) (equality : relation.isEquality = true) :
    q.eval t = 0 := by
  cases relation with
  | equality divides => exact eval_eq_zero_of_toPolynomial_dvd divides eventZero
  | coprime certificate => simp [ConditionRelation.isEquality] at equality

theorem ConditionRelation.eval_ne_zero_of_isEquality_false
    {p q : RatPolynomial} (relation : ConditionRelation p q) {t : ℚ}
    (eventZero : p.eval t = 0) (nonEquality : relation.isEquality = false) :
    q.eval t ≠ 0 := by
  cases relation with
  | equality divides => simp [ConditionRelation.isEquality] at nonEquality
  | coprime certificate =>
      intro conditionZero
      have identity := certificate.identity t
      rw [eventZero, conditionZero] at identity
      norm_num at identity

/-- Restrict a condition relation to a squarefree divisor event factor. -/
def ConditionRelation.ofDvd
    {p q subfactor : RatPolynomial} (relation : ConditionRelation p q)
    (subfactorInput : SquarefreeInput subfactor)
    (divides : subfactor.toPolynomial ∣ p.toPolynomial) :
    ConditionRelation subfactor q :=
  match relation with
  | .equality conditionDivides =>
      .equality (dvd_trans divides conditionDivides)
  | .coprime certificate =>
      .coprime (certificateOfIsCoprime subfactor q subfactorInput.nonzero
        (certificate.isCoprime.of_isCoprime_of_dvd_left divides))

/-- Relations aligned with an ordered finite condition list. -/
inductive ConditionRelations (p : RatPolynomial) :
    List RatPolynomial → Type
  | nil : ConditionRelations p []
  | cons {q : RatPolynomial} {conditions : List RatPolynomial}
      (head : ConditionRelation p q)
      (tail : ConditionRelations p conditions) :
      ConditionRelations p (q :: conditions)

def ConditionRelations.ofDvd
    {p subfactor : RatPolynomial} (subfactorInput : SquarefreeInput subfactor)
    (divides : subfactor.toPolynomial ∣ p.toPolynomial) :
    {conditions : List RatPolynomial} → ConditionRelations p conditions →
      ConditionRelations subfactor conditions
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (head.ofDvd subfactorInput divides)
        (tail.ofDvd subfactorInput divides)

/-- One squarefree event factor classified against every processed
condition. -/
structure ClassifiedEventFactor (conditions : List RatPolynomial) where
  factor : Factor
  relations : ConditionRelations factor.polynomial conditions

theorem residualFactor_toPolynomial_dvd_left (p q : RatPolynomial) :
    (leftFactor p q).toPolynomial ∣ p.toPolynomial := by
  refine ⟨(FTA.DenseGCD.gcd p q).toPolynomial, ?_⟩
  calc
    p.toPolynomial = (FTA.DenseGCD.gcd p q).toPolynomial *
        (leftFactor p q).toPolynomial :=
      leftFactor_toPolynomial_identity p q
    _ = (leftFactor p q).toPolynomial *
        (FTA.DenseGCD.gcd p q).toPolynomial := mul_comm _ _

/-- Refine one already-classified event factor by one additional condition.
The result has one branch in the coprime/all-shared cases and two branches
for a genuine partial gcd split. -/
def refineClassifiedEventFactor
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions) (q : RatPolynomial) :
    List (ClassifiedEventFactor (q :: conditions)) :=
  match splitCondition classified.factor.input q with
  | .coprime certificate =>
      [{ factor := classified.factor
         relations := .cons (.coprime certificate) classified.relations }]
  | .shared branch =>
      let sharedFactor : Factor :=
        { polynomial := FTA.DenseGCD.gcd classified.factor.polynomial q
          input := branch.sharedInput }
      let sharedClassified : ClassifiedEventFactor (q :: conditions) :=
        { factor := sharedFactor
          relations := .cons
            (.equality (gcd_toPolynomial_dvd_right
              classified.factor.polynomial q))
            (classified.relations.ofDvd branch.sharedInput
              (gcd_toPolynomial_dvd_left classified.factor.polynomial q)) }
      match branch.residual with
      | .constant _ => [sharedClassified]
      | .nonconstant residualInput =>
          let residualFactor : Factor :=
            { polynomial := leftFactor classified.factor.polynomial q
              input := residualInput }
          let residualClassified : ClassifiedEventFactor (q :: conditions) :=
            { factor := residualFactor
              relations := .cons (.coprime branch.residualCoprime)
                (classified.relations.ofDvd residualInput
                  (residualFactor_toPolynomial_dvd_left
                    classified.factor.polynomial q)) }
          [sharedClassified, residualClassified]

theorem refineClassifiedEventFactor_nonempty
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions) (q : RatPolynomial) :
    refineClassifiedEventFactor classified q ≠ [] := by
  simp only [refineClassifiedEventFactor]
  split
  · simp
  · split <;> simp

/-- Every branch returned by one condition split remains a squarefree divisor
of its parent event factor. -/
theorem refineClassifiedEventFactor_dvd
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions) (q : RatPolynomial)
    {child : ClassifiedEventFactor (q :: conditions)}
    (member : child ∈ refineClassifiedEventFactor classified q) :
    child.factor.polynomial.toPolynomial ∣
      classified.factor.polynomial.toPolynomial := by
  cases split : splitCondition classified.factor.input q with
  | coprime certificate =>
      simp [refineClassifiedEventFactor, split] at member
      subst child
      exact dvd_rfl
  | shared branch =>
      cases residualKind : branch.residual with
      | constant degreeZero =>
          simp [refineClassifiedEventFactor, split, residualKind] at member
          subst child
          exact gcd_toPolynomial_dvd_left classified.factor.polynomial q
      | nonconstant residualInput =>
          simp [refineClassifiedEventFactor, split, residualKind] at member
          rcases member with rfl | rfl
          · exact gcd_toPolynomial_dvd_left classified.factor.polynomial q
          · exact residualFactor_toPolynomial_dvd_left
              classified.factor.polynomial q

/-- A one-step split covers every rational zero of the parent event factor. -/
theorem refineClassifiedEventFactor_covers
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions) (q : RatPolynomial)
    {t : ℚ} (eventZero : classified.factor.polynomial.eval t = 0) :
    ∃ child ∈ refineClassifiedEventFactor classified q,
      child.factor.polynomial.eval t = 0 := by
  cases split : splitCondition classified.factor.input q with
  | coprime certificate =>
      let child : ClassifiedEventFactor (q :: conditions) :=
        { factor := classified.factor
          relations := .cons (.coprime certificate) classified.relations }
      refine ⟨child, ?_, eventZero⟩
      simp [refineClassifiedEventFactor, split, child]
  | shared branch =>
      let sharedFactor : Factor :=
        { polynomial := FTA.DenseGCD.gcd classified.factor.polynomial q
          input := branch.sharedInput }
      let sharedChild : ClassifiedEventFactor (q :: conditions) :=
        { factor := sharedFactor
          relations := .cons
            (.equality (gcd_toPolynomial_dvd_right
              classified.factor.polynomial q))
            (classified.relations.ofDvd branch.sharedInput
              (gcd_toPolynomial_dvd_left classified.factor.polynomial q)) }
      have eventSplit := branch.event_zero_split eventZero
      rcases eventSplit with sharedEvent | residualEvent
      · refine ⟨sharedChild, ?_, sharedEvent.1⟩
        cases residualKind : branch.residual <;>
          simp [refineClassifiedEventFactor, split, residualKind,
            sharedChild, sharedFactor]
      · cases residualKind : branch.residual with
        | constant degreeZero =>
            have residualValue := eval_eq_leadingCoeff_of_natDegree_eq_zero
              branch.residualNonzero degreeZero t
            have leadingNonzero := leadingCoeff_ne_zero branch.residualNonzero
            exact (leadingNonzero (residualValue ▸ residualEvent.2.1)).elim
        | nonconstant residualInput =>
            let residualFactor : Factor :=
              { polynomial := leftFactor classified.factor.polynomial q
                input := residualInput }
            let residualChild : ClassifiedEventFactor (q :: conditions) :=
              { factor := residualFactor
                relations := .cons (.coprime branch.residualCoprime)
                  (classified.relations.ofDvd residualInput
                    (residualFactor_toPolynomial_dvd_left
                      classified.factor.polynomial q)) }
            refine ⟨residualChild, ?_, residualEvent.2.1⟩
            simp [refineClassifiedEventFactor, split, residualKind,
              residualChild, residualFactor]

/-- Process an arbitrary finite condition list.  Every returned factor is
squarefree and carries, for every condition, either divisibility (equality at
that event) or a Bézout certificate (a bounded strict-sign event). -/
def classifyEventConditions {p : RatPolynomial} (input : SquarefreeInput p) :
    (conditions : List RatPolynomial) →
      List (ClassifiedEventFactor conditions)
  | [] => [{ factor := { polynomial := p, input }
             relations := .nil }]
  | q :: conditions =>
      (classifyEventConditions input conditions).flatMap fun classified =>
        refineClassifiedEventFactor classified q

theorem classifyEventConditions_nonempty
    {p : RatPolynomial} (input : SquarefreeInput p) :
    ∀ conditions, classifyEventConditions input conditions ≠ [] := by
  intro conditions
  induction conditions with
  | nil => simp [classifyEventConditions]
  | cons q conditions ih =>
      rw [classifyEventConditions]
      cases classified : classifyEventConditions input conditions with
      | nil => exact (ih classified).elim
      | cons head tail =>
          simp only [List.flatMap_cons]
          intro empty
          exact refineClassifiedEventFactor_nonempty head q
            (List.append_eq_nil_iff.mp empty).1

/-- Every fully classified event branch remains a squarefree divisor of the
original event polynomial. -/
theorem classifyEventConditions_dvd
    {p : RatPolynomial} (input : SquarefreeInput p) :
    ∀ {conditions : List RatPolynomial}
      {classified : ClassifiedEventFactor conditions},
      classified ∈ classifyEventConditions input conditions →
        classified.factor.polynomial.toPolynomial ∣ p.toPolynomial := by
  intro conditions
  induction conditions with
  | nil =>
      intro classified member
      simp [classifyEventConditions] at member
      subst classified
      exact dvd_rfl
  | cons q conditions inductionHypothesis =>
      intro classified member
      rw [classifyEventConditions, List.mem_flatMap] at member
      rcases member with ⟨parent, parentMember, childMember⟩
      exact dvd_trans
        (refineClassifiedEventFactor_dvd parent q childMember)
        (inductionHypothesis parentMember)

/-- The finite classified list covers every rational zero of the original
event factor. -/
theorem classifyEventConditions_covers
    {p : RatPolynomial} (input : SquarefreeInput p)
    (conditions : List RatPolynomial) {t : ℚ} (eventZero : p.eval t = 0) :
    ∃ classified ∈ classifyEventConditions input conditions,
      classified.factor.polynomial.eval t = 0 := by
  induction conditions with
  | nil =>
      let classified : ClassifiedEventFactor [] :=
        { factor := { polynomial := p, input }
          relations := .nil }
      refine ⟨classified, ?_, eventZero⟩
      simp [classifyEventConditions, classified]
  | cons q conditions ih =>
      rcases ih with ⟨parent, parentMember, parentZero⟩
      rcases refineClassifiedEventFactor_covers parent q parentZero with
        ⟨child, childMember, childZero⟩
      refine ⟨child, ?_, childZero⟩
      rw [classifyEventConditions, List.mem_flatMap]
      exact ⟨parent, parentMember, childMember⟩

/-! ## Common signs on every classified branch -/

/-- Retain exactly the non-equality conditions, each with the Bézout
certificate produced while splitting the event factor. -/
def ConditionRelations.coprimeConditions {p : RatPolynomial} :
    {conditions : List RatPolynomial} → ConditionRelations p conditions →
      List (CoprimeCondition p)
  | [], .nil => []
  | _ :: _, .cons (.equality _) tail => tail.coprimeConditions
  | q :: _, .cons (.coprime certificate) tail =>
      ({ polynomial := q, coprime := certificate } : CoprimeCondition p) ::
        tail.coprimeConditions

def ClassifiedEventFactor.coprimeConditions
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions) :
    List (CoprimeCondition classified.factor.polynomial) :=
  classified.relations.coprimeConditions

/-- After the finite gcd tree has assigned all equality conditions, one
bounded shared refinement computes the strict signs of every remaining
condition on this event factor. -/
def ClassifiedEventFactor.computeEventSigns
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions)
    (parent : CountOneInterval classified.factor.polynomial) :
    CommonEventSigns classified.factor.input classified.coprimeConditions
      parent :=
  computeCommonEventSigns classified.factor.input
    classified.coprimeConditions parent

end CCLIntersectionSharedFactors
end FTA
