import FTA.CCLBranchEvidence
import FTA.CCLClearanceExclusion
import FTA.CCLFormulaPath

/-!
# Parser-formula values on classified CCL branch events

An isolated branch event represents an algebraic parameter by a squarefree
factor and a count-one rational interval.  Completing that parameter is not
needed to choose the parser's strict/weak equality convention.  Gcd
classification says that each cleared atom is either identically zero on the
event branch or coprime to it; the existing common sign refinement supplies a
single rational sample for every coprime atom.

This module turns those aligned relation certificates into surrogate rational
atom values.  Zero relations receive the exact value zero, while coprime
relations receive their certified sample value.  A small list-consuming
evaluator then proves that every Boolean parser formula has exactly the same
truth value on the surrogate list as at any represented event zero.
-/

namespace FTA
namespace CCLBranchEventOwner

open CCL
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLParserGeometry
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLIntersectionEventSigns
open FTA.CCLIntersectionSharedFactors
open FTA.CCLIntersectionEventDecision
open FTA.CCLIntersectionSampler
open FTA.CCLCountOneClassification
open FTA.CCLBranchEvent
open FTA.CCLBranchEvidence
open FTA.CCLBranchCharts
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLGeometry
open FTA.ProjectivePath
open FTA.ProjectivePathBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation
open FTA.LocalExtraction
open FTA.GaussianPolynomialBounds
open FTA.CCLClearanceExclusion
open FTA.RationalPolynomialBounds
open FTA.SquarefreeFactorization
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Rational surrogate values aligned with the original classified condition
list.  Equality relations contribute zero; a coprime relation contributes the
sample of its whole-cell sign certificate. -/
def eventValues
    {p : RatPolynomial} {input : SquarefreeInput p}
    (parent : CountOneInterval p) :
    {conditions : List RatPolynomial} →
      (relations : ConditionRelations p conditions) →
      CommonEventSigns input relations.coprimeConditions parent → List ℚ
  | [], .nil, _ => []
  | _ :: _, .cons (.equality _) tail, result =>
      0 :: eventValues parent tail result
  | q :: _, .cons (.coprime certificate) tail, result =>
      let condition : CoprimeCondition p :=
        { polynomial := q, coprime := certificate }
      let sign := result.signs condition (by
        simp [ConditionRelations.coprimeConditions, condition])
      q.eval sign.sample ::
        eventValues parent tail
          (FTA.CCLIntersectionEventDecision.CommonEventSigns.dropHead result)

/-- Canonical rational representative of a polynomial's sign at an isolated
event.  A multiple of the event factor receives zero; every coprime
polynomial is sampled at the common refined interval's left endpoint. -/
def canonicalEventValue {event : RatPolynomial}
    (input : SquarefreeInput event) (polynomial : RatPolynomial)
    (sample : ℚ) : ℚ :=
  match splitCondition input polynomial with
  | .coprime _ => polynomial.eval sample
  | .shared _ => 0

private theorem not_dvd_of_coprime
    {p q : RatPolynomial} (input : SquarefreeInput p)
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) :
    ¬p.toPolynomial ∣ q.toPolynomial := by
  intro divides
  have unit := certificate.isCoprime.isUnit_of_dvd divides
  have degree := Polynomial.natDegree_eq_zero_of_isUnit unit
  rw [natDegree_toPolynomial input.nonzero] at degree
  exact input.nonconstant degree

/-- A polynomial multiple of the nonconstant event factor receives the
canonical equality value zero. -/
theorem canonicalEventValue_eq_zero_of_dvd
    {event : RatPolynomial} (input : SquarefreeInput event)
    (polynomial : RatPolynomial) (sample : ℚ)
    (divides : event.toPolynomial ∣ polynomial.toPolynomial) :
    canonicalEventValue input polynomial sample = 0 := by
  cases split : splitCondition input polynomial with
  | coprime certificate =>
      exact (not_dvd_of_coprime input certificate divides).elim
  | shared branch =>
      simp [canonicalEventValue, split]

/-- A polynomial that is nonnegative at every rational parameter remains
nonnegative in the event's canonical oracle.  The coprime branch is evaluated
at its displayed rational sample, while the shared branch receives zero. -/
theorem canonicalEventValue_nonneg_of_eval_nonneg
    {event : RatPolynomial} (input : SquarefreeInput event)
    (polynomial : RatPolynomial) (sample : ℚ)
    (nonnegative : ∀ t : ℚ, 0 ≤ polynomial.eval t) :
    0 ≤ canonicalEventValue input polynomial sample := by
  cases split : splitCondition input polynomial with
  | coprime certificate =>
      simpa [canonicalEventValue, split] using nonnegative sample
  | shared branch =>
      simp [canonicalEventValue, split]

private theorem not_shared_of_coprime
    {p q : RatPolynomial} (input : SquarefreeInput p)
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q)
    (branch : SharedFactorBranch p q input) : False := by
  have unit := certificate.isCoprime.isUnit_of_dvd'
    (FTA.DenseGCD.gcd_toPolynomial_dvd_left p q)
    (FTA.DenseGCD.gcd_toPolynomial_dvd_right p q)
  have degree := Polynomial.natDegree_eq_zero_of_isUnit unit
  rw [natDegree_toPolynomial branch.sharedInput.nonzero] at degree
  exact branch.sharedNonconstant degree

/-- The position-dependent samples used by `eventValues` have exactly the
same six sign-test outcomes as a canonical value depending only on the
condition polynomial.  Consequently repeated occurrences of one atom
polynomial cannot acquire inconsistent formal signs. -/
theorem eventValues_canonical
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent) :
    List.Forall₂
      (fun polynomial value => ∀ test : SignTest,
        test.Holds value ↔ test.Holds
          (canonicalEventValue input polynomial
            result.refined.interval.lower))
      conditions (eventValues parent relations result) := by
  induction relations with
  | nil => exact .nil
  | @cons q conditions relation tail inductionHypothesis =>
      cases relation with
      | equality divides =>
          cases split : splitCondition input q with
          | coprime certificate =>
              exact (not_dvd_of_coprime input certificate divides).elim
          | shared branch =>
              exact .cons (by
                intro test
                simp [canonicalEventValue, split])
                (inductionHypothesis result)
      | coprime certificate =>
          let condition : CoprimeCondition p :=
            { polynomial := q, coprime := certificate }
          have member : condition ∈
              (ConditionRelations.cons (.coprime certificate)
                tail).coprimeConditions := by
            simp [ConditionRelations.coprimeConditions, condition]
          let sign := result.signs condition member
          cases split : splitCondition input q with
          | coprime computed =>
              exact .cons (by
                intro test
                rw [canonicalEventValue, split]
                exact (PolynomialStatus.strict sign).holds_iff test
                  sign.lowerLe sign.leUpper le_rfl result.refined.proper.le)
                (inductionHypothesis
                  (FTA.CCLIntersectionEventDecision.CommonEventSigns.dropHead
                    result))
          | shared branch =>
              exact (not_shared_of_coprime input certificate branch).elim

/-- A classified condition has the same sign-test outcome at the canonical
left endpoint and at every rational parameter in the common refined
interval.  Equality relations are identically zero on the event factor;
coprime relations use their retained strict sign certificate. -/
theorem ConditionRelations.canonicalEventValue_holds_iff_between
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q : RatPolynomial} (member : q ∈ conditions)
    (test : SignTest) {t : ℚ}
    (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    test.Holds (canonicalEventValue input q
        result.refined.interval.lower) ↔
      test.Holds (canonicalEventValue input q t) := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons q conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides =>
            rw [canonicalEventValue_eq_zero_of_dvd input q
              result.refined.interval.lower divides,
              canonicalEventValue_eq_zero_of_dvd input q t divides]
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let sign := result.signs condition conditionMember
            cases split : splitCondition input q with
            | coprime computed =>
                have atLower := (PolynomialStatus.strict sign).holds_iff test
                  sign.lowerLe sign.leUpper le_rfl result.refined.proper.le
                have atTarget := (PolynomialStatus.strict sign).holds_iff test
                  sign.lowerLe sign.leUpper lower upper
                simpa only [canonicalEventValue, split] using
                  atLower.symm.trans atTarget
            | shared branch =>
                exact (not_shared_of_coprime input certificate branch).elim
      · cases relation with
        | equality divides =>
            exact inductionHypothesis result tailMember lower upper
        | coprime certificate =>
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            have tailLower : tailResult.refined.interval.lower ≤ t := by
              simpa [tailResult, CommonEventSigns.dropHead] using lower
            have tailUpper : t ≤ tailResult.refined.interval.upper := by
              simpa [tailResult, CommonEventSigns.dropHead] using upper
            simpa [tailResult, CommonEventSigns.dropHead] using
              inductionHypothesis tailResult tailMember tailLower
                tailUpper

/-- Restricting a fully classified event to a squarefree divisor preserves
every listed sign-test outcome at any sample that remains in the original
common sign interval.  Equality divisibility composes with the divisor;
coprimality restricts to the divisor and keeps the original strict sign. -/
theorem ConditionRelations.canonicalEventValue_holds_iff_ofDvd_between
    {p subfactor : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    (subfactorInput : SquarefreeInput subfactor)
    (divides : subfactor.toPolynomial ∣ p.toPolynomial)
    {q : RatPolynomial} (member : q ∈ conditions)
    (test : SignTest) {t : ℚ}
    (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    test.Holds (canonicalEventValue input q
        result.refined.interval.lower) ↔
      test.Holds (canonicalEventValue subfactorInput q t) := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons q conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality conditionDivides =>
            rw [canonicalEventValue_eq_zero_of_dvd input q
              result.refined.interval.lower conditionDivides,
              canonicalEventValue_eq_zero_of_dvd subfactorInput q t
                (divides.trans conditionDivides)]
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let sign := result.signs condition conditionMember
            let subfactorCertificate :=
              FTA.DenseSquarefree.certificateOfIsCoprime subfactor q
                subfactorInput.nonzero
              (certificate.isCoprime.of_isCoprime_of_dvd_left divides)
            cases originalSplit : splitCondition input q with
            | coprime computed =>
                cases subfactorSplit : splitCondition subfactorInput q with
                | coprime subfactorComputed =>
                    have atLower :=
                      (PolynomialStatus.strict sign).holds_iff test
                        sign.lowerLe sign.leUpper le_rfl
                          result.refined.proper.le
                    have atTarget :=
                      (PolynomialStatus.strict sign).holds_iff test
                        sign.lowerLe sign.leUpper lower upper
                    simpa only [canonicalEventValue, originalSplit,
                      subfactorSplit] using atLower.symm.trans atTarget
                | shared branch =>
                    exact (not_shared_of_coprime subfactorInput
                      subfactorCertificate branch).elim
            | shared branch =>
                exact (not_shared_of_coprime input certificate branch).elim
      · cases relation with
        | equality conditionDivides =>
            exact inductionHypothesis result tailMember lower upper
        | coprime certificate =>
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            have tailLower : tailResult.refined.interval.lower ≤ t := by
              simpa [tailResult, CommonEventSigns.dropHead] using lower
            have tailUpper : t ≤ tailResult.refined.interval.upper := by
              simpa [tailResult, CommonEventSigns.dropHead] using upper
            simpa [tailResult, CommonEventSigns.dropHead] using
              inductionHypothesis tailResult tailMember tailLower tailUpper

/-- A condition has canonical value zero exactly on the equality side of the
classified event branch.  The useful direction here exposes the divisibility
certificate needed by quantitative rational approximations. -/
theorem ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q : RatPolynomial} (member : q ∈ conditions)
    (zero : canonicalEventValue input q
      result.refined.interval.lower = 0) :
    p.toPolynomial ∣ q.toPolynomial := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons _ conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides => exact divides
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let sign := result.signs condition conditionMember
            cases split : splitCondition input q with
            | coprime computed =>
                have nonzero := sign.eval_ne_zero le_rfl
                  result.refined.proper.le
                rw [canonicalEventValue, split] at zero
                exact (nonzero zero).elim
            | shared branch =>
                exact (not_shared_of_coprime input certificate branch).elim
      · cases relation with
        | equality divides =>
            exact inductionHypothesis result tailMember zero
        | coprime certificate =>
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            apply inductionHypothesis tailResult tailMember
            simpa [tailResult, CommonEventSigns.dropHead] using zero

/-- The same equality/divisibility conclusion at any rational parameter in
the common refined sign interval.  This is needed after a further independent
condition family has narrowed the event cell. -/
theorem ConditionRelations.dvd_of_canonicalEventValue_eq_zero_between
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q : RatPolynomial} (member : q ∈ conditions)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper)
    (zero : canonicalEventValue input q t = 0) :
    p.toPolynomial ∣ q.toPolynomial := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons _ conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides => exact divides
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let sign := result.signs condition conditionMember
            cases split : splitCondition input q with
            | coprime computed =>
                have nonzero := sign.eval_ne_zero lower upper
                rw [canonicalEventValue, split] at zero
                exact (nonzero zero).elim
            | shared branch =>
                exact (not_shared_of_coprime input certificate branch).elim
      · cases relation with
        | equality divides =>
            exact inductionHypothesis result tailMember lower upper zero
        | coprime certificate =>
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            have tailLower : tailResult.refined.interval.lower ≤ t := by
              simpa [tailResult, CommonEventSigns.dropHead] using lower
            have tailUpper : t ≤ tailResult.refined.interval.upper := by
              simpa [tailResult, CommonEventSigns.dropHead] using upper
            exact inductionHypothesis tailResult tailMember tailLower
              tailUpper zero

/-- Every canonically strict condition keeps that exact sign throughout the
common refined event interval. -/
theorem ConditionRelations.canonicalEventValue_mul_eval_pos
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q : RatPolynomial} (member : q ∈ conditions)
    (canonicalNonzero : canonicalEventValue input q
      result.refined.interval.lower ≠ 0)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    0 < canonicalEventValue input q result.refined.interval.lower * q.eval t := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons _ conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides =>
            cases split : splitCondition input q with
            | coprime certificate =>
                exact (not_dvd_of_coprime input certificate divides).elim
            | shared branch =>
                exact (canonicalNonzero (by
                  simp [canonicalEventValue, split])).elim
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            have conditionMember : condition ∈
                (ConditionRelations.cons (.coprime certificate)
                  tail).coprimeConditions := by
              simp [ConditionRelations.coprimeConditions, condition]
            let sign := result.signs condition conditionMember
            cases split : splitCondition input q with
            | coprime computed =>
                rw [canonicalEventValue, split]
                exact sign.eval_mul_pos_between le_rfl
                  result.refined.proper.le lower upper
            | shared branch =>
                exact (not_shared_of_coprime input certificate branch).elim
      · cases relation with
        | equality divides =>
            exact inductionHypothesis result tailMember canonicalNonzero
              lower upper
        | coprime certificate =>
            let tailResult :
                CommonEventSigns input tail.coprimeConditions parent :=
              CommonEventSigns.dropHead result
            have tailNonzero : canonicalEventValue input q
                tailResult.refined.interval.lower ≠ 0 := by
              simpa [tailResult, CommonEventSigns.dropHead] using
                canonicalNonzero
            have tailLower : tailResult.refined.interval.lower ≤ t := by
              simpa [tailResult, CommonEventSigns.dropHead] using lower
            have tailUpper : t ≤ tailResult.refined.interval.upper := by
              simpa [tailResult, CommonEventSigns.dropHead] using upper
            simpa [tailResult, CommonEventSigns.dropHead] using
              inductionHypothesis tailResult tailMember tailNonzero
                tailLower tailUpper

/-- Two listed conditions that are exact polynomial negatives receive
opposite strict canonical signs.  This is proved through their common sign
interval rather than by depending on the implementation of `splitCondition`.
-/
theorem ConditionRelations.canonicalEventValue_pos_of_polynomial_neg
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q opposite : RatPolynomial} (qMember : q ∈ conditions)
    (oppositeMember : opposite ∈ conditions)
    (polynomialNeg : opposite.toPolynomial = -q.toPolynomial)
    (negative : canonicalEventValue input q
      result.refined.interval.lower < 0) :
    0 < canonicalEventValue input opposite
      result.refined.interval.lower := by
  have qProduct :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
      relations parent result qMember negative.ne
      (t := result.refined.interval.lower) le_rfl result.refined.proper.le
  have qEvalNegative : q.eval result.refined.interval.lower < 0 := by
    nlinarith
  have oppositeCanonicalNonzero : canonicalEventValue input opposite
      result.refined.interval.lower ≠ 0 := by
    intro oppositeZero
    have oppositeDivides :=
      FTA.CCLBranchEventOwner.ConditionRelations.dvd_of_canonicalEventValue_eq_zero
        relations parent result oppositeMember oppositeZero
    have qDivides : p.toPolynomial ∣ q.toPolynomial := by
      rw [polynomialNeg, dvd_neg] at oppositeDivides
      exact oppositeDivides
    have qZero := canonicalEventValue_eq_zero_of_dvd input q
      result.refined.interval.lower qDivides
    linarith
  have oppositeProduct :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
      relations parent result oppositeMember oppositeCanonicalNonzero
      (t := result.refined.interval.lower) le_rfl result.refined.proper.le
  have oppositeEvalPositive :
      0 < opposite.eval result.refined.interval.lower := by
    calc
      0 < -q.eval result.refined.interval.lower := neg_pos.mpr qEvalNegative
      _ = opposite.eval result.refined.interval.lower := by
        rw [← DensePolynomial.eval_toPolynomial opposite,
          polynomialNeg, Polynomial.eval_neg,
          DensePolynomial.eval_toPolynomial q]
  nlinarith

/-- A canonically nonzero condition is one of the genuinely coprime
conditions retained by the branch classifier.  This proposition-valued
lookup keeps proof elimination separate from the computed sign data. -/
theorem ConditionRelations.exists_coprimeCondition_of_canonical_ne
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions) (sample : ℚ)
    {q : RatPolynomial} (member : q ∈ conditions)
    (canonicalNonzero : canonicalEventValue input q sample ≠ 0) :
    ∃ condition ∈ relations.coprimeConditions,
      condition.polynomial = q := by
  induction relations generalizing q with
  | nil => simp at member
  | @cons _ conditions relation tail inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · cases relation with
        | equality divides =>
            cases split : splitCondition input q with
            | coprime certificate =>
                exact (not_dvd_of_coprime input certificate divides).elim
            | shared branch =>
                exact (canonicalNonzero (by
                  simp [canonicalEventValue, split])).elim
        | coprime certificate =>
            let condition : CoprimeCondition p :=
              { polynomial := q, coprime := certificate }
            exact ⟨condition, by
              simp [ConditionRelations.coprimeConditions, condition], rfl⟩
      · cases relation with
        | equality divides =>
            exact inductionHypothesis tailMember canonicalNonzero
        | coprime certificate =>
            rcases inductionHypothesis tailMember canonicalNonzero with
              ⟨condition, conditionMember, polynomial⟩
            exact ⟨condition, List.mem_cons_of_mem _ conditionMember,
              polynomial⟩

/-- A canonically nonzero listed condition can be cancelled from a product
which is divisible by the represented event factor.  The remaining factor
therefore receives canonical value zero. -/
theorem ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_left
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions) (sample : ℚ)
    {q r : RatPolynomial} (qMember : q ∈ conditions)
    (qNonzero : canonicalEventValue input q sample ≠ 0)
    (divides : p.toPolynomial ∣ q.toPolynomial * r.toPolynomial) :
    canonicalEventValue input r sample = 0 := by
  rcases FTA.CCLBranchEventOwner.ConditionRelations.exists_coprimeCondition_of_canonical_ne
      relations sample qMember qNonzero with
    ⟨condition, _conditionMember, polynomial⟩
  have factorDivides : p.toPolynomial ∣ r.toPolynomial := by
    subst q
    exact condition.coprime.isCoprime.dvd_of_dvd_mul_left divides
  exact canonicalEventValue_eq_zero_of_dvd input r sample factorDivides

/-- Right-factor form of canonical cancellation, avoiding any normalization
of a potentially large polynomial product. -/
theorem ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_right
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions) (sample : ℚ)
    {q r : RatPolynomial} (qMember : q ∈ conditions)
    (qNonzero : canonicalEventValue input q sample ≠ 0)
    (divides : p.toPolynomial ∣ r.toPolynomial * q.toPolynomial) :
    canonicalEventValue input r sample = 0 := by
  rcases FTA.CCLBranchEventOwner.ConditionRelations.exists_coprimeCondition_of_canonical_ne
      relations sample qMember qNonzero with
    ⟨condition, _conditionMember, polynomial⟩
  have factorDivides : p.toPolynomial ∣ r.toPolynomial := by
    subst q
    exact condition.coprime.isCoprime.dvd_of_dvd_mul_right divides
  exact canonicalEventValue_eq_zero_of_dvd input r sample factorDivides

/-- One positive rational margin simultaneously valid for every coprime
condition on the commonly refined event interval. -/
def ConditionRelations.strictMargin
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent) : ℚ :=
  FTA.Maximality.positiveMinimum
    (relations.coprimeConditions.attach.map fun condition =>
      (result.signs condition.1 condition.2).absMargin)

theorem ConditionRelations.strictMargin_pos
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent) :
    0 < FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      relations parent result := by
  apply FTA.Maximality.positiveMinimum_pos
  intro margin marginMember
  rw [List.mem_map] at marginMember
  rcases marginMember with ⟨condition, conditionMember, rfl⟩
  exact (result.signs condition.1 condition.2).absMargin_pos

/-- The common strict margin lower-bounds the absolute value of every
canonically nonzero classified condition throughout the refined interval. -/
theorem ConditionRelations.strictMargin_le_abs_eval
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q : RatPolynomial} (member : q ∈ conditions)
    (canonicalNonzero : canonicalEventValue input q
      result.refined.interval.lower ≠ 0)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      relations parent result ≤ |q.eval t| := by
  rcases FTA.CCLBranchEventOwner.ConditionRelations.exists_coprimeCondition_of_canonical_ne
      relations result.refined.interval.lower member canonicalNonzero with
    ⟨condition, conditionMember, polynomial⟩
  let attached : {condition // condition ∈ relations.coprimeConditions} :=
    ⟨condition, conditionMember⟩
  have marginLe : FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      relations parent result ≤
      (result.signs condition conditionMember).absMargin := by
    apply FTA.Maximality.positiveMinimum_le_of_mem
    exact List.mem_map.mpr ⟨attached, List.mem_attach _ attached,
      by simp only [attached]⟩
  subst q
  exact marginLe.trans
    ((result.signs condition conditionMember).absMargin_le_abs_eval lower upper)

/-- If an event factor divides a sum of two products, the four canonical
signs cannot make both products strictly positive.  Otherwise the common
strict margin gives that multiple a forbidden uniform positive lower bound. -/
theorem ConditionRelations.not_both_canonical_products_pos_of_dvd_sum
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {a b c d : RatPolynomial}
    (aMember : a ∈ conditions) (bMember : b ∈ conditions)
    (cMember : c ∈ conditions) (dMember : d ∈ conditions)
    (divides : p.toPolynomial ∣ (a * b + c * d).toPolynomial)
    (firstPositive : 0 <
      canonicalEventValue input a result.refined.interval.lower *
        canonicalEventValue input b result.refined.interval.lower)
    (secondPositive : 0 <
      canonicalEventValue input c result.refined.interval.lower *
        canonicalEventValue input d result.refined.interval.lower) :
    False := by
  let margin := FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
    relations parent result
  have marginPositive : 0 < margin :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      relations parent result
  have aNonzero : canonicalEventValue input a
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at firstPositive
    exact (lt_irrefl 0 firstPositive).elim
  have bNonzero : canonicalEventValue input b
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at firstPositive
    exact (lt_irrefl 0 firstPositive).elim
  have cNonzero : canonicalEventValue input c
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at secondPositive
    exact (lt_irrefl 0 secondPositive).elim
  have dNonzero : canonicalEventValue input d
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at secondPositive
    exact (lt_irrefl 0 secondPositive).elim
  let certificate : FTA.PositiveLowerBound.Certificate
      (a * b + c * d) result.refined.interval :=
    { bound := (2 * margin ^ 2) ^ 2
      positive := sq_pos_of_pos (mul_pos (by norm_num)
        (sq_pos_of_pos marginPositive))
      lower := by
        intro t lower upper
        have aProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result aMember aNonzero lower upper
        have bProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result bMember bNonzero lower upper
        have cProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result cMember cNonzero lower upper
        have dProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result dMember dNonzero lower upper
        have abPositive : 0 < a.eval t * b.eval t := by
          nlinarith [mul_pos aProduct bProduct]
        have cdPositive : 0 < c.eval t * d.eval t := by
          nlinarith [mul_pos cProduct dProduct]
        have marginA :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result aMember aNonzero lower upper
        have marginB :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result bMember bNonzero lower upper
        have marginC :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result cMember cNonzero lower upper
        have marginD :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result dMember dNonzero lower upper
        have marginAB : margin ^ 2 ≤ a.eval t * b.eval t := by
          calc
            margin ^ 2 = margin * margin := by ring
            _ ≤ |a.eval t| * |b.eval t| :=
              mul_le_mul marginA marginB marginPositive.le
                (abs_nonneg (a.eval t))
            _ = |a.eval t * b.eval t| := (abs_mul _ _).symm
            _ = a.eval t * b.eval t := abs_of_pos abPositive
        have marginCD : margin ^ 2 ≤ c.eval t * d.eval t := by
          calc
            margin ^ 2 = margin * margin := by ring
            _ ≤ |c.eval t| * |d.eval t| :=
              mul_le_mul marginC marginD marginPositive.le
                (abs_nonneg (c.eval t))
            _ = |c.eval t * d.eval t| := (abs_mul _ _).symm
            _ = c.eval t * d.eval t := abs_of_pos cdPositive
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
        nlinarith [sq_nonneg (a.eval t * b.eval t + c.eval t * d.eval t)] }
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    input result.refined divides certificate

/-- If an event factor divides a sum of two products, the four canonical
signs likewise cannot make both products strictly negative.  Squaring the
uniform negative separation gives the same forbidden positive lower bound. -/
theorem ConditionRelations.not_both_canonical_products_neg_of_dvd_sum
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {a b c d : RatPolynomial}
    (aMember : a ∈ conditions) (bMember : b ∈ conditions)
    (cMember : c ∈ conditions) (dMember : d ∈ conditions)
    (divides : p.toPolynomial ∣ (a * b + c * d).toPolynomial)
    (firstNegative :
      canonicalEventValue input a result.refined.interval.lower *
        canonicalEventValue input b result.refined.interval.lower < 0)
    (secondNegative :
      canonicalEventValue input c result.refined.interval.lower *
        canonicalEventValue input d result.refined.interval.lower < 0) :
    False := by
  let margin := FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
    relations parent result
  have marginPositive : 0 < margin :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      relations parent result
  have aNonzero : canonicalEventValue input a
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at firstNegative
    exact (lt_irrefl 0 firstNegative).elim
  have bNonzero : canonicalEventValue input b
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at firstNegative
    exact (lt_irrefl 0 firstNegative).elim
  have cNonzero : canonicalEventValue input c
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at secondNegative
    exact (lt_irrefl 0 secondNegative).elim
  have dNonzero : canonicalEventValue input d
      result.refined.interval.lower ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at secondNegative
    exact (lt_irrefl 0 secondNegative).elim
  let certificate : FTA.PositiveLowerBound.Certificate
      (a * b + c * d) result.refined.interval :=
    { bound := (2 * margin ^ 2) ^ 2
      positive := sq_pos_of_pos (mul_pos (by norm_num)
        (sq_pos_of_pos marginPositive))
      lower := by
        intro t lower upper
        have aProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result aMember aNonzero lower upper
        have bProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result bMember bNonzero lower upper
        have cProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result cMember cNonzero lower upper
        have dProduct :=
          FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
            relations parent result dMember dNonzero lower upper
        have abNegative : a.eval t * b.eval t < 0 := by
          nlinarith [mul_pos aProduct bProduct]
        have cdNegative : c.eval t * d.eval t < 0 := by
          nlinarith [mul_pos cProduct dProduct]
        have marginA :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result aMember aNonzero lower upper
        have marginB :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result bMember bNonzero lower upper
        have marginC :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result cMember cNonzero lower upper
        have marginD :=
          FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
            relations parent result dMember dNonzero lower upper
        have marginAB : margin ^ 2 ≤ -(a.eval t * b.eval t) := by
          calc
            margin ^ 2 = margin * margin := by ring
            _ ≤ |a.eval t| * |b.eval t| :=
              mul_le_mul marginA marginB marginPositive.le
                (abs_nonneg (a.eval t))
            _ = |a.eval t * b.eval t| := (abs_mul _ _).symm
            _ = -(a.eval t * b.eval t) := abs_of_neg abNegative
        have marginCD : margin ^ 2 ≤ -(c.eval t * d.eval t) := by
          calc
            margin ^ 2 = margin * margin := by ring
            _ ≤ |c.eval t| * |d.eval t| :=
              mul_le_mul marginC marginD marginPositive.le
                (abs_nonneg (c.eval t))
            _ = |c.eval t * d.eval t| := (abs_mul _ _).symm
            _ = -(c.eval t * d.eval t) := abs_of_neg cdNegative
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
        nlinarith [sq_nonneg
          (a.eval t * b.eval t + c.eval t * d.eval t)] }
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    input result.refined divides certificate

/-- Canonical positivity is preserved by a positive scalar congruence modulo
the represented event factor.  A further rational count-one approximation
makes the divisible error smaller than the common strict sign margin. -/
theorem ConditionRelations.canonicalEventValue_pos_of_positive_scale_mod
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {q r error : RatPolynomial}
    (qMember : q ∈ conditions) (rMember : r ∈ conditions)
    (scale : ℚ) (scalePositive : 0 < scale)
    (identity : r.toPolynomial =
      Polynomial.C scale * q.toPolynomial + error.toPolynomial)
    (errorDivides : p.toPolynomial ∣ error.toPolynomial)
    (qPositive : 0 < canonicalEventValue input q
      result.refined.interval.lower) :
    0 < canonicalEventValue input r result.refined.interval.lower := by
  have qNonzero : canonicalEventValue input q
      result.refined.interval.lower ≠ 0 := qPositive.ne'
  have rNonzero : canonicalEventValue input r
      result.refined.interval.lower ≠ 0 := by
    intro rZero
    have rDivides :=
      FTA.CCLBranchEventOwner.ConditionRelations.dvd_of_canonicalEventValue_eq_zero
        relations parent result rMember rZero
    have scaledQDivides : p.toPolynomial ∣
        Polynomial.C scale * q.toPolynomial := by
      have difference := dvd_sub rDivides errorDivides
      rw [identity] at difference
      simpa using difference
    have scalarUnit : IsUnit (Polynomial.C scale) :=
      Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr scalePositive.ne')
    have qDivides : p.toPolynomial ∣ q.toPolynomial :=
      scalarUnit.dvd_mul_left.mp scaledQDivides
    have qZero := canonicalEventValue_eq_zero_of_dvd input q
      result.refined.interval.lower qDivides
    exact qNonzero qZero
  let margin := FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
    relations parent result
  let coefficient := FTA.RootCountDivisibility.approximationCoefficient
    error p result.refined
  let majorant := max 1 coefficient
  let epsilon := scale * margin / (2 * majorant)
  have marginPositive : 0 < margin :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      relations parent result
  have coefficientNonnegative : 0 ≤ coefficient :=
    FTA.RootCountDivisibility.approximationCoefficient_nonneg
      error p result.refined
  have majorantPositive : 0 < majorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have coefficientLeMajorant : coefficient ≤ majorant := le_max_right _ _
  have epsilonPositive : 0 < epsilon :=
    div_pos (mul_pos scalePositive marginPositive)
      (mul_pos (by norm_num) majorantPositive)
  let approximation := FTA.RootCountDivisibility.approximateMultiple input
    errorDivides result.refined epsilon epsilonPositive
  have qProduct :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
      relations parent result qMember qNonzero approximation.lower
      approximation.upper
  have qEvalPositive : 0 < q.eval approximation.parameter := by
    nlinarith
  have marginQ :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
      relations parent result qMember qNonzero approximation.lower
      approximation.upper
  have marginLeQ : margin ≤ q.eval approximation.parameter := by
    simpa [abs_of_pos qEvalPositive] using marginQ
  have scaled : coefficient * epsilon ≤ scale * margin / 2 := by
    unfold epsilon
    apply (mul_le_mul_of_nonneg_right coefficientLeMajorant
      (div_nonneg (mul_pos scalePositive marginPositive).le
        (mul_pos (by norm_num) majorantPositive).le)).trans_eq
    field_simp
  have errorSmall : |error.eval approximation.parameter| ≤
      scale * margin / 2 := by
    apply approximation.smallValue.trans
    rw [FTA.RootCountDivisibility.approximationBound_eq_coefficient_mul]
    exact scaled
  have evalIdentity : r.eval approximation.parameter =
      scale * q.eval approximation.parameter +
        error.eval approximation.parameter := by
    rw [← DensePolynomial.eval_toPolynomial r, identity,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      DensePolynomial.eval_toPolynomial q,
      DensePolynomial.eval_toPolynomial error]
  have rEvalPositive : 0 < r.eval approximation.parameter := by
    have errorLower := neg_abs_le (error.eval approximation.parameter)
    nlinarith
  have rProduct :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
      relations parent result rMember rNonzero approximation.lower
      approximation.upper
  nlinarith

/-- Every surrogate value has the same result as the corresponding event
polynomial for all six parser sign tests. -/
theorem eventValues_correct
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations p conditions)
    (parent : CountOneInterval p)
    (result : CommonEventSigns input relations.coprimeConditions parent)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper)
    (eventZero : p.eval t = 0) :
    List.Forall₂
      (fun polynomial value => ∀ test : SignTest,
        test.Holds value ↔ test.Holds (polynomial.eval t))
      conditions (eventValues parent relations result) := by
  induction relations with
  | nil => exact .nil
  | @cons q conditions relation tail inductionHypothesis =>
      cases relation with
      | equality divides =>
          let relation : ConditionRelation p q := .equality divides
          have conditionZero : q.eval t = 0 :=
            relation.eval_eq_zero_of_isEquality eventZero rfl
          exact .cons (by
            intro test
            rw [conditionZero])
            (inductionHypothesis result lower upper)
      | coprime certificate =>
          let condition : CoprimeCondition p :=
            { polynomial := q, coprime := certificate }
          have member : condition ∈
              (ConditionRelations.cons (.coprime certificate)
                tail).coprimeConditions := by
            simp [ConditionRelations.coprimeConditions, condition]
          let sign := result.signs condition member
          have headCorrect : ∀ test : SignTest,
              test.Holds (q.eval sign.sample) ↔ test.Holds (q.eval t) := by
            intro test
            exact (PolynomialStatus.strict sign).holds_iff test
              sign.lowerLe sign.leUpper lower upper
          exact .cons headCorrect
            (inductionHypothesis
              (FTA.CCLIntersectionEventDecision.CommonEventSigns.dropHead result)
              lower upper)

/-- Cleared atom polynomials in precisely the order consumed by the formula
syntax tree. -/
def eventFormulaPolynomials (formula : Formula) (path : ProjectivePath.Path) :
    List RatPolynomial :=
  (formulaAtoms formula).map fun atom => clearedForm atom.form path

/-- A formula evaluator that consumes one rational value for each atom and
returns the unused suffix.  The empty atom case is only a totality default;
the correctness theorem supplies an exactly aligned value list. -/
def consumeAtomValues : Formula → List ℚ → Bool × List ℚ
  | .truth, values => (true, values)
  | .falsity, values => (false, values)
  | .atom atom, [] => (decide (atom.sign.Holds 0), [])
  | .atom atom, value :: values => (decide (atom.sign.Holds value), values)
  | .and left right, values =>
      let leftResult := consumeAtomValues left values
      let rightResult := consumeAtomValues right leftResult.2
      (leftResult.1 && rightResult.1, rightResult.2)
  | .or left right, values =>
      let leftResult := consumeAtomValues left values
      let rightResult := consumeAtomValues right leftResult.2
      (leftResult.1 || rightResult.1, rightResult.2)

def evalAtomValues (formula : Formula) (values : List ℚ) : Bool :=
  (consumeAtomValues formula values).1

/-- Structural formula evaluation through an arbitrary rational value oracle
for Hermitian forms. -/
def formulaEvalWith : Formula → (HermitianForm → ℚ) → Bool
  | .truth, _ => true
  | .falsity, _ => false
  | .atom atom, value => decide (atom.sign.Holds (value atom.form))
  | .and left right, value =>
      formulaEvalWith left value && formulaEvalWith right value
  | .or left right, value =>
      formulaEvalWith left value || formulaEvalWith right value

private def AtomValueMatches
    (value : HermitianForm → ℚ) (atom : Atom) (sample : ℚ) : Prop :=
  atom.sign.Holds sample ↔ atom.sign.Holds (value atom.form)

private def AtomValueCorrect
    (path : ProjectivePath.Path) (t : ℚ) (atom : Atom) (value : ℚ) : Prop :=
  atom.sign.Holds value ↔ atomPathHolds atom path t

private theorem atomValues_correct_of_polynomials
    (path : ProjectivePath.Path) (t : ℚ)
    {atoms : List Atom} {values : List ℚ}
    (correct : List.Forall₂
      (fun polynomial value => ∀ test : SignTest,
        test.Holds value ↔ test.Holds (polynomial.eval t))
      (atoms.map fun atom => clearedForm atom.form path) values) :
    List.Forall₂ (AtomValueCorrect path t) atoms values := by
  rw [List.forall₂_map_left_iff] at correct
  exact correct.imp (by
    intro atom value head
    simpa [AtomValueCorrect, atomPathHolds] using head atom.sign)

/-- Consuming an aligned surrogate list produces the ordinary cleared-path
Boolean and leaves an arbitrary trailing list untouched. -/
theorem consumeAtomValues_correct
    (formula : Formula) (path : ProjectivePath.Path) (t : ℚ)
    {values : List ℚ}
    (correct : List.Forall₂ (AtomValueCorrect path t)
      (formulaAtoms formula) values) (suffix : List ℚ) :
    consumeAtomValues formula (values ++ suffix) =
      (pathEvalBool formula path t, suffix) := by
  induction formula generalizing values suffix with
  | truth =>
      cases correct
      rfl
  | falsity =>
      cases correct
      rfl
  | atom atom =>
      cases correct with
      | cons head tail =>
          cases tail
          have check : decide (atom.sign.Holds _ ) =
              decide (atomPathHolds atom path t) :=
            Bool.decide_congr head
          simp [consumeAtomValues, pathEvalBool, check]
  | and left right leftInduction rightInduction =>
      let leftCount := (formulaAtoms left).length
      let leftValues := values.take leftCount
      let rightValues := values.drop leftCount
      have leftCorrect : List.Forall₂ (AtomValueCorrect path t)
          (formulaAtoms left) leftValues := by
        have taken := List.forall₂_take leftCount correct
        simpa [leftCount, leftValues, formulaAtoms] using taken
      have rightCorrect : List.Forall₂ (AtomValueCorrect path t)
          (formulaAtoms right) rightValues := by
        have dropped := List.forall₂_drop leftCount correct
        simpa [leftCount, rightValues, formulaAtoms] using dropped
      have valuesIdentity : values = leftValues ++ rightValues := by
        simp [leftValues, rightValues]
      rw [valuesIdentity, List.append_assoc]
      simp only [consumeAtomValues]
      rw [leftInduction leftCorrect (rightValues ++ suffix),
        rightInduction rightCorrect suffix]
      rfl
  | or left right leftInduction rightInduction =>
      let leftCount := (formulaAtoms left).length
      let leftValues := values.take leftCount
      let rightValues := values.drop leftCount
      have leftCorrect : List.Forall₂ (AtomValueCorrect path t)
          (formulaAtoms left) leftValues := by
        have taken := List.forall₂_take leftCount correct
        simpa [leftCount, leftValues, formulaAtoms] using taken
      have rightCorrect : List.Forall₂ (AtomValueCorrect path t)
          (formulaAtoms right) rightValues := by
        have dropped := List.forall₂_drop leftCount correct
        simpa [leftCount, rightValues, formulaAtoms] using dropped
      have valuesIdentity : values = leftValues ++ rightValues := by
        simp [leftValues, rightValues]
      rw [valuesIdentity, List.append_assoc]
      simp only [consumeAtomValues]
      rw [leftInduction leftCorrect (rightValues ++ suffix),
        rightInduction rightCorrect suffix]
      rfl

/-- Consuming values that match a form oracle produces its structural Boolean
evaluation and leaves an arbitrary trailing list untouched. -/
theorem consumeAtomValues_matches
    (formula : Formula) (value : HermitianForm → ℚ)
    {values : List ℚ}
    (correct : List.Forall₂ (AtomValueMatches value)
      (formulaAtoms formula) values) (suffix : List ℚ) :
    consumeAtomValues formula (values ++ suffix) =
      (formulaEvalWith formula value, suffix) := by
  induction formula generalizing values suffix with
  | truth =>
      cases correct
      rfl
  | falsity =>
      cases correct
      rfl
  | atom atom =>
      cases correct with
      | cons head tail =>
          cases tail
          have check : decide (atom.sign.Holds _) =
              decide (atom.sign.Holds (value atom.form)) :=
            Bool.decide_congr head
          simp [consumeAtomValues, formulaEvalWith, check]
  | and left right leftInduction rightInduction =>
      let leftCount := (formulaAtoms left).length
      let leftValues := values.take leftCount
      let rightValues := values.drop leftCount
      have leftCorrect : List.Forall₂ (AtomValueMatches value)
          (formulaAtoms left) leftValues := by
        have taken := List.forall₂_take leftCount correct
        simpa [leftCount, leftValues, formulaAtoms] using taken
      have rightCorrect : List.Forall₂ (AtomValueMatches value)
          (formulaAtoms right) rightValues := by
        have dropped := List.forall₂_drop leftCount correct
        simpa [leftCount, rightValues, formulaAtoms] using dropped
      have valuesIdentity : values = leftValues ++ rightValues := by
        simp [leftValues, rightValues]
      rw [valuesIdentity, List.append_assoc]
      simp only [consumeAtomValues]
      rw [leftInduction leftCorrect (rightValues ++ suffix),
        rightInduction rightCorrect suffix]
      rfl
  | or left right leftInduction rightInduction =>
      let leftCount := (formulaAtoms left).length
      let leftValues := values.take leftCount
      let rightValues := values.drop leftCount
      have leftCorrect : List.Forall₂ (AtomValueMatches value)
          (formulaAtoms left) leftValues := by
        have taken := List.forall₂_take leftCount correct
        simpa [leftCount, leftValues, formulaAtoms] using taken
      have rightCorrect : List.Forall₂ (AtomValueMatches value)
          (formulaAtoms right) rightValues := by
        have dropped := List.forall₂_drop leftCount correct
        simpa [leftCount, rightValues, formulaAtoms] using dropped
      have valuesIdentity : values = leftValues ++ rightValues := by
        simp [leftValues, rightValues]
      rw [valuesIdentity, List.append_assoc]
      simp only [consumeAtomValues]
      rw [leftInduction leftCorrect (rightValues ++ suffix),
        rightInduction rightCorrect suffix]
      rfl
/-- Finite gcd branches classifying every atom of a parser formula against
one squarefree event factor. -/
def eventFormulaBranches
    {p : RatPolynomial} (input : SquarefreeInput p)
    (formula : Formula) (path : ProjectivePath.Path) :
    List (ClassifiedEventFactor (eventFormulaPolynomials formula path)) :=
  classifyEventConditions input (eventFormulaPolynomials formula path)

theorem eventFormulaBranches_nonempty
    {p : RatPolynomial} (input : SquarefreeInput p)
    (formula : Formula) (path : ProjectivePath.Path) :
    eventFormulaBranches input formula path ≠ [] :=
  classifyEventConditions_nonempty input (eventFormulaPolynomials formula path)

theorem eventFormulaBranches_cover
    {p : RatPolynomial} (input : SquarefreeInput p)
    (formula : Formula) (path : ProjectivePath.Path)
    {t : ℚ} (eventZero : p.eval t = 0) :
    ∃ branch ∈ eventFormulaBranches input formula path,
      branch.factor.polynomial.eval t = 0 :=
  classifyEventConditions_covers input (eventFormulaPolynomials formula path)
    eventZero

/-- Exact formula bit on one fully classified count-one event branch. -/
def eventFormulaCheck
    {formula : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor (eventFormulaPolynomials formula path))
    (parent : CountOneInterval branch.factor.polynomial) : Bool :=
  let signs := branch.computeEventSigns parent
  evalAtomValues formula (eventValues parent branch.relations signs)

/-- Event evaluation factors through the canonical sign oracle: multiples of
the isolated factor are zero, and every other cleared atom is evaluated at
one common rational endpoint. -/
theorem eventFormulaCheck_eq_canonicalEval
    {formula : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor (eventFormulaPolynomials formula path))
    (parent : CountOneInterval branch.factor.polynomial) :
    eventFormulaCheck branch parent =
      formulaEvalWith formula (fun form =>
        canonicalEventValue branch.factor.input (clearedForm form path)
          (branch.computeEventSigns parent).refined.interval.lower) := by
  let signs := branch.computeEventSigns parent
  have polynomialCorrect := eventValues_canonical branch.relations parent signs
  have atomCorrect : List.Forall₂
      (AtomValueMatches fun form =>
        canonicalEventValue branch.factor.input (clearedForm form path)
          signs.refined.interval.lower)
      (formulaAtoms formula) (eventValues parent branch.relations signs) := by
    have polynomialCorrect' : List.Forall₂
        (fun polynomial value => ∀ test : SignTest,
          test.Holds value ↔ test.Holds
            (canonicalEventValue branch.factor.input polynomial
              signs.refined.interval.lower))
        ((formulaAtoms formula).map fun atom => clearedForm atom.form path)
        (eventValues parent branch.relations signs) := by
      simpa only [eventFormulaPolynomials] using polynomialCorrect
    rw [List.forall₂_map_left_iff] at polynomialCorrect'
    exact polynomialCorrect'.imp (by
      intro atom value head
      exact head atom.sign)
  have consumed := consumeAtomValues_matches formula
    (fun form => canonicalEventValue branch.factor.input
      (clearedForm form path) signs.refined.interval.lower)
    atomCorrect []
  simp only [List.append_nil] at consumed
  simpa [eventFormulaCheck, evalAtomValues, signs] using
    congrArg Prod.fst consumed

/-- The computed event bit is exactly the original affine parser formula at
every rational event zero in the shared refined interval. -/
theorem eventFormulaCheck_eq_true_iff
    {formula : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor (eventFormulaPolynomials formula path))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    eventFormulaCheck branch parent = true ↔
      formula.Holds (path.value t) := by
  let signs := branch.computeEventSigns parent
  have polynomialCorrect := eventValues_correct branch.relations parent signs
    lower upper eventZero
  have atomCorrect : List.Forall₂ (AtomValueCorrect path t)
      (formulaAtoms formula)
      (eventValues parent branch.relations signs) :=
    atomValues_correct_of_polynomials path t polynomialCorrect
  have consumed := consumeAtomValues_correct formula path t atomCorrect []
  simp only [List.append_nil] at consumed
  have checkIdentity : eventFormulaCheck branch parent =
      pathEvalBool formula path t := by
    simpa [eventFormulaCheck, evalAtomValues, signs] using
      congrArg Prod.fst consumed
  rw [checkIdentity]
  exact pathEvalBool_eq_true_iff formula path t pathDenominator

/-! ## Two-child event owner decisions -/

/-- Classify both child formulas with one gcd tree.  The conjunction is used
only as an atom-list carrier: its atom order is the left list followed by the
right list. -/
def eventFormulaPairBranches
    {p : RatPolynomial} (input : SquarefreeInput p)
    (left right : Formula) (path : ProjectivePath.Path) :
    List (ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path)) :=
  eventFormulaBranches input (.and left right) path

theorem eventFormulaPairBranches_nonempty
    {p : RatPolynomial} (input : SquarefreeInput p)
    (left right : Formula) (path : ProjectivePath.Path) :
    eventFormulaPairBranches input left right path ≠ [] :=
  eventFormulaBranches_nonempty input (.and left right) path

/-- Parser specialization: classify both proposed next-bit formulas in one
finite gcd tree on the event factor. -/
def inputEventPolynomials
    (state : RawParser.State) (path : ProjectivePath.Path) :
    List RatPolynomial :=
  eventFormulaPolynomials
    (.and (inputAdvanceFormula state false)
      (inputAdvanceFormula state true)) path

def inputEventBranches
    {p : RatPolynomial} (input : SquarefreeInput p)
    (state : RawParser.State) (path : ProjectivePath.Path) :
    List (ClassifiedEventFactor
      (inputEventPolynomials state path)) :=
  eventFormulaPairBranches input (inputAdvanceFormula state false)
    (inputAdvanceFormula state true) path

theorem inputEventBranches_nonempty
    {p : RatPolynomial} (input : SquarefreeInput p)
    (state : RawParser.State) (path : ProjectivePath.Path) :
    inputEventBranches input state path ≠ [] :=
  eventFormulaPairBranches_nonempty input (inputAdvanceFormula state false)
    (inputAdvanceFormula state true) path

/-- The two formula bits computed from one aligned surrogate-value list. -/
def eventFormulaPairCheck
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial) : Bool × Bool :=
  let signs := branch.computeEventSigns parent
  let values := eventValues parent branch.relations signs
  let leftResult := consumeAtomValues left values
  (leftResult.1, evalAtomValues right leftResult.2)

/-- The conjunction of the returned pair is the ordinary combined-formula
event check on the same aligned value list. -/
theorem eventFormulaPairCheck_and_eq
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial) :
    ((eventFormulaPairCheck branch parent).1 &&
        (eventFormulaPairCheck branch parent).2) =
      eventFormulaCheck branch parent := by
  rfl

/-- Thus a two-child event check is interpreted by one coherent canonical
sign oracle even when the isolated event has no rational zero. -/
theorem eventFormulaPairCheck_and_eq_canonicalEval
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial) :
    ((eventFormulaPairCheck branch parent).1 &&
        (eventFormulaPairCheck branch parent).2) =
      formulaEvalWith (.and left right) (fun form =>
        canonicalEventValue branch.factor.input (clearedForm form path)
          (branch.computeEventSigns parent).refined.interval.lower) := by
  rw [eventFormulaPairCheck_and_eq]
  exact eventFormulaCheck_eq_canonicalEval branch parent

/-- The two returned owner bits separately agree with the same canonical
algebraic-event oracle.  Keeping the pair intact gives later controller
adapters access to the selected component without re-expanding the complete
surrogate list. -/
theorem eventFormulaPairCheck_eq_canonicalPair
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial) :
    eventFormulaPairCheck branch parent =
      (formulaEvalWith left (fun form =>
          canonicalEventValue branch.factor.input (clearedForm form path)
            (branch.computeEventSigns parent).refined.interval.lower),
        formulaEvalWith right (fun form =>
          canonicalEventValue branch.factor.input (clearedForm form path)
            (branch.computeEventSigns parent).refined.interval.lower)) := by
  let signs := branch.computeEventSigns parent
  let values := eventValues parent branch.relations signs
  let value : HermitianForm → ℚ := fun form =>
    canonicalEventValue branch.factor.input (clearedForm form path)
      signs.refined.interval.lower
  have polynomialCorrect := eventValues_canonical branch.relations parent signs
  have combinedCorrect : List.Forall₂ (AtomValueMatches value)
      (formulaAtoms (.and left right)) values := by
    have polynomialCorrect' : List.Forall₂
        (fun polynomial sample => ∀ test : SignTest,
          test.Holds sample ↔ test.Holds
            (canonicalEventValue branch.factor.input polynomial
              signs.refined.interval.lower))
        ((formulaAtoms (.and left right)).map fun atom =>
          clearedForm atom.form path) values := by
      simpa only [eventFormulaPolynomials, values] using polynomialCorrect
    rw [List.forall₂_map_left_iff] at polynomialCorrect'
    exact polynomialCorrect'.imp (by
      intro atom sample head
      exact head atom.sign)
  let leftCount := (formulaAtoms left).length
  let leftValues := values.take leftCount
  let rightValues := values.drop leftCount
  have leftCorrect : List.Forall₂ (AtomValueMatches value)
      (formulaAtoms left) leftValues := by
    have taken := List.forall₂_take leftCount combinedCorrect
    simpa [leftCount, leftValues, formulaAtoms] using taken
  have rightCorrect : List.Forall₂ (AtomValueMatches value)
      (formulaAtoms right) rightValues := by
    have dropped := List.forall₂_drop leftCount combinedCorrect
    simpa [leftCount, rightValues, formulaAtoms] using dropped
  have valuesIdentity : values = leftValues ++ rightValues := by
    simp [leftValues, rightValues]
  have leftConsumed := consumeAtomValues_matches left value leftCorrect rightValues
  have rightConsumed := consumeAtomValues_matches right value rightCorrect []
  simp only [List.append_nil] at rightConsumed
  change
    ((consumeAtomValues left values).1,
      evalAtomValues right (consumeAtomValues left values).2) =
        (formulaEvalWith left value, formulaEvalWith right value)
  rw [valuesIdentity, leftConsumed]
  exact congrArg (fun result => (formulaEvalWith left value, result.1))
    rightConsumed

private theorem formulaEvalWith_inputAdvance_initial_ne_both
    (matrix : Mat2 CCL.GaussianRat) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.initial, matrix, history⟩ false) value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.initial, matrix, history⟩ true) value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
    RawParser.step, stateFormula, activeFormula, Formula.pullback,
    formulaEvalWith, Formula.all, SignTest.Holds] at falseCheck trueCheck
  linarith

private theorem formulaEvalWith_inputAdvance_highUnary_ne_both
    (count : ℕ) (matrix : Mat2 CCL.GaussianRat)
    (history : List RawParser.Constraint) (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.highUnary count, matrix, history⟩ false) value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.highUnary count, matrix, history⟩ true) value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
    RawParser.step, stateFormula, activeFormula, radialFormula,
    Formula.pullback, formulaEvalWith, Formula.all,
    normComparisonForm_identity, SignTest.Holds] at falseCheck trueCheck
  linarith

private theorem formulaEvalWith_inputAdvance_lowUnary_ne_both
    (count : ℕ) (matrix : Mat2 CCL.GaussianRat)
    (history : List RawParser.Constraint) (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.lowUnary count, matrix, history⟩ false) value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.lowUnary count, matrix, history⟩ true) value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  cases count with
  | zero =>
      simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
        RawParser.step, stateFormula, activeFormula, radialFormula,
        Formula.pullback, formulaEvalWith, Formula.all,
        normComparisonForm_identity, SignTest.Holds] at falseCheck trueCheck
      linarith
  | succ count =>
      simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
        RawParser.step, stateFormula, activeFormula, radialFormula,
        Formula.pullback, formulaEvalWith, Formula.all,
        normComparisonForm_identity, SignTest.Holds] at falseCheck trueCheck
      linarith

private theorem formulaEvalWith_inputAdvance_loopUnary_ne_both
    (count : ℕ) (matrix : Mat2 CCL.GaussianRat)
    (history : List RawParser.Constraint) (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.loopUnary count, matrix, history⟩ false) value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.loopUnary count, matrix, history⟩ true) value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
    RawParser.step, stateFormula, activeFormula, radialFormula,
    Formula.pullback, formulaEvalWith, Formula.all,
    normComparisonForm_identity, SignTest.Holds] at falseCheck trueCheck
  linarith

private theorem formulaEvalWith_inputAdvance_sector_two_ne_both
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 CCL.GaussianRat) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent (.two first second), matrix, history⟩
            false) value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent (.two first second), matrix, history⟩
            true) value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  cases first <;> cases second <;>
    simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
      sectorFormula, Formula.pullback, formulaEvalWith,
      RawParser.sectorOfBits, SignTest.Holds] at falseCheck trueCheck <;>
    linarith

private theorem formulaEvalWith_inputAdvance_sector_one_ne_both
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (matrix : Mat2 CCL.GaussianRat) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent (.one first), matrix, history⟩ false)
            value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent (.one first), matrix, history⟩ true)
            value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  cases first <;>
    simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
      RawParser.step, stateFormula, activeFormula, sectorBitsFormula,
      Formula.pullback, formulaEvalWith, Formula.all,
    SignTest.Holds] at falseCheck trueCheck <;>
    linarith

private theorem formulaEvalWith_inputAdvance_sector_zero_ne_both
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (matrix : Mat2 CCL.GaussianRat) (history : List RawParser.Constraint)
    (value : HermitianForm → ℚ) :
    ¬(formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent .zero, matrix, history⟩ false)
            value = true ∧
      formulaEvalWith
          (inputAdvanceFormula
            ⟨.sector kind exponent .zero, matrix, history⟩ true)
            value = true) := by
  rintro ⟨falseCheck, trueCheck⟩
  simp [inputAdvanceFormula, CCLNextBitFormula.advanceFormula,
    RawParser.step, stateFormula, activeFormula, sectorBitsFormula,
    Formula.pullback, formulaEvalWith, Formula.all,
    SignTest.Holds] at falseCheck trueCheck
  rcases falseCheck.2.2 with falseFirst | falseSecond
  · rcases trueCheck.2.2.1.1 with realNegative | imagNonpositive
    · linarith [falseFirst.1, realNegative]
    · linarith [falseFirst.2, imagNonpositive]
  · rcases trueCheck.2.2.1.2 with realNonnegative | imagNegative
    · linarith [falseSecond.1, realNonnegative]
    · linarith [falseSecond.2, imagNegative]

/-- Parser phases whose two child formulas are disjoint for every coherent
value oracle solely by their displayed complementary atoms. -/
inductive OracleExclusivePhase : RawParser.Phase → Prop where
  | initial : OracleExclusivePhase .initial
  | highUnary (count : ℕ) : OracleExclusivePhase (.highUnary count)
  | lowUnary (count : ℕ) : OracleExclusivePhase (.lowUnary count)
  | loopUnary (count : ℕ) : OracleExclusivePhase (.loopUnary count)
  | sectorTwo (kind : RawParser.BlockKind) (exponent : ℕ)
      (first second : Bool) :
      OracleExclusivePhase (.sector kind exponent (.two first second))
  | sectorOne (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool) :
      OracleExclusivePhase (.sector kind exponent (.one first))
  | sectorZero (kind : RawParser.BlockKind) (exponent : ℕ) :
      OracleExclusivePhase (.sector kind exponent .zero)

/-- Every raw-parser phase has an oracle-independent exclusive child split. -/
theorem oracleExclusivePhase : (phase : RawParser.Phase) →
    OracleExclusivePhase phase
  | .initial => .initial
  | .highUnary count => .highUnary count
  | .lowUnary count => .lowUnary count
  | .loopUnary count => .loopUnary count
  | .sector kind exponent .zero => .sectorZero kind exponent
  | .sector kind exponent (.one first) => .sectorOne kind exponent first
  | .sector kind exponent (.two first second) =>
      .sectorTwo kind exponent first second

/-- The canonical algebraic-event truth table cannot select both bits in all
phases whose strict/weak split is carried by one common atom. -/
theorem inputEventPairCheck_ne_both_of_oracleExclusive
    (state : RawParser.State) (path : ProjectivePath.Path)
    (branch : ClassifiedEventFactor (inputEventPolynomials state path))
    (parent : CountOneInterval branch.factor.polynomial)
    (exclusive : OracleExclusivePhase state.phase) :
    eventFormulaPairCheck branch parent ≠ (true, true) := by
  intro both
  let value : HermitianForm → ℚ := fun form =>
    canonicalEventValue branch.factor.input (clearedForm form path)
      (branch.computeEventSigns parent).refined.interval.lower
  have pairAnd : ((eventFormulaPairCheck branch parent).1 &&
      (eventFormulaPairCheck branch parent).2) = true := by
    rw [both]
    rfl
  have canonicalAnd : formulaEvalWith
      (.and (inputAdvanceFormula state false)
        (inputAdvanceFormula state true)) value = true := by
    calc
      _ = ((eventFormulaPairCheck branch parent).1 &&
          (eventFormulaPairCheck branch parent).2) := by
        symm
        simpa only [inputEventPolynomials, value] using
          eventFormulaPairCheck_and_eq_canonicalEval branch parent
      _ = true := pairAnd
  have canonicalBoth :
      formulaEvalWith (inputAdvanceFormula state false) value = true ∧
        formulaEvalWith (inputAdvanceFormula state true) value = true := by
    simpa only [formulaEvalWith, Bool.and_eq_true] using canonicalAnd
  rcases state with ⟨phase, matrix, history⟩
  cases exclusive with
  | initial =>
      exact formulaEvalWith_inputAdvance_initial_ne_both matrix history value
        canonicalBoth
  | highUnary count =>
      exact formulaEvalWith_inputAdvance_highUnary_ne_both count matrix history
        value canonicalBoth
  | lowUnary count =>
      exact formulaEvalWith_inputAdvance_lowUnary_ne_both count matrix history
        value canonicalBoth
  | loopUnary count =>
      exact formulaEvalWith_inputAdvance_loopUnary_ne_both count matrix history
        value canonicalBoth
  | sectorTwo kind exponent first second =>
      exact formulaEvalWith_inputAdvance_sector_two_ne_both kind exponent
        first second matrix history value canonicalBoth
  | sectorOne kind exponent first =>
      exact formulaEvalWith_inputAdvance_sector_one_ne_both kind exponent
        first matrix history value canonicalBoth
  | sectorZero kind exponent =>
      exact formulaEvalWith_inputAdvance_sector_zero_ne_both kind exponent
        matrix history value canonicalBoth

/-- The exact algebraic-event truth table never assigns one event to both
children, in every raw-parser phase and without choosing an event root. -/
theorem inputEventPairCheck_ne_both
    (state : RawParser.State) (path : ProjectivePath.Path)
    (branch : ClassifiedEventFactor (inputEventPolynomials state path))
    (parent : CountOneInterval branch.factor.polynomial) :
    eventFormulaPairCheck branch parent ≠ (true, true) :=
  inputEventPairCheck_ne_both_of_oracleExclusive state path branch parent
    (oracleExclusivePhase state.phase)

private theorem eventFormulaPairCheck_eq_pathEvalBool
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0) :
    eventFormulaPairCheck branch parent =
      (pathEvalBool left path t, pathEvalBool right path t) := by
  let signs := branch.computeEventSigns parent
  let values := eventValues parent branch.relations signs
  have polynomialCorrect := eventValues_correct branch.relations parent signs
    lower upper eventZero
  have combinedCorrect : List.Forall₂ (AtomValueCorrect path t)
      (formulaAtoms (.and left right)) values :=
    atomValues_correct_of_polynomials path t polynomialCorrect
  let leftCount := (formulaAtoms left).length
  let leftValues := values.take leftCount
  let rightValues := values.drop leftCount
  have leftCorrect : List.Forall₂ (AtomValueCorrect path t)
      (formulaAtoms left) leftValues := by
    have taken := List.forall₂_take leftCount combinedCorrect
    simpa [leftCount, leftValues, formulaAtoms] using taken
  have rightCorrect : List.Forall₂ (AtomValueCorrect path t)
      (formulaAtoms right) rightValues := by
    have dropped := List.forall₂_drop leftCount combinedCorrect
    simpa [leftCount, rightValues, formulaAtoms] using dropped
  have valuesIdentity : values = leftValues ++ rightValues := by
    simp [leftValues, rightValues]
  have leftConsumed := consumeAtomValues_correct left path t leftCorrect rightValues
  have rightConsumed := consumeAtomValues_correct right path t rightCorrect []
  simp only [List.append_nil] at rightConsumed
  change
    ((consumeAtomValues left values).1,
      evalAtomValues right (consumeAtomValues left values).2) =
        (pathEvalBool left path t, pathEvalBool right path t)
  rw [valuesIdentity]
  rw [leftConsumed]
  exact congrArg (fun result => (pathEvalBool left path t, result.1))
    rightConsumed

theorem eventFormulaPairCheck_left_iff
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (eventFormulaPairCheck branch parent).1 = true ↔
      left.Holds (path.value t) := by
  rw [eventFormulaPairCheck_eq_pathEvalBool branch parent lower upper eventZero]
  exact pathEvalBool_eq_true_iff left path t pathDenominator

theorem eventFormulaPairCheck_right_iff
    {left right : Formula} {path : ProjectivePath.Path}
    (branch : ClassifiedEventFactor
      (eventFormulaPolynomials (.and left right) path))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (branch.computeEventSigns parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (branch.computeEventSigns parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (eventFormulaPairCheck branch parent).2 = true ↔
      right.Holds (path.value t) := by
  rw [eventFormulaPairCheck_eq_pathEvalBool branch parent lower upper eventZero]
  exact pathEvalBool_eq_true_iff right path t pathDenominator

/-! ## Generic re-isolation of classified event branches -/

private theorem eval_ne_zero_of_toPolynomial_dvd
    {small large : RatPolynomial} {t : ℚ}
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (largeNonzero : large.eval t ≠ 0) : small.eval t ≠ 0 := by
  rcases divides with ⟨quotient, identity⟩
  intro smallZero
  apply largeNonzero
  calc
    large.eval t = Polynomial.eval t large.toPolynomial :=
      (eval_toPolynomial large t).symm
    _ = Polynomial.eval t (small.toPolynomial * quotient) := by rw [identity]
    _ = small.eval t * Polynomial.eval t quotient := by
      rw [Polynomial.eval_mul, eval_toPolynomial]
    _ = 0 := by rw [smallZero, zero_mul]

private theorem eval_eq_zero_of_toPolynomial_dvd
    {small large : RatPolynomial} {t : ℚ}
    (divides : small.toPolynomial ∣ large.toPolynomial)
    (smallZero : small.eval t = 0) : large.eval t = 0 := by
  rcases divides with ⟨quotient, identity⟩
  calc
    large.eval t = Polynomial.eval t large.toPolynomial :=
      (eval_toPolynomial large t).symm
    _ = Polynomial.eval t (small.toPolynomial * quotient) := by rw [identity]
    _ = small.eval t * Polynomial.eval t quotient := by
      rw [Polynomial.eval_mul, eval_toPolynomial]
    _ = 0 := by rw [smallZero, zero_mul]

/-- A small generic index for a re-isolated classified divisor.  Keeping the
condition list abstract prevents parser-formula normalization from being
repeated in every dependent field. -/
structure ClassifiedEventCell
    (conditions : List RatPolynomial) (original : Factor)
    (root : CountOneInterval original.polynomial) where
  branch : ClassifiedEventFactor conditions
  divides : branch.factor.polynomial.toPolynomial ∣
    original.polynomial.toPolynomial
  parent : CountOneInterval branch.factor.polynomial
  refines : parent.interval.Refines root.interval

def classifiedEventCellsForBranch
    {conditions : List RatPolynomial} {original : Factor}
    (root : CountOneInterval original.polynomial)
    (branch : ClassifiedEventFactor conditions)
    (divides : branch.factor.polynomial.toPolynomial ∣
      original.polynomial.toPolynomial) :
    List (ClassifiedEventCell conditions original root) :=
  let isolation := FTA.SturmIsolation.isolate branch.factor.input
    root.interval.lower root.interval.upper root.proper
    (eval_ne_zero_of_toPolynomial_dvd divides root.lowerClear)
    (eval_ne_zero_of_toPolynomial_dvd divides root.upperClear)
  isolation.transducers.attach.map fun item =>
    { branch := branch
      divides := divides
      parent := item.1
      refines := isolation.refine item.1 item.2 }

/-- Following a count-one event through further finite condition splits
always leaves at least one re-isolated cell.  The selected descendant already
has doubled count two on a nested interval; additivity and nonnegativity make
its count positive on the original interval, so the fresh isolation list
cannot be empty. -/
theorem classifiedEventCellsForBranch_ne_nil_of_classification
    {conditions : List RatPolynomial} {original : Factor}
    {root : CountOneInterval original.polynomial}
    (classification : CountOneClassification conditions original root) :
    classifiedEventCellsForBranch root classification.branch
      classification.divides ≠ [] := by
  let polynomial := classification.branch.factor.polynomial
  have lowerClear : polynomial.eval root.interval.lower ≠ 0 :=
    eval_ne_zero_of_toPolynomial_dvd classification.divides root.lowerClear
  have upperClear : polynomial.eval root.interval.upper ≠ 0 :=
    eval_ne_zero_of_toPolynomial_dvd classification.divides root.upperClear
  have leftNonnegative : 0 ≤ FTA.Sturm.sturmRootCount2 polynomial
      root.interval.lower classification.parent.interval.lower := by
    rcases lt_or_eq_of_le classification.refines.1 with proper | equality
    · exact (computedEventPartitionProgram
        classification.branch.factor.input).nonnegativeLaw proper lowerClear
          classification.parent.lowerClear
    · rw [← equality]
      simp
  have rightNonnegative : 0 ≤ FTA.Sturm.sturmRootCount2 polynomial
      classification.parent.interval.upper root.interval.upper := by
    rcases lt_or_eq_of_le classification.refines.2 with proper | equality
    · exact (computedEventPartitionProgram
        classification.branch.factor.input).nonnegativeLaw proper
          classification.parent.upperClear upperClear
    · rw [equality]
      simp
  have leftAdd := FTA.Sturm.sturmRootCount2_add polynomial
    root.interval.lower classification.parent.interval.lower
      classification.parent.interval.upper
  have rightAdd := FTA.Sturm.sturmRootCount2_add polynomial
    root.interval.lower classification.parent.interval.upper
      root.interval.upper
  have ambientPositive : 0 < FTA.Sturm.sturmRootCount2 polynomial
      root.interval.lower root.interval.upper := by
    rw [← rightAdd, ← leftAdd]
    rw [classification.parent.countOne]
    omega
  let isolation := FTA.SturmIsolation.isolate
    classification.branch.factor.input root.interval.lower root.interval.upper
      root.proper lowerClear upperClear
  cases transducersEquation : isolation.transducers with
  | nil =>
      have exactCount := isolation.exactCount
      rw [transducersEquation] at exactCount
      simp only [List.length_nil, Nat.cast_zero, mul_zero] at exactCount
      exact (ne_of_gt ambientPositive exactCount).elim
  | cons parent parents =>
      simp [classifiedEventCellsForBranch, isolation, transducersEquation]

/-- Re-isolation does not lose an exact rational zero lying in the original
count-one interval. -/
theorem classifiedEventCellsForBranch_covers
    {conditions : List RatPolynomial} {original : Factor}
    (root : CountOneInterval original.polynomial)
    (branch : ClassifiedEventFactor conditions)
    (divides : branch.factor.polynomial.toPolynomial ∣
      original.polynomial.toPolynomial)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0) :
    ∃ cell ∈ classifiedEventCellsForBranch root branch divides,
      cell.parent.interval.lower ≤ t ∧
        t ≤ cell.parent.interval.upper ∧
        cell.branch.factor.polynomial.eval t = 0 := by
  let isolation := FTA.SturmIsolation.isolate branch.factor.input
    root.interval.lower root.interval.upper root.proper
    (eval_ne_zero_of_toPolynomial_dvd divides root.lowerClear)
    (eval_ne_zero_of_toPolynomial_dvd divides root.upperClear)
  rcases FTA.PositiveLowerBound.IsolationResult.rationalZero_mem
      branch.factor.input isolation lower upper eventZero with
    ⟨parent, parentMember, parentLower, parentUpper⟩
  let item : { child // child ∈ isolation.transducers } :=
    ⟨parent, parentMember⟩
  let cell : ClassifiedEventCell conditions original root :=
    { branch := branch
      divides := divides
      parent := parent
      refines := isolation.refine parent parentMember }
  refine ⟨cell, ?_, parentLower, parentUpper, eventZero⟩
  change cell ∈ isolation.transducers.attach.map fun item =>
    { branch := branch
      divides := divides
      parent := item.1
      refines := isolation.refine item.1 item.2 }
  rw [List.mem_map]
  exact ⟨item, by simp [item], rfl⟩

theorem ClassifiedEventCell.original_event_zero
    {conditions : List RatPolynomial} {original : Factor}
    {root : CountOneInterval original.polynomial}
    (cell : ClassifiedEventCell conditions original root) {t : ℚ}
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    original.polynomial.eval t = 0 :=
  eval_eq_zero_of_toPolynomial_dvd cell.divides eventZero

theorem ClassifiedEventCell.signRefines
    {conditions : List RatPolynomial} {original : Factor}
    {root : CountOneInterval original.polynomial}
    (cell : ClassifiedEventCell conditions original root) :
    (cell.branch.computeEventSigns cell.parent).refined.interval.Refines
      root.interval :=
  RationalInterval.refines_trans
    (cell.branch.computeEventSigns cell.parent).refines cell.refines

/-! ## Parser-owner cells for relevant curve events -/

/-- The already computed closed-box sign refinement is the canonical root
interval for subsequent owner classification. -/
def ownerRoot
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) :
    CountOneInterval event.branch.factor.polynomial :=
  (boxEventSigns event.branch event.parent).refined

/-- A relevant non-pole event already contains a whole-cell positive lower
bound for its projective denominator norm.  The box-sign projection retains
the same common refined interval, so no additional refinement is needed. -/
def RelevantCurveEvent.ownerDenominatorCertificate
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) :
    DenominatorCertificate path (ownerRoot event).interval := by
  let condition := denominatorCoprimeCondition event.branch
    event.denominatorNonEquality
  let allSigns := event.branch.computeEventSigns event.parent
  have signCertificate := allSigns.signs condition
    (denominatorCoprimeCondition_mem event.branch
      event.denominatorNonEquality)
  have denominatorSigns : IntervalSignCertificate
      (CCLPathIntersection.denominatorNorm path)
      allSigns.refined.interval.lower allSigns.refined.interval.upper := by
    simpa [condition] using signCertificate
  rw [ownerRoot, boxEventSigns_refined]
  exact DenominatorCertificate.ofSignCertificate path
    allSigns.refined.interval denominatorSigns

/-- The quantitative denominator certificate excludes projective poles at
every rational parameter in the canonical owner interval. -/
theorem RelevantCurveEvent.ownerDenominator_ne
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) {t : ℚ}
    (lower : (ownerRoot event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot event).interval.upper) :
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 :=
  (RelevantCurveEvent.ownerDenominatorCertificate event).denominator_ne
    lower upper

abbrev InputEventCell
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box) :=
  ClassifiedEventCell (inputEventPolynomials state path)
    event.branch.factor (ownerRoot event)

def inputEventCellsForBranch
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box)
    (classified : { branch // branch ∈
      inputEventBranches event.branch.factor.input state path }) :
    List (InputEventCell state event) :=
  let divides : classified.1.factor.polynomial.toPolynomial ∣
      event.branch.factor.polynomial.toPolynomial :=
    classifyEventConditions_dvd event.branch.factor.input (by
      simpa [inputEventBranches, inputEventPolynomials,
        eventFormulaPairBranches, eventFormulaBranches] using classified.2)
  classifiedEventCellsForBranch (ownerRoot event) classified.1 divides

theorem inputEventCellsForBranch_covers
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box)
    (classified : { branch // branch ∈
      inputEventBranches event.branch.factor.input state path })
    {t : ℚ} (lower : (ownerRoot event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot event).interval.upper)
    (eventZero : classified.1.factor.polynomial.eval t = 0) :
    ∃ cell ∈ inputEventCellsForBranch state event classified,
      cell.parent.interval.lower ≤ t ∧
        t ≤ cell.parent.interval.upper ∧
        cell.branch.factor.polynomial.eval t = 0 := by
  simpa only [inputEventCellsForBranch] using
    classifiedEventCellsForBranch_covers (ownerRoot event) classified.1
      (classifyEventConditions_dvd event.branch.factor.input (by
        simpa [inputEventBranches, inputEventPolynomials,
          eventFormulaPairBranches, eventFormulaBranches] using classified.2))
      lower upper eventZero

/-- Fully executable finite owner-classified re-isolation of one relevant
curve event. -/
def inputEventCells
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box) :
    List (InputEventCell state event) :=
  (inputEventBranches event.branch.factor.input state path).attach.flatMap
    (inputEventCellsForBranch state event)

/-- The fully classified parser-owner family of a relevant count-one event is
never empty, independently of whether its algebraic root happens to be
rational. -/
theorem inputEventCells_ne_nil
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box) :
    inputEventCells state event ≠ [] := by
  let classification := followCountOneConditions event.branch.factor
    (ownerRoot event) (inputEventPolynomials state path)
  have branchMember : classification.branch ∈
      inputEventBranches event.branch.factor.input state path := by
    simpa [inputEventBranches, inputEventPolynomials,
      eventFormulaPairBranches, eventFormulaBranches] using
        classification.member
  let classified : { branch // branch ∈
      inputEventBranches event.branch.factor.input state path } :=
    ⟨classification.branch, branchMember⟩
  have branchCellsNonempty :
      inputEventCellsForBranch state event classified ≠ [] := by
    simpa [inputEventCellsForBranch, classified] using
      classifiedEventCellsForBranch_ne_nil_of_classification classification
  intro empty
  have branchCellsEmpty :=
    (List.flatMap_eq_nil_iff.mp (by
      simpa only [inputEventCells] using empty)) classified (by
        simp [classified])
  exact branchCellsNonempty branchCellsEmpty

/-- The complete finite parser-owner family covers every exact rational zero
represented by the original relevant event interval. -/
theorem inputEventCells_covers
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box)
    {t : ℚ} (lower : (ownerRoot event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot event).interval.upper)
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    ∃ cell ∈ inputEventCells state event,
      cell.parent.interval.lower ≤ t ∧
        t ≤ cell.parent.interval.upper ∧
        cell.branch.factor.polynomial.eval t = 0 := by
  rcases classifyEventConditions_covers event.branch.factor.input
      (inputEventPolynomials state path) eventZero with
    ⟨branch, branchMember, branchZero⟩
  have inputMember : branch ∈
      inputEventBranches event.branch.factor.input state path := by
    simpa [inputEventBranches, inputEventPolynomials,
      eventFormulaPairBranches, eventFormulaBranches] using branchMember
  let classified : { candidate // candidate ∈
      inputEventBranches event.branch.factor.input state path } :=
    ⟨branch, inputMember⟩
  rcases inputEventCellsForBranch_covers state event classified lower upper
      branchZero with
    ⟨cell, cellMember, cellLower, cellUpper, cellZero⟩
  refine ⟨cell, ?_, cellLower, cellUpper, cellZero⟩
  rw [inputEventCells, List.mem_flatMap]
  exact ⟨classified, by simp [classified], cellMember⟩

/-- The parser-owner family's internal common-sign refinement also retains the
exact rational zero covered by the re-isolated owner cell. -/
theorem inputEventCells_covers_refined
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box)
    {t : ℚ} (lower : (ownerRoot event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot event).interval.upper)
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    ∃ cell ∈ inputEventCells state event,
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t ∧
      t ≤ (cell.branch.computeEventSigns cell.parent).refined.interval.upper ∧
      cell.branch.factor.polynomial.eval t = 0 := by
  rcases inputEventCells_covers state event lower upper eventZero with
    ⟨cell, cellMember, cellLower, cellUpper, cellZero⟩
  let signs := cell.branch.computeEventSigns cell.parent
  have inside :=
    FTA.PositiveLowerBound.CountOneInterval.rationalZero_mem_of_refines
      cell.branch.factor.input cell.parent signs.refined signs.refines
      cellLower cellUpper cellZero
  exact ⟨cell, cellMember,
    by simpa only [signs] using inside.1,
    by simpa only [signs] using inside.2, cellZero⟩

theorem inputEventCells_ne_nil_of_rational_zero
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    (state : RawParser.State) (event : RelevantCurveEvent p path box)
    {t : ℚ} (lower : (ownerRoot event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot event).interval.upper)
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    inputEventCells state event ≠ [] := by
  rcases inputEventCells_covers state event lower upper eventZero with
    ⟨cell, member, _cellLower, _cellUpper, _cellZero⟩
  exact List.ne_nil_of_mem member

theorem InputEventCell.path_denominator_ne
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 :=
  event.path_denominator_ne (cell.original_event_zero eventZero)

/-- Re-isolating an event by parser conditions preserves the whole-cell
denominator exclusion, not merely its value at a represented event zero. -/
theorem InputEventCell.path_denominator_ne_on_cell
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper) :
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 :=
  RelevantCurveEvent.ownerDenominator_ne event
    (cell.signRefines.1.trans lower)
    (upper.trans cell.signRefines.2)

/-- The final parser-classified event factor remains a divisor of the curve
common factor through both gcd-classification layers. -/
theorem InputEventCell.factor_toPolynomial_dvd_commonFactor
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.branch.factor.polynomial.toPolynomial ∣
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).toPolynomial :=
  cell.divides.trans
    (curveFactor_toPolynomial_dvd event.branch event.curveEquality)

theorem InputEventCell.factor_toPolynomial_dvd_clearedReal
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.branch.factor.polynomial.toPolynomial ∣
      (clearedReal p path).toPolynomial := by
  apply cell.factor_toPolynomial_dvd_commonFactor.trans
  simpa only [PathClearance.commonFactor] using
    FTA.DenseGCD.symmetricGCD_toPolynomial_dvd_left
      (clearedReal p path) (clearedImag p path)

theorem InputEventCell.factor_toPolynomial_dvd_clearedImag
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.branch.factor.polynomial.toPolynomial ∣
      (clearedImag p path).toPolynomial := by
  apply cell.factor_toPolynomial_dvd_commonFactor.trans
  simpa only [PathClearance.commonFactor] using
    FTA.DenseGCD.symmetricGCD_toPolynomial_dvd_right
      (clearedReal p path) (clearedImag p path)

/-- Narrow the selected count-one event factor once, so both cleared
coordinates can use the same rational approximation point. -/
def InputEventCell.clearedApproximation
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    NarrowEventApproximation cell.branch.factor.input
      (cell.branch.computeEventSigns cell.parent).refined epsilon :=
  narrowEventApproximation cell.branch.factor.input
    (cell.branch.computeEventSigns cell.parent).refined epsilon epsilonPositive

theorem InputEventCell.clearedApproximation_realSmall
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    |(clearedReal p path).eval
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower| ≤
      approximationBound (clearedReal p path) cell.branch.factor.polynomial
        (cell.branch.computeEventSigns cell.parent).refined epsilon :=
  (cell.clearedApproximation epsilon epsilonPositive).multipleSmall
    cell.factor_toPolynomial_dvd_clearedReal epsilonPositive.le

theorem InputEventCell.clearedApproximation_imagSmall
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    |(clearedImag p path).eval
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower| ≤
      approximationBound (clearedImag p path) cell.branch.factor.polynomial
        (cell.branch.computeEventSigns cell.parent).refined epsilon :=
  (cell.clearedApproximation epsilon epsilonPositive).multipleSmall
    cell.factor_toPolynomial_dvd_clearedImag epsilonPositive.le

/-- Affine residual bound at the shared rational approximation point, after
dividing by the event interval's positive projective denominator margin. -/
def InputEventCell.affineApproximationBound
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ) : ℚ :=
  affineResidualBound p
    (RelevantCurveEvent.ownerDenominatorCertificate event)
    (approximationBound (clearedReal p path) cell.branch.factor.polynomial
      (cell.branch.computeEventSigns cell.parent).refined epsilon)
    (approximationBound (clearedImag p path) cell.branch.factor.polynomial
      (cell.branch.computeEventSigns cell.parent).refined epsilon)

theorem InputEventCell.clearedApproximation_affineSmall
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    CCL.GaussianRat.normSq (p.eval (path.value
      (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower)) ≤
        cell.affineApproximationBound epsilon := by
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  apply normSq_eval_le_affineResidualBound
    (RelevantCurveEvent.ownerDenominatorCertificate event)
  · exact cell.signRefines.1.trans approximation.refines.1
  · exact (approximation.refined.proper.le.trans approximation.refines.2).trans
      cell.signRefines.2
  · simpa only [approximation] using
      cell.clearedApproximation_realSmall epsilon epsilonPositive
  · simpa only [approximation] using
      cell.clearedApproximation_imagSmall epsilon epsilonPositive

/-- Coefficient of the squared requested parameter width in the affine
residual estimate. -/
def InputEventCell.affineApproximationCoefficient
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  (approximationCoefficient (clearedReal p path)
      cell.branch.factor.polynomial
      (cell.branch.computeEventSigns cell.parent).refined ^ 2 +
    approximationCoefficient (clearedImag p path)
      cell.branch.factor.polynomial
      (cell.branch.computeEventSigns cell.parent).refined ^ 2) /
    (RelevantCurveEvent.ownerDenominatorCertificate event).bound ^
      p.coeffs.length

theorem InputEventCell.affineApproximationBound_eq
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ) :
    cell.affineApproximationBound epsilon =
      cell.affineApproximationCoefficient * epsilon ^ 2 := by
  unfold InputEventCell.affineApproximationBound
  unfold ProjectivePathBounds.affineResidualBound
  rw [approximationBound_eq_coefficient_mul,
    approximationBound_eq_coefficient_mul]
  unfold InputEventCell.affineApproximationCoefficient
  ring

theorem InputEventCell.affineApproximationCoefficient_nonneg
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 ≤ cell.affineApproximationCoefficient := by
  apply div_nonneg
  · exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact (pow_pos
      (RelevantCurveEvent.ownerDenominatorCertificate event).positive
      p.coeffs.length).le

/-- Positive coefficient majorant used to turn any requested affine residual
threshold into one ordinary rational parameter-width request. -/
def InputEventCell.affineApproximationMajorant
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  max 1 cell.affineApproximationCoefficient

theorem InputEventCell.affineApproximationMajorant_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 < cell.affineApproximationMajorant :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem InputEventCell.affineApproximationCoefficient_le_majorant
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.affineApproximationCoefficient ≤
      cell.affineApproximationMajorant :=
  le_max_right _ _

def InputEventCell.affineApproximationWidth
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (threshold : ℚ) : ℚ :=
  min 1 (threshold / cell.affineApproximationMajorant)

theorem InputEventCell.affineApproximationWidth_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    0 < cell.affineApproximationWidth threshold := by
  apply lt_min zero_lt_one
  exact div_pos thresholdPositive cell.affineApproximationMajorant_pos

theorem InputEventCell.affineApproximationBound_le
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    cell.affineApproximationBound
        (cell.affineApproximationWidth threshold) ≤ threshold := by
  let epsilon := cell.affineApproximationWidth threshold
  let coefficient := cell.affineApproximationCoefficient
  let majorant := cell.affineApproximationMajorant
  have epsilonPositive : 0 < epsilon :=
    cell.affineApproximationWidth_pos thresholdPositive
  have epsilonLeOne : epsilon ≤ 1 := min_le_left _ _
  have epsilonLeRatio : epsilon ≤ threshold / majorant := min_le_right _ _
  have coefficientNonnegative : 0 ≤ coefficient :=
    cell.affineApproximationCoefficient_nonneg
  have coefficientLeMajorant : coefficient ≤ majorant :=
    cell.affineApproximationCoefficient_le_majorant
  have majorantPositive : 0 < majorant :=
    cell.affineApproximationMajorant_pos
  have epsilonSquareLe : epsilon ^ 2 ≤ epsilon := by
    nlinarith
  rw [cell.affineApproximationBound_eq]
  calc
    coefficient * epsilon ^ 2 ≤ majorant * epsilon ^ 2 :=
      mul_le_mul_of_nonneg_right coefficientLeMajorant (sq_nonneg epsilon)
    _ ≤ majorant * epsilon :=
      mul_le_mul_of_nonneg_left epsilonSquareLe majorantPositive.le
    _ ≤ threshold := by
      have := (le_div_iff₀ majorantPositive).mp epsilonLeRatio
      simpa only [mul_comm] using this

/-- Every positive rational residual request yields a rational parameter in
the retained owner interval at which the affine polynomial residual meets
that request. -/
theorem InputEventCell.arbitrarilySmallAffineResidual
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    CCL.GaussianRat.normSq (p.eval (path.value
      (cell.clearedApproximation (cell.affineApproximationWidth threshold)
        (cell.affineApproximationWidth_pos thresholdPositive)).refined.interval.lower)) ≤
      threshold :=
  (cell.clearedApproximation_affineSmall
      (cell.affineApproximationWidth threshold)
      (cell.affineApproximationWidth_pos thresholdPositive)).trans
    (cell.affineApproximationBound_le thresholdPositive)

/-- At the rational approximation point, every original closed-box
condition is already nonnegative unless it is an equality multiple of the
selected factor; in that case its possible violation has an explicit
linear-in-width bound. -/
theorem InputEventCell.boxCondition_nonnegative_or_small
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) {condition : RatPolynomial}
    (member : condition ∈
      FTA.CCLIntersectionGuard.conditionPolynomials
        (FTA.CCLPathIntersection.boxConditions path box)) :
    0 ≤ condition.eval
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower ∨
      |condition.eval
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower| ≤
        approximationBound condition cell.branch.factor.polynomial
          (cell.branch.computeEventSigns cell.parent).refined epsilon := by
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  have boxLower :
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤
        approximation.refined.interval.lower := by
    simpa only [ownerRoot] using
      cell.signRefines.1.trans approximation.refines.1
  have boxUpper :
      approximation.refined.interval.lower ≤
        (boxEventSigns event.branch event.parent).refined.interval.upper := by
    simpa only [ownerRoot] using
      (approximation.refined.proper.le.trans approximation.refines.2).trans
        cell.signRefines.2
  have alternative :=
    ConditionRelations.dvd_or_nonnegative_of_closedCheck
      event.branch.factor.input event.parent (boxRelations event.branch)
      (boxEventSigns event.branch event.parent) event.meetsBox member
      boxLower boxUpper
  rcases alternative with divides | nonnegative
  · right
    exact approximation.multipleSmall (cell.divides.trans divides)
      epsilonPositive.le
  · exact Or.inl nonnegative

/-- One positive coefficient majorizing the four possible equality-condition
residuals for closed membership in the original event box. -/
def InputEventCell.boxApproximationMajorant
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  let conditions := FTA.CCLPathIntersection.boxConditions path box
  let factor := cell.branch.factor.polynomial
  let root := (cell.branch.computeEventSigns cell.parent).refined
  1 + approximationCoefficient conditions.xLower factor root +
    approximationCoefficient conditions.xUpper factor root +
    approximationCoefficient conditions.yLower factor root +
    approximationCoefficient conditions.yUpper factor root

theorem InputEventCell.boxApproximationMajorant_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 < cell.boxApproximationMajorant := by
  let conditions := FTA.CCLPathIntersection.boxConditions path box
  have xLower := approximationCoefficient_nonneg conditions.xLower
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have xUpper := approximationCoefficient_nonneg conditions.xUpper
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have yLower := approximationCoefficient_nonneg conditions.yLower
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have yUpper := approximationCoefficient_nonneg conditions.yUpper
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  dsimp only [InputEventCell.boxApproximationMajorant, conditions]
  linarith

theorem InputEventCell.boxConditionApproximationBound_le
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {epsilon : ℚ}
    (epsilonNonnegative : 0 ≤ epsilon) {condition : RatPolynomial}
    (member : condition ∈
      FTA.CCLIntersectionGuard.conditionPolynomials
        (FTA.CCLPathIntersection.boxConditions path box)) :
    approximationBound condition cell.branch.factor.polynomial
        (cell.branch.computeEventSigns cell.parent).refined epsilon ≤
      cell.boxApproximationMajorant * epsilon := by
  rw [approximationBound_eq_coefficient_mul]
  let conditions := FTA.CCLPathIntersection.boxConditions path box
  have xLower := approximationCoefficient_nonneg conditions.xLower
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have xUpper := approximationCoefficient_nonneg conditions.xUpper
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have yLower := approximationCoefficient_nonneg conditions.yLower
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have yUpper := approximationCoefficient_nonneg conditions.yUpper
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  have coefficientLe :
      approximationCoefficient condition cell.branch.factor.polynomial
          (cell.branch.computeEventSigns cell.parent).refined ≤
        cell.boxApproximationMajorant := by
    simp only [FTA.CCLIntersectionGuard.conditionPolynomials,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      dsimp only [InputEventCell.boxApproximationMajorant, conditions]
      linarith
  exact mul_le_mul_of_nonneg_right coefficientLe epsilonNonnegative

def InputEventCell.boxApproximationMargin
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ) : ℚ :=
  cell.boxApproximationMajorant * epsilon /
    (RelevantCurveEvent.ownerDenominatorCertificate event).bound

theorem InputEventCell.boxApproximationMargin_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < cell.boxApproximationMargin epsilon := by
  exact div_pos (mul_pos cell.boxApproximationMajorant_pos epsilonPositive)
    (RelevantCurveEvent.ownerDenominatorCertificate event).positive

private theorem neg_div_le_gap_of_scaled_gap
    {denominatorLower denominatorValue magnitude gap : ℚ}
    (lowerPositive : 0 < denominatorLower)
    (lowerLeValue : denominatorLower ≤ denominatorValue)
    (magnitudeNonnegative : 0 ≤ magnitude)
    (scaledLower : -magnitude ≤ denominatorValue * gap) :
    -magnitude / denominatorLower ≤ gap := by
  by_cases gapNonnegative : 0 ≤ gap
  · have quotientNonnegative : 0 ≤ magnitude / denominatorLower :=
      div_nonneg magnitudeNonnegative lowerPositive.le
    rw [neg_div]
    exact (neg_nonpos.mpr quotientNonnegative).trans gapNonnegative
  · have gapNonpositive : gap ≤ 0 := le_of_not_ge gapNonnegative
    have scaledUpper : denominatorValue * gap ≤ denominatorLower * gap :=
      mul_le_mul_of_nonpos_right lowerLeValue gapNonpositive
    apply (div_le_iff₀ lowerPositive).2
    calc
      -magnitude ≤ denominatorValue * gap := scaledLower
      _ ≤ denominatorLower * gap := scaledUpper
      _ = gap * denominatorLower := mul_comm _ _

/-- The rational common approximation is explicitly close to the retained
closed event box.  Coprime box conditions hold exactly; equality conditions
can violate a side only by the displayed linear rational margin. -/
theorem InputEventCell.clearedApproximation_boxSlack
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    let point := path.value
      (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower
    let margin := cell.boxApproximationMargin epsilon
    box.xLower - margin ≤ point.re ∧ point.re ≤ box.xUpper + margin ∧
      box.yLower - margin ≤ point.im ∧ point.im ≤ box.yUpper + margin := by
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let point := path.value t
  let conditions := FTA.CCLPathIntersection.boxConditions path box
  let certificate := RelevantCurveEvent.ownerDenominatorCertificate event
  let magnitude := cell.boxApproximationMajorant * epsilon
  let margin := cell.boxApproximationMargin epsilon
  have ownerLower : (ownerRoot event).interval.lower ≤ t :=
    cell.signRefines.1.trans approximation.refines.1
  have ownerUpper : t ≤ (ownerRoot event).interval.upper :=
    (approximation.refined.proper.le.trans approximation.refines.2).trans
      cell.signRefines.2
  have denominatorLower :
      certificate.bound ≤
        (FTA.CCLPathIntersection.denominatorNorm path).eval t :=
    certificate.lower ownerLower ownerUpper
  have denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 :=
    certificate.denominator_ne ownerLower ownerUpper
  have magnitudeNonnegative : 0 ≤ magnitude :=
    mul_nonneg cell.boxApproximationMajorant_pos.le epsilonPositive.le
  have conditionLower (condition : RatPolynomial)
      (member : condition ∈
        FTA.CCLIntersectionGuard.conditionPolynomials conditions) :
      -magnitude ≤ condition.eval t := by
    have alternative := cell.boxCondition_nonnegative_or_small epsilon
      epsilonPositive member
    have bound := cell.boxConditionApproximationBound_le
      epsilonPositive.le member
    rcases alternative with nonnegative | small
    · exact (neg_nonpos.mpr magnitudeNonnegative).trans nonnegative
    · exact neg_le_of_abs_le (small.trans bound)
  have xLowerScaled :
      -magnitude ≤
        (FTA.CCLPathIntersection.denominatorNorm path).eval t *
          (point.re - box.xLower) := by
    rw [← FTA.CCLPathIntersection.eval_boxConditions_xLower path box t
      denominatorNonzero]
    apply conditionLower conditions.xLower
    simp [FTA.CCLIntersectionGuard.conditionPolynomials]
  have xUpperScaled :
      -magnitude ≤
        (FTA.CCLPathIntersection.denominatorNorm path).eval t *
          (box.xUpper - point.re) := by
    rw [← FTA.CCLPathIntersection.eval_boxConditions_xUpper path box t
      denominatorNonzero]
    apply conditionLower conditions.xUpper
    simp [FTA.CCLIntersectionGuard.conditionPolynomials]
  have yLowerScaled :
      -magnitude ≤
        (FTA.CCLPathIntersection.denominatorNorm path).eval t *
          (point.im - box.yLower) := by
    rw [← FTA.CCLPathIntersection.eval_boxConditions_yLower path box t
      denominatorNonzero]
    apply conditionLower conditions.yLower
    simp [FTA.CCLIntersectionGuard.conditionPolynomials]
  have yUpperScaled :
      -magnitude ≤
        (FTA.CCLPathIntersection.denominatorNorm path).eval t *
          (box.yUpper - point.im) := by
    rw [← FTA.CCLPathIntersection.eval_boxConditions_yUpper path box t
      denominatorNonzero]
    apply conditionLower conditions.yUpper
    simp [FTA.CCLIntersectionGuard.conditionPolynomials]
  have xLowerGap := neg_div_le_gap_of_scaled_gap certificate.positive
    denominatorLower magnitudeNonnegative xLowerScaled
  have xUpperGap := neg_div_le_gap_of_scaled_gap certificate.positive
    denominatorLower magnitudeNonnegative xUpperScaled
  have yLowerGap := neg_div_le_gap_of_scaled_gap certificate.positive
    denominatorLower magnitudeNonnegative yLowerScaled
  have yUpperGap := neg_div_le_gap_of_scaled_gap certificate.positive
    denominatorLower magnitudeNonnegative yUpperScaled
  have marginEq : margin = magnitude / certificate.bound := rfl
  rw [neg_div] at xLowerGap xUpperGap yLowerGap yUpperGap
  have xLowerFinal : box.xLower - margin ≤ point.re := by
    rw [marginEq]
    linarith
  have xUpperFinal : point.re ≤ box.xUpper + margin := by
    rw [marginEq]
    linarith
  have yLowerFinal : box.yLower - margin ≤ point.im := by
    rw [marginEq]
    linarith
  have yUpperFinal : point.im ≤ box.yUpper + margin := by
    rw [marginEq]
    linarith
  simpa only [point, t, approximation, margin] using
    And.intro xLowerFinal (And.intro xUpperFinal
      (And.intro yLowerFinal yUpperFinal))

/-- Spatial form of the same estimate: the rational event approximation is
within an explicit squared coordinate distance of the retained box. -/
theorem InputEventCell.clearedApproximation_withinSqOfBox
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    WithinSqOfBox box
      (path.value
        (cell.clearedApproximation epsilon epsilonPositive).refined.interval.lower)
      (3 * cell.boxApproximationMargin epsilon ^ 2) := by
  rcases cell.clearedApproximation_boxSlack epsilon epsilonPositive with
    ⟨xLower, xUpper, yLower, yUpper⟩
  exact withinSqOfBox_of_coordinate_slack
    (cell.boxApproximationMargin_pos epsilonPositive)
    xLower xUpper yLower yUpper

def InputEventCell.boxApproximationDistanceCoefficient
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  3 * (cell.boxApproximationMajorant /
    (RelevantCurveEvent.ownerDenominatorCertificate event).bound) ^ 2

theorem InputEventCell.boxApproximationDistanceCoefficient_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 < cell.boxApproximationDistanceCoefficient := by
  apply mul_pos (by norm_num)
  apply sq_pos_of_pos
  exact div_pos cell.boxApproximationMajorant_pos
    (RelevantCurveEvent.ownerDenominatorCertificate event).positive

theorem InputEventCell.boxApproximationDistance_eq
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (epsilon : ℚ) :
    3 * cell.boxApproximationMargin epsilon ^ 2 =
      cell.boxApproximationDistanceCoefficient * epsilon ^ 2 := by
  unfold InputEventCell.boxApproximationMargin
  unfold InputEventCell.boxApproximationDistanceCoefficient
  ring

def InputEventCell.boxApproximationWidth
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (threshold : ℚ) : ℚ :=
  min 1 (threshold /
    (2 * cell.boxApproximationDistanceCoefficient))

theorem InputEventCell.boxApproximationWidth_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    0 < cell.boxApproximationWidth threshold := by
  apply lt_min zero_lt_one
  exact div_pos thresholdPositive
    (mul_pos (by norm_num) cell.boxApproximationDistanceCoefficient_pos)

theorem InputEventCell.boxApproximationDistance_lt
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    3 * cell.boxApproximationMargin
        (cell.boxApproximationWidth threshold) ^ 2 < threshold := by
  let epsilon := cell.boxApproximationWidth threshold
  let coefficient := cell.boxApproximationDistanceCoefficient
  have epsilonPositive : 0 < epsilon :=
    cell.boxApproximationWidth_pos thresholdPositive
  have epsilonLeOne : epsilon ≤ 1 := min_le_left _ _
  have epsilonLeRatio : epsilon ≤ threshold / (2 * coefficient) :=
    min_le_right _ _
  have coefficientPositive : 0 < coefficient :=
    cell.boxApproximationDistanceCoefficient_pos
  have epsilonSquareLe : epsilon ^ 2 ≤ epsilon := by nlinarith
  rw [cell.boxApproximationDistance_eq]
  have scaledRatio : coefficient * epsilon ≤ threshold / 2 := by
    have := (le_div_iff₀ (mul_pos (by norm_num) coefficientPositive)).mp
      epsilonLeRatio
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2
    nlinarith
  calc
    coefficient * epsilon ^ 2 ≤ coefficient * epsilon :=
      mul_le_mul_of_nonneg_left epsilonSquareLe coefficientPositive.le
    _ ≤ threshold / 2 := scaledRatio
    _ < threshold := by linarith

/-- The retained algebraic event cell has rational curve points arbitrarily
close to its closed event box, with a precomputed ordinary width request. -/
theorem InputEventCell.arbitrarilyCloseToBox
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {threshold : ℚ}
    (thresholdPositive : 0 < threshold) :
    WithinSqOfBox box
      (path.value
        (cell.clearedApproximation (cell.boxApproximationWidth threshold)
          (cell.boxApproximationWidth_pos thresholdPositive)).refined.interval.lower)
      threshold := by
  apply WithinSqOfBox.mono
    (cell.clearedApproximation_withinSqOfBox
      (cell.boxApproximationWidth threshold)
      (cell.boxApproximationWidth_pos thresholdPositive))
  exact (cell.boxApproximationDistance_lt thresholdPositive).le

/-- Spatial tolerance small enough that the nearby-ambient Lipschitz change
uses less than one sixteenth of the retained box's boundary clearance. -/
def InputEventCell.interiorSpatialThreshold
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (_cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  min 1 (clearance.bound /
    (16 * denseLipschitzBound p (nearbyAmbient box)))

theorem InputEventCell.interiorSpatialThreshold_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < cell.interiorSpatialThreshold clearance := by
  apply lt_min zero_lt_one
  exact div_pos clearance.positive
    (mul_pos (by norm_num)
      (denseLipschitzBound_pos p (nearbyAmbient box)))

theorem InputEventCell.interiorSpatialThreshold_le_one
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    cell.interiorSpatialThreshold clearance ≤ 1 :=
  min_le_left _ _

theorem InputEventCell.interiorSpatialThreshold_distanceBudget
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    denseLipschitzBound p (nearbyAmbient box) *
        cell.interiorSpatialThreshold clearance <
      clearance.bound / 8 := by
  let L := denseLipschitzBound p (nearbyAmbient box)
  let threshold := cell.interiorSpatialThreshold clearance
  have LPositive : 0 < L := denseLipschitzBound_pos p (nearbyAmbient box)
  have thresholdLe : threshold ≤ clearance.bound / (16 * L) :=
    min_le_right _ _
  have scaled : L * threshold ≤ clearance.bound / 16 := by
    have product := (le_div_iff₀ (mul_pos (by norm_num) LPositive)).mp
      thresholdLe
    dsimp only [L, threshold]
    dsimp only [L, threshold] at product
    nlinarith
  dsimp only [L, threshold] at scaled ⊢
  nlinarith [clearance.positive]

/-- One parameter width satisfying an arbitrary positive affine-residual
request together with the fixed spatial-clamp budget. -/
def InputEventCell.controlledApproximationWidth
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    (residualThreshold : ℚ) : ℚ :=
  min (cell.affineApproximationWidth residualThreshold)
    (cell.boxApproximationWidth
      (cell.interiorSpatialThreshold clearance))

theorem InputEventCell.controlledApproximationWidth_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {residualThreshold : ℚ} (residualPositive : 0 < residualThreshold) :
    0 < cell.controlledApproximationWidth clearance residualThreshold := by
  apply lt_min
  · exact cell.affineApproximationWidth_pos residualPositive
  · exact cell.boxApproximationWidth_pos
      (cell.interiorSpatialThreshold_pos clearance)

/-- The controlled common approximation meets its requested affine residual
threshold. -/
theorem InputEventCell.controlledApproximation_residual_le
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {residualThreshold : ℚ} (residualPositive : 0 < residualThreshold) :
    let epsilon := cell.controlledApproximationWidth clearance residualThreshold
    CCL.GaussianRat.normSq (p.eval (path.value
      (cell.clearedApproximation epsilon
        (cell.controlledApproximationWidth_pos clearance
          residualPositive)).refined.interval.lower)) ≤ residualThreshold := by
  let epsilon := cell.controlledApproximationWidth clearance residualThreshold
  let affineWidth := cell.affineApproximationWidth residualThreshold
  let point := path.value
    (cell.clearedApproximation epsilon
      (cell.controlledApproximationWidth_pos clearance
        residualPositive)).refined.interval.lower
  have epsilonPositive : 0 < epsilon :=
    cell.controlledApproximationWidth_pos clearance residualPositive
  have affineWidthPositive : 0 < affineWidth :=
    cell.affineApproximationWidth_pos residualPositive
  have epsilonLeAffine : epsilon ≤ affineWidth := min_le_left _ _
  have epsilonSquareLeAffine : epsilon ^ 2 ≤ affineWidth ^ 2 := by
    nlinarith
  have approximationBound := cell.clearedApproximation_affineSmall
    epsilon epsilonPositive
  have boundMonotone :
      cell.affineApproximationBound epsilon ≤
        cell.affineApproximationBound affineWidth := by
    rw [cell.affineApproximationBound_eq,
      cell.affineApproximationBound_eq]
    exact mul_le_mul_of_nonneg_left epsilonSquareLeAffine
      cell.affineApproximationCoefficient_nonneg
  exact approximationBound.trans (boundMonotone.trans
    (cell.affineApproximationBound_le residualPositive))

/-- The same controlled approximation meets the fixed clamp-distance budget
independently of the requested residual threshold. -/
theorem InputEventCell.controlledApproximation_clampDistance
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {residualThreshold : ℚ} (residualPositive : 0 < residualThreshold) :
    let epsilon := cell.controlledApproximationWidth clearance residualThreshold
    let point := path.value
      (cell.clearedApproximation epsilon
        (cell.controlledApproximationWidth_pos clearance
          residualPositive)).refined.interval.lower
    CCL.GaussianRat.normSq (point - clampToBox box point) <
      cell.interiorSpatialThreshold clearance := by
  let epsilon := cell.controlledApproximationWidth clearance residualThreshold
  let spatialThreshold := cell.interiorSpatialThreshold clearance
  let boxWidth := cell.boxApproximationWidth spatialThreshold
  let point := path.value
    (cell.clearedApproximation epsilon
      (cell.controlledApproximationWidth_pos clearance
        residualPositive)).refined.interval.lower
  have epsilonPositive : 0 < epsilon :=
    cell.controlledApproximationWidth_pos clearance residualPositive
  have boxWidthPositive : 0 < boxWidth :=
    cell.boxApproximationWidth_pos
      (cell.interiorSpatialThreshold_pos clearance)
  have epsilonLeBox : epsilon ≤ boxWidth := min_le_right _ _
  have epsilonSquareLeBox : epsilon ^ 2 ≤ boxWidth ^ 2 := by
    nlinarith
  rcases cell.clearedApproximation_boxSlack epsilon epsilonPositive with
    ⟨xLower, xUpper, yLower, yUpper⟩
  have rawClampDistance :
      CCL.GaussianRat.normSq (point - clampToBox box point) <
        3 * cell.boxApproximationMargin epsilon ^ 2 := by
    exact normSq_sub_clampToBox_lt_of_coordinate_slack
      (cell.boxApproximationMargin_pos epsilonPositive)
      xLower xUpper yLower yUpper
  have clampDistance :
      CCL.GaussianRat.normSq (point - clampToBox box point) <
        spatialThreshold := by
    calc
      CCL.GaussianRat.normSq (point - clampToBox box point) <
          3 * cell.boxApproximationMargin epsilon ^ 2 := rawClampDistance
      _ = cell.boxApproximationDistanceCoefficient * epsilon ^ 2 :=
        cell.boxApproximationDistance_eq epsilon
      _ ≤ cell.boxApproximationDistanceCoefficient * boxWidth ^ 2 :=
        mul_le_mul_of_nonneg_left epsilonSquareLeBox
          cell.boxApproximationDistanceCoefficient_pos.le
      _ = 3 * cell.boxApproximationMargin boxWidth ^ 2 :=
        (cell.boxApproximationDistance_eq boxWidth).symm
      _ < spatialThreshold :=
        cell.boxApproximationDistance_lt
          (cell.interiorSpatialThreshold_pos clearance)
  exact clampDistance

/-- Any controlled residual request below one sixteenth of the boundary
clearance produces a rational event point strictly inside the box. -/
theorem InputEventCell.controlledApproximation_strictContains
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {residualThreshold : ℚ} (residualPositive : 0 < residualThreshold)
    (residualLe : residualThreshold ≤ clearance.bound / 16) :
    let epsilon := cell.controlledApproximationWidth clearance residualThreshold
    box.StrictContains (path.value
      (cell.clearedApproximation epsilon
        (cell.controlledApproximationWidth_pos clearance
          residualPositive)).refined.interval.lower) := by
  let epsilon := cell.controlledApproximationWidth clearance residualThreshold
  let point := path.value
    (cell.clearedApproximation epsilon
      (cell.controlledApproximationWidth_pos clearance
        residualPositive)).refined.interval.lower
  have residualBound : CCL.GaussianRat.normSq (p.eval point) ≤
      residualThreshold :=
    cell.controlledApproximation_residual_le clearance residualPositive
  have pointResidual : CCL.GaussianRat.normSq (p.eval point) <
      clearance.bound / 8 := by
    nlinarith [clearance.positive]
  have clampDistance :=
    cell.controlledApproximation_clampDistance clearance residualPositive
  exact strictContains_of_clamp clearance
    (cell.interiorSpatialThreshold_le_one clearance) clampDistance
    pointResidual (cell.interiorSpatialThreshold_distanceBudget clearance)

/-- Quantitative form: the controlled approximation has the uniform
clearance-derived four-radius gap from every box side. -/
theorem InputEventCell.controlledApproximation_deepInside
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box)
    {residualThreshold : ℚ} (residualPositive : 0 < residualThreshold)
    (residualLe : residualThreshold ≤ clearance.bound / 16) :
    let epsilon := cell.controlledApproximationWidth clearance residualThreshold
    let point := path.value
      (cell.clearedApproximation epsilon
        (cell.controlledApproximationWidth_pos clearance
          residualPositive)).refined.interval.lower
    let radius := boundaryInteriorRadius p box clearance
    box.xLower + 4 * radius < point.re ∧
      point.re < box.xUpper - 4 * radius ∧
      box.yLower + 4 * radius < point.im ∧
      point.im < box.yUpper - 4 * radius := by
  let epsilon := cell.controlledApproximationWidth clearance residualThreshold
  let point := path.value
    (cell.clearedApproximation epsilon
      (cell.controlledApproximationWidth_pos clearance
        residualPositive)).refined.interval.lower
  have strict := cell.controlledApproximation_strictContains clearance
    residualPositive residualLe
  have residual : CCL.GaussianRat.normSq (p.eval point) ≤
      clearance.bound / 16 :=
    (cell.controlledApproximation_residual_le clearance
      residualPositive).trans residualLe
  exact deepInside_of_small_residual clearance strict residual

/-- Default controlled width using one sixteenth of boundary clearance. -/
def InputEventCell.interiorApproximationWidth
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  cell.controlledApproximationWidth clearance (clearance.bound / 16)

theorem InputEventCell.interiorApproximationWidth_pos
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    0 < cell.interiorApproximationWidth clearance :=
  cell.controlledApproximationWidth_pos clearance
    (div_pos clearance.positive (by norm_num))

/-- The selected algebraic event has an explicitly computed rational curve
point strictly inside the retained winding-one box. -/
theorem InputEventCell.clearedApproximation_strictContains
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    let epsilon := cell.interiorApproximationWidth clearance
    box.StrictContains (path.value
      (cell.clearedApproximation epsilon
        (cell.interiorApproximationWidth_pos clearance)).refined.interval.lower) := by
  simpa only [InputEventCell.interiorApproximationWidth] using
    cell.controlledApproximation_strictContains clearance
      (div_pos clearance.positive (by norm_num)) le_rfl

theorem InputEventCell.polynomial_eval_eq_zero
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    p.eval (path.value t) = 0 :=
  event.polynomial_eval_eq_zero (cell.original_event_zero eventZero)

theorem InputEventCell.contains
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    box.Contains (path.value t) := by
  have rootLower : (ownerRoot event).interval.lower ≤ t :=
    cell.signRefines.1.trans lower
  have rootUpper : t ≤ (ownerRoot event).interval.upper :=
    upper.trans cell.signRefines.2
  exact event.contains rootLower rootUpper
    (cell.original_event_zero eventZero)

/-- The exact false/true child bits on one re-isolated owner cell. -/
def InputEventCell.ownerChecks
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : Bool × Bool :=
  eventFormulaPairCheck cell.branch cell.parent

/-- Algebraic owner uniqueness for any phase admitting the structural
exclusive-child certificate.  This statement uses only the isolated factor
and its canonical sign oracle, so it applies whether or not that factor has a
rational zero. -/
theorem InputEventCell.ownerChecks_ne_both_of_oracleExclusive
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (exclusive : OracleExclusivePhase state.phase) :
    cell.ownerChecks ≠ (true, true) :=
  inputEventPairCheck_ne_both_of_oracleExclusive state path
    cell.branch cell.parent exclusive

/-- Algebraic event-owner uniqueness in every raw-parser phase, without
realizing the isolated event root in any ordered extension of `ℚ`. -/
theorem InputEventCell.ownerChecks_ne_both_algebraic
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    cell.ownerChecks ≠ (true, true) :=
  inputEventPairCheck_ne_both state path cell.branch cell.parent

theorem InputEventCell.false_ownerCheck_iff
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    cell.ownerChecks.1 = true ↔
      (inputAdvanceFormula state false).Holds (path.value t) :=
  eventFormulaPairCheck_left_iff cell.branch cell.parent lower upper eventZero
    (cell.path_denominator_ne eventZero)

theorem InputEventCell.true_ownerCheck_iff
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0) :
    cell.ownerChecks.2 = true ↔
      (inputAdvanceFormula state true).Holds (path.value t) :=
  eventFormulaPairCheck_right_iff cell.branch cell.parent lower upper eventZero
    (cell.path_denominator_ne eventZero)

/-- Formula disjointness rules out the two-owner truth table at every
rational event zero where the inverse-decoder affine chart is defined.  No
represented-state hypothesis is needed. -/
theorem InputEventCell.ownerChecks_ne_both_at_zero
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0)
    (inverseDenominator :
      (adjugate state.matrix).c * path.value t +
        (adjugate state.matrix).d ≠ 0) :
    cell.ownerChecks ≠ (true, true) := by
  intro both
  have falseCheck : cell.ownerChecks.1 = true := by rw [both]
  have trueCheck : cell.ownerChecks.2 = true := by rw [both]
  have impossible : false = true :=
    inputAdvanceFormula_unique_at state (path.value t)
      inverseDenominator
      ((cell.false_ownerCheck_iff lower upper eventZero).mp falseCheck)
      ((cell.true_ownerCheck_iff lower upper eventZero).mp trueCheck)
  exact Bool.false_ne_true impossible

/-- Parser uniqueness rules out the two-owner truth table at every
represented event zero. -/
theorem InputEventCell.ownerChecks_ne_both
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * path.value t +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) (path.value t))) :
    cell.ownerChecks ≠ (true, true) := by
  intro both
  have falseCheck : cell.ownerChecks.1 = true := by rw [both]
  have trueCheck : cell.ownerChecks.2 = true := by rw [both]
  have impossible : false = true :=
    inputAdvanceFormula_unique state (path.value t) stateDeterminant
      inverseDenominator holds
      ((cell.false_ownerCheck_iff lower upper eventZero).mp falseCheck)
      ((cell.true_ownerCheck_iff lower upper eventZero).mp trueCheck)
  exact Bool.false_ne_true impossible

/-- The three possible owner truth tables after the parser's impossible
two-owner case has been removed. -/
inductive ResolvedEventOwner : Bool × Bool → Type where
  | neither : ResolvedEventOwner (false, false)
  | falseOwner : ResolvedEventOwner (true, false)
  | trueOwner : ResolvedEventOwner (false, true)

/-- Exact finite owner classification directly from the isolated algebraic
event and its canonical rational sign oracle. -/
def InputEventCell.resolveOwnerChecksAlgebraic
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    ResolvedEventOwner cell.ownerChecks := by
  cases falseCheck : cell.ownerChecks.1 with
  | false =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          have checks : cell.ownerChecks = (false, false) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .neither
      | true =>
          have checks : cell.ownerChecks = (false, true) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .trueOwner
  | true =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          have checks : cell.ownerChecks = (true, false) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .falseOwner
      | true =>
          exact (cell.ownerChecks_ne_both_algebraic (by
            apply Prod.ext
            · exact falseCheck
            · exact trueCheck)).elim

/-- Exact finite owner classification at a represented event zero.  The
`neither` case is retained because it is interpreted as terminal only after
the coupled track state supplies its terminal alternative. -/
def InputEventCell.resolveOwnerChecks
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * path.value t +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) (path.value t))) :
    ResolvedEventOwner cell.ownerChecks := by
  cases falseCheck : cell.ownerChecks.1 with
  | false =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          have checks : cell.ownerChecks = (false, false) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .neither
      | true =>
          have checks : cell.ownerChecks = (false, true) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .trueOwner
  | true =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          have checks : cell.ownerChecks = (true, false) :=
            Prod.ext falseCheck trueCheck
          rw [checks]
          exact .falseOwner
      | true =>
          exact (cell.ownerChecks_ne_both lower upper eventZero
            stateDeterminant inverseDenominator holds (by
              apply Prod.ext
              · exact falseCheck
              · exact trueCheck)).elim

/-- Pointwise semantic form of a resolved event truth table.  `neither` is
kept distinct from `next` because the coupled controller interprets it as a
terminal result only after exact reconstruction. -/
inductive EventFormulaDecision
    (state : RawParser.State) (input : CCL.GaussianRat) where
  | neither
      (none : ∀ bit, ¬(inputAdvanceFormula state bit).Holds input)
  | next (bit : Bool)
      (holds : (inputAdvanceFormula state bit).Holds input)
      (otherFails : ¬(inputAdvanceFormula state (!bit)).Holds input)

/-- Resolve the computed pair all the way to the original child formulas at
one represented event zero. -/
def InputEventCell.resolveFormulaDecision
    {p : CCLBranchEvent.GaussianPolynomial}
    {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper)
    (eventZero : cell.branch.factor.polynomial.eval t = 0)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * path.value t +
        (adjugate state.matrix).d ≠ 0)
    (holds : state.Holds
      (RatBox.homographic (adjugate state.matrix) (path.value t))) :
    EventFormulaDecision state (path.value t) := by
  cases falseCheck : cell.ownerChecks.1 with
  | false =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          exact .neither (by
            intro bit
            cases bit with
            | false =>
                intro falseHolds
                have check := (cell.false_ownerCheck_iff lower upper
                  eventZero).mpr falseHolds
                rw [falseCheck] at check
                contradiction
            | true =>
                intro trueHolds
                have check := (cell.true_ownerCheck_iff lower upper
                  eventZero).mpr trueHolds
                rw [trueCheck] at check
                contradiction)
      | true =>
          exact .next true
            ((cell.true_ownerCheck_iff lower upper eventZero).mp trueCheck)
            (by
              simpa using fun falseHolds => by
                have check := (cell.false_ownerCheck_iff lower upper
                  eventZero).mpr falseHolds
                rw [falseCheck] at check
                contradiction)
  | true =>
      cases trueCheck : cell.ownerChecks.2 with
      | false =>
          exact .next false
            ((cell.false_ownerCheck_iff lower upper eventZero).mp falseCheck)
            (by
              simpa using fun trueHolds => by
                have check := (cell.true_ownerCheck_iff lower upper
                  eventZero).mpr trueHolds
                rw [trueCheck] at check
                contradiction)
      | true =>
          exact (cell.ownerChecks_ne_both lower upper eventZero
            stateDeterminant inverseDenominator holds (by
              apply Prod.ext
              · exact falseCheck
              · exact trueCheck)).elim

/-! ## Source-labelled finite owner families -/

/-- Retain the guarded chart and planned boundary source alongside one
re-isolated parser-owner cell. -/
structure SourceInputEventCell
    (p : CCLBranchEvent.GaussianPolynomial) (box : RatBox)
    (state : RawParser.State) where
  sourceEvent : SourceRelevantCurveEvent p box
  conditions : List RatPolynomial
  conditions_eq :
    inputEventPolynomials state sourceEvent.partition.entry.chart.path =
      conditions
  cell : ClassifiedEventCell conditions sourceEvent.event.branch.factor
    (ownerRoot sourceEvent.event)

/-- Recover the parser-specialized cell after keeping its potentially large
condition index abstract in the source-labelled record. -/
def SourceInputEventCell.inputCell
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {state : RawParser.State} (candidate : SourceInputEventCell p box state) :
    InputEventCell state candidate.sourceEvent.event := by
  change ClassifiedEventCell
    (inputEventPolynomials state
      candidate.sourceEvent.partition.entry.chart.path)
    candidate.sourceEvent.event.branch.factor
    (ownerRoot candidate.sourceEvent.event)
  rw [candidate.conditions_eq]
  exact candidate.cell

def sourceInputEventCells
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceRelevantCurveEvent p box) :
    List (SourceInputEventCell p box state) :=
  (inputEventCells state sourceEvent.event).map fun cell =>
    { sourceEvent := sourceEvent
      conditions := inputEventPolynomials state
        sourceEvent.partition.entry.chart.path
      conditions_eq := rfl
      cell := cell }

/-- Parser-owner re-isolation of a cell-local relevant event, retaining the
exact terminal guard-cell provenance needed for its count decision. -/
structure SourceGuardInputEventCell
    (p : CCLBranchEvent.GaussianPolynomial) (box : RatBox)
    (state : RawParser.State) where
  sourceEvent : SourceGuardCurveEvent p box
  conditions : List RatPolynomial
  conditions_eq : inputEventPolynomials state
    sourceEvent.sourceCell.partition.entry.chart.path = conditions
  cell : ClassifiedEventCell conditions sourceEvent.event.branch.factor
    (ownerRoot sourceEvent.event)

def SourceGuardInputEventCell.inputCell
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {state : RawParser.State}
    (candidate : SourceGuardInputEventCell p box state) :
    InputEventCell state candidate.sourceEvent.event := by
  change ClassifiedEventCell
    (inputEventPolynomials state
      candidate.sourceEvent.sourceCell.partition.entry.chart.path)
    candidate.sourceEvent.event.branch.factor
    (ownerRoot candidate.sourceEvent.event)
  rw [candidate.conditions_eq]
  exact candidate.cell

def sourceGuardInputEventCells
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceGuardCurveEvent p box) :
    List (SourceGuardInputEventCell p box state) :=
  (inputEventCells state sourceEvent.event).map fun cell =>
    { sourceEvent := sourceEvent
      conditions := inputEventPolynomials state
        sourceEvent.sourceCell.partition.entry.chart.path
      conditions_eq := rfl
      cell := cell }

def sourceGuardInputEventCellsOfEvents
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State)
    (events : List (SourceGuardCurveEvent p box)) :
    List (SourceGuardInputEventCell p box state) :=
  events.flatMap (sourceGuardInputEventCells state)

theorem sourceGuardInputEventCells_ne_nil
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceGuardCurveEvent p box) :
    sourceGuardInputEventCells state sourceEvent ≠ [] := by
  intro empty
  apply inputEventCells_ne_nil state sourceEvent.event
  exact List.map_eq_nil_iff.mp (by
    simpa only [sourceGuardInputEventCells] using empty)

/-- Every retained cell-local relevant event contributes at least one actual
parser-owner cell to the flattened guarded family, even for a nonrational
algebraic event. -/
theorem sourceGuardInputEventCellsOfEvents_exists_of_mem
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State)
    (events : List (SourceGuardCurveEvent p box))
    (sourceEvent : SourceGuardCurveEvent p box)
    (sourceMember : sourceEvent ∈ events) :
    ∃ candidate ∈ sourceGuardInputEventCellsOfEvents state events,
      candidate.sourceEvent = sourceEvent := by
  rcases List.exists_mem_of_ne_nil _
      (sourceGuardInputEventCells_ne_nil state sourceEvent) with
    ⟨candidate, candidateMember⟩
  have sourceEquality : candidate.sourceEvent = sourceEvent := by
    rw [sourceGuardInputEventCells, List.mem_map] at candidateMember
    rcases candidateMember with ⟨cell, _cellMember, equality⟩
    cases equality
    rfl
  refine ⟨candidate, ?_, sourceEquality⟩
  rw [sourceGuardInputEventCellsOfEvents, List.mem_flatMap]
  exact ⟨sourceEvent, sourceMember, candidateMember⟩

theorem SourceGuardInputEventCell.sourceEvent_mem_of_mem
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {state : RawParser.State}
    {events : List (SourceGuardCurveEvent p box)}
    {candidate : SourceGuardInputEventCell p box state}
    (member : candidate ∈ sourceGuardInputEventCellsOfEvents state events) :
    candidate.sourceEvent ∈ events := by
  rw [sourceGuardInputEventCellsOfEvents, List.mem_flatMap] at member
  rcases member with ⟨sourceEvent, sourceEventMember, cellMember⟩
  rw [sourceGuardInputEventCells, List.mem_map] at cellMember
  rcases cellMember with ⟨cell, _cellMember, equality⟩
  cases equality
  exact sourceEventMember

theorem sourceGuardCurveEvent_sourceCell_mem_of_mem
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    {candidate : SourceGuardCurveEvent p box}
    (member : candidate ∈
      guardCurveEventsOfSourceEventGuardCells sourceCells) :
    candidate.sourceCell ∈ sourceCells := by
  rw [guardCurveEventsOfSourceEventGuardCells, List.mem_flatMap] at member
  rcases member with ⟨sourceCell, sourceCellMember, eventMember⟩
  rw [guardCurveEventsOfSourceEventGuardCell, List.mem_map] at eventMember
  rcases eventMember with ⟨event, _eventMember, equality⟩
  cases equality
  exact sourceCellMember

theorem sourceEventGuardCell_partition_mem_of_mem
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {candidate : SourceEventGuardCell p box}
    (member : candidate ∈ eventGuardCellsOfSourcePartitions partitions) :
    candidate.partition ∈ partitions := by
  rw [eventGuardCellsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨partition, partitionMember, cellMember⟩
  rw [eventGuardCellsOfSourcePartition, List.mem_map] at cellMember
  rcases cellMember with ⟨cell, _cellMember, equality⟩
  cases equality
  exact partitionMember

def SourceGuardInputEventCell.decideSourceCount
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {state : RawParser.State}
    (candidate : SourceGuardInputEventCell p box state) :
    CurveEventCountDecision p
      candidate.sourceEvent.sourceCell.partition.entry.chart.path box
      candidate.sourceEvent.event :=
  candidate.sourceEvent.decideCount

theorem sourceInputEventCells_covers
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceRelevantCurveEvent p box)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    ∃ candidate ∈ sourceInputEventCells state sourceEvent,
      candidate.cell.parent.interval.lower ≤ t ∧
        t ≤ candidate.cell.parent.interval.upper ∧
        candidate.cell.branch.factor.polynomial.eval t = 0 := by
  rcases inputEventCells_covers state sourceEvent.event lower upper eventZero with
    ⟨cell, cellMember, cellLower, cellUpper, cellZero⟩
  let candidate : SourceInputEventCell p box state :=
    { sourceEvent := sourceEvent
      conditions := inputEventPolynomials state
        sourceEvent.partition.entry.chart.path
      conditions_eq := rfl
      cell := cell }
  refine ⟨candidate, ?_, cellLower, cellUpper, cellZero⟩
  rw [sourceInputEventCells, List.mem_map]
  exact ⟨cell, cellMember, rfl⟩

/-- Source labelling preserves coverage through the final parser-formula sign
refinement. -/
theorem sourceInputEventCells_covers_refined
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceRelevantCurveEvent p box)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    ∃ candidate ∈ sourceInputEventCells state sourceEvent,
      (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.lower ≤ t ∧
      t ≤ (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.upper ∧
      candidate.inputCell.branch.factor.polynomial.eval t = 0 := by
  rcases inputEventCells_covers_refined state sourceEvent.event lower upper
      eventZero with
    ⟨cell, cellMember, cellLower, cellUpper, cellZero⟩
  let candidate : SourceInputEventCell p box state :=
    { sourceEvent := sourceEvent
      conditions := inputEventPolynomials state
        sourceEvent.partition.entry.chart.path
      conditions_eq := rfl
      cell := cell }
  refine ⟨candidate, ?_, ?_, ?_, ?_⟩
  · rw [sourceInputEventCells, List.mem_map]
    exact ⟨cell, cellMember, rfl⟩
  · exact cellLower
  · exact cellUpper
  · exact cellZero

theorem sourceInputEventCells_ne_nil_of_rational_zero
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State) (sourceEvent : SourceRelevantCurveEvent p box)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    sourceInputEventCells state sourceEvent ≠ [] := by
  rcases sourceInputEventCells_covers state sourceEvent lower upper eventZero with
    ⟨candidate, member, _cellLower, _cellUpper, _cellZero⟩
  exact List.ne_nil_of_mem member

/-- Flatten parser-owner re-isolation over an arbitrary finite family of
source-labelled relevant events. -/
def sourceInputEventCellsOfEvents
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State)
    (events : List (SourceRelevantCurveEvent p box)) :
    List (SourceInputEventCell p box state) :=
  events.flatMap (sourceInputEventCells state)

/-- Flattening over source events preserves rational-zero coverage and its
exact source label. -/
theorem sourceInputEventCellsOfEvents_covers
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    (state : RawParser.State)
    (events : List (SourceRelevantCurveEvent p box))
    (sourceEvent : SourceRelevantCurveEvent p box)
    (sourceMember : sourceEvent ∈ events)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    ∃ candidate ∈ sourceInputEventCellsOfEvents state events,
      candidate.sourceEvent = sourceEvent ∧
        candidate.cell.parent.interval.lower ≤ t ∧
        t ≤ candidate.cell.parent.interval.upper ∧
        candidate.cell.branch.factor.polynomial.eval t = 0 := by
  rcases sourceInputEventCells_covers state sourceEvent lower upper eventZero with
    ⟨candidate, candidateMember, cellLower, cellUpper, cellZero⟩
  refine ⟨candidate, ?_, ?_, cellLower, cellUpper, cellZero⟩
  · rw [sourceInputEventCellsOfEvents, List.mem_flatMap]
    exact ⟨sourceEvent, sourceMember, candidateMember⟩
  · rw [sourceInputEventCells, List.mem_map] at candidateMember
    rcases candidateMember with ⟨cell, _cellMember, equality⟩
    cases equality
    rfl

theorem SourceInputEventCell.sourceEvent_mem_of_mem
    {p : CCLBranchEvent.GaussianPolynomial} {box : RatBox}
    {state : RawParser.State}
    {events : List (SourceRelevantCurveEvent p box)}
    {candidate : SourceInputEventCell p box state}
    (member : candidate ∈ sourceInputEventCellsOfEvents state events) :
    candidate.sourceEvent ∈ events := by
  rw [sourceInputEventCellsOfEvents, List.mem_flatMap] at member
  rcases member with ⟨sourceEvent, sourceEventMember, cellMember⟩
  rw [sourceInputEventCells, List.mem_map] at cellMember
  rcases cellMember with ⟨cell, _cellMember, equality⟩
  cases equality
  exact sourceEventMember

/-- The complete finite owner-cell family generated by the denominator-
separated charts of one parser state. -/
def separatedInputEventCells
    {ambient : RatBox} (p : CCLBranchEvent.GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceInputEventCell p output.state.box state) :=
  sourceInputEventCellsOfEvents state
    (separatedRelevantCurveEvents p state output)

/-- Parser-owner cells generated directly from the source-labelled terminal
guard-event family, retaining local count evidence. -/
def separatedGuardInputEventCells
    {ambient : RatBox} (p : CCLBranchEvent.GaussianPolynomial)
    {current : WindingOneState p ambient} (state : RawParser.State)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)) :
    List (SourceGuardInputEventCell p output.state.box state) :=
  sourceGuardInputEventCellsOfEvents state
    (separatedSourceGuardCurveEvents p state output)

theorem separatedGuardInputEventCells_exists_of_sourceEvent_mem
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (sourceEvent : SourceGuardCurveEvent p output.state.box)
    (sourceMember : sourceEvent ∈
      separatedSourceGuardCurveEvents p state output) :
    ∃ candidate ∈ separatedGuardInputEventCells p state output,
      candidate.sourceEvent = sourceEvent := by
  simpa only [separatedGuardInputEventCells] using
    sourceGuardInputEventCellsOfEvents_exists_of_mem state
      (separatedSourceGuardCurveEvents p state output) sourceEvent sourceMember

/-- Every exact rational zero represented by a retained separated event is
covered by a source-labelled parser-owner cell in the final finite family. -/
theorem separatedInputEventCells_covers
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (sourceEvent : SourceRelevantCurveEvent p output.state.box)
    (sourceMember : sourceEvent ∈
      separatedRelevantCurveEvents p state output)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    ∃ candidate ∈ separatedInputEventCells p state output,
      candidate.sourceEvent = sourceEvent ∧
        candidate.cell.parent.interval.lower ≤ t ∧
        t ≤ candidate.cell.parent.interval.upper ∧
        candidate.cell.branch.factor.polynomial.eval t = 0 := by
  simpa only [separatedInputEventCells] using
    sourceInputEventCellsOfEvents_covers state
      (separatedRelevantCurveEvents p state output) sourceEvent sourceMember
      lower upper eventZero

/-- Final separated owner cells retain the rational zero through their parser
formula sign refinement. -/
theorem separatedInputEventCells_covers_refined
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (sourceEvent : SourceRelevantCurveEvent p output.state.box)
    (sourceMember : sourceEvent ∈
      separatedRelevantCurveEvents p state output)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    ∃ candidate ∈ separatedInputEventCells p state output,
      candidate.sourceEvent = sourceEvent ∧
      (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.lower ≤ t ∧
      t ≤ (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.upper ∧
      candidate.inputCell.branch.factor.polynomial.eval t = 0 := by
  rcases sourceInputEventCells_covers_refined state sourceEvent lower upper
      eventZero with
    ⟨candidate, candidateMember, cellLower, cellUpper, cellZero⟩
  refine ⟨candidate, ?_, ?_, cellLower, cellUpper, cellZero⟩
  · rw [separatedInputEventCells, sourceInputEventCellsOfEvents,
      List.mem_flatMap]
    exact ⟨sourceEvent, sourceMember, candidateMember⟩
  · rw [sourceInputEventCells, List.mem_map] at candidateMember
    rcases candidateMember with ⟨cell, _cellMember, equality⟩
    cases equality
    rfl

/-- End-to-end rational chart-root coverage: a non-identically-zero root in a
separated source chart reaches one final parser-owner cell, and the returned
sign-refined interval still contains its exact parameter. -/
theorem separatedInputEventCells_covers_chart_root_nonzero
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (partition : SourceChartPartition p output.state.box)
    (partitionMember : partition ∈ separatedChartPartitions p state output)
    {t : ℚ} (lower : partition.entry.chart.interval.lower ≤ t)
    (upper : t ≤ partition.entry.chart.interval.upper)
    (clearedNonzero :
      (clearedReal p partition.entry.chart.path).isZero = false ∨
      (clearedImag p partition.entry.chart.path).isZero = false)
    (pathDenominator : partition.entry.chart.path.denominator.eval
      (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (partition.entry.chart.path.value t) = 0)
    (contains : output.state.box.Contains
      (partition.entry.chart.path.value t)) :
    ∃ candidate ∈ separatedInputEventCells p state output,
      candidate.sourceEvent.partition = partition ∧
      (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.lower ≤ t ∧
      t ≤ (candidate.inputCell.branch.computeEventSigns
        candidate.inputCell.parent).refined.interval.upper ∧
      candidate.inputCell.branch.factor.polynomial.eval t = 0 := by
  rcases separatedRelevantCurveEvents_covers_root_nonzero partition
      partitionMember lower upper clearedNonzero pathDenominator polynomialZero
      contains with
    ⟨sourceEvent, sourceMember, sourcePartition, eventLower, eventUpper,
      eventZero⟩
  have ownerLower : (ownerRoot sourceEvent.event).interval.lower ≤ t := by
    simpa only [ownerRoot] using eventLower
  have ownerUpper : t ≤ (ownerRoot sourceEvent.event).interval.upper := by
    simpa only [ownerRoot] using eventUpper
  rcases separatedInputEventCells_covers_refined sourceEvent sourceMember
      ownerLower ownerUpper eventZero with
    ⟨candidate, candidateMember, candidateSource, cellLower, cellUpper,
      cellZero⟩
  refine ⟨candidate, candidateMember, ?_, cellLower, cellUpper, cellZero⟩
  rw [candidateSource, sourcePartition]

theorem separatedInputEventCells_ne_nil_of_rational_zero
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (sourceEvent : SourceRelevantCurveEvent p output.state.box)
    (sourceMember : sourceEvent ∈
      separatedRelevantCurveEvents p state output)
    {t : ℚ} (lower : (ownerRoot sourceEvent.event).interval.lower ≤ t)
    (upper : t ≤ (ownerRoot sourceEvent.event).interval.upper)
    (eventZero : sourceEvent.event.branch.factor.polynomial.eval t = 0) :
    separatedInputEventCells p state output ≠ [] := by
  rcases separatedInputEventCells_covers sourceEvent sourceMember lower upper
      eventZero with
    ⟨candidate, member, _source, _cellLower, _cellUpper, _cellZero⟩
  exact List.ne_nil_of_mem member

theorem SourceInputEventCell.sourceEvent_mem_separated
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceInputEventCell p output.state.box state}
    (member : candidate ∈ separatedInputEventCells p state output) :
    candidate.sourceEvent ∈ separatedRelevantCurveEvents p state output :=
  candidate.sourceEvent_mem_of_mem (by
    simpa only [separatedInputEventCells] using member)

/-- Every source-labelled parser-owner cell exposes the complete curve-event
count decision inherited from its denominator-separated guarded chart. -/
def SourceInputEventCell.decideSourceCount
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (candidate : SourceInputEventCell p output.state.box state)
    (member : candidate ∈ separatedInputEventCells p state output) :
    CurveEventCountDecision p
      candidate.sourceEvent.partition.entry.chart.path output.state.box
      candidate.sourceEvent.event :=
  CCLBranchEvidence.SourceRelevantCurveEvent.decideSeparatedCount
    candidate.sourceEvent
    (candidate.sourceEvent_mem_separated member)

theorem SourceInputEventCell.source_mem_inputPlan
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceInputEventCell p output.state.box state}
    (member : candidate ∈ separatedInputEventCells p state output) :
    candidate.sourceEvent.partition.entry.source ∈ inputPlan state :=
  separatedRelevantCurveEvent_source_mem_inputPlan
    (candidate.sourceEvent_mem_separated member)

theorem SourceInputEventCell.source_determinant_ne
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceInputEventCell p output.state.box state}
    (member : candidate ∈ separatedInputEventCells p state output) :
    determinant candidate.sourceEvent.partition.entry.source.matrix ≠ 0 :=
  separatedRelevantCurveEvent_determinant_ne stateDeterminant
    (candidate.sourceEvent_mem_separated member)

/-- At every represented zero of a separated owner cell, the retained
planned source really is its exact Hermitian boundary. -/
theorem SourceInputEventCell.source_onBoundary
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceInputEventCell p output.state.box state}
    (member : candidate ∈ separatedInputEventCells p state output)
    {t : ℚ}
    (eventZero : candidate.inputCell.branch.factor.polynomial.eval t = 0) :
    candidate.sourceEvent.partition.entry.source.form.eval
        (candidate.sourceEvent.partition.entry.chart.path.value t) = 0 :=
    candidate.sourceEvent.partition.entry.onBoundary
    (candidate.source_determinant_ne stateDeterminant member)
    (candidate.inputCell.path_denominator_ne eventZero)

/-! ## Guarded source-cell provenance -/

theorem SourceGuardInputEventCell.sourceEvent_mem_separated
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output) :
    candidate.sourceEvent ∈ separatedSourceGuardCurveEvents p state output :=
  candidate.sourceEvent_mem_of_mem (by
    simpa only [separatedGuardInputEventCells] using member)

theorem SourceGuardInputEventCell.sourceCell_mem_separated
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output) :
    candidate.sourceEvent.sourceCell ∈
      separatedEventGuardCells p state output :=
  sourceGuardCurveEvent_sourceCell_mem_of_mem (by
    simpa only [separatedSourceGuardCurveEvents] using
      candidate.sourceEvent_mem_separated member)

theorem SourceGuardInputEventCell.source_entry_mem_separated
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output) :
    candidate.sourceEvent.sourceCell.partition.entry ∈
      separatedCharts state output := by
  have partitionMember : candidate.sourceEvent.sourceCell.partition ∈
      separatedChartPartitions p state output :=
    sourceEventGuardCell_partition_mem_of_mem (by
      simpa only [separatedEventGuardCells] using
        candidate.sourceCell_mem_separated member)
  exact SourceChartPartition.entry_mem_of_mem_build (by
    simpa only [separatedChartPartitions] using partitionMember)

theorem SourceGuardInputEventCell.source_mem_inputPlan
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output) :
    candidate.sourceEvent.sourceCell.partition.entry.source ∈ inputPlan state :=
  separatedChart_source_mem_inputPlan
    (candidate.source_entry_mem_separated member)

theorem SourceGuardInputEventCell.source_determinant_ne
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output) :
    determinant
      candidate.sourceEvent.sourceCell.partition.entry.source.matrix ≠ 0 :=
  separatedChart_determinant_ne stateDeterminant
    (candidate.source_entry_mem_separated member)

theorem SourceGuardInputEventCell.source_onBoundary
    {p : CCLBranchEvent.GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (stateDeterminant : determinant state.matrix ≠ 0)
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {candidate : SourceGuardInputEventCell p output.state.box state}
    (member : candidate ∈ separatedGuardInputEventCells p state output)
    {t : ℚ}
    (eventZero : candidate.inputCell.branch.factor.polynomial.eval t = 0) :
    candidate.sourceEvent.sourceCell.partition.entry.source.form.eval
        (candidate.sourceEvent.sourceCell.partition.entry.chart.path.value t) =
      0 :=
  candidate.sourceEvent.sourceCell.partition.entry.onBoundary
    (candidate.source_determinant_ne stateDeterminant member)
    (candidate.inputCell.path_denominator_ne eventZero)

end CCLBranchEventOwner
end FTA
