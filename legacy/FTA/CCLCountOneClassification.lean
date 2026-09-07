import FTA.CCLIntersectionSharedFactors
import FTA.RootCountDivisibility

/-!
# Following one algebraic event through finite condition splits

The generic shared-factor classifier returns every factor branch.  At a
count-one event interval, exactly one branch is needed by later owner
constructions.  This module follows such a branch without realizing a real
root: if every gcd child had zero Sturm count, their coefficient-computed
positive lower bounds would give a positive lower bound for the count-one
parent, contradicting finite count-one refinement.
-/

namespace FTA
namespace CCLCountOneClassification

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLIntersectionSharedFactors
open FTA.DenseSquarefree
open FTA.PositiveLowerBound
open FTA.RootCountDivisibility
open FTA.SquarefreeFactorization
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

private theorem divisor_endpoint_ne
    {small large : RatPolynomial}
    (divides : small.toPolynomial ∣ large.toPolynomial) {t : ℚ}
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

/-- At least one child of a one-condition gcd split has nonzero Sturm count
inside the count-one parent interval. -/
theorem refineClassifiedEventFactor_exists_count_ne_zero
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions)
    (root : CountOneInterval classified.factor.polynomial)
    (q : RatPolynomial) :
    ∃ child ∈ refineClassifiedEventFactor classified q,
      sturmRootCount2 child.factor.polynomial
        root.interval.lower root.interval.upper ≠ 0 := by
  cases split : splitCondition classified.factor.input q with
  | coprime certificate =>
      let child : ClassifiedEventFactor (q :: conditions) :=
        { factor := classified.factor
          relations := .cons (.coprime certificate) classified.relations }
      refine ⟨child, ?_, ?_⟩
      · simp [refineClassifiedEventFactor, split, child]
      · simpa only [child] using (show
          sturmRootCount2 classified.factor.polynomial root.interval.lower
            root.interval.upper ≠ 0 by
              intro zero
              rw [root.countOne] at zero
              norm_num at zero)
  | shared branch =>
      let sharedFactor : Factor :=
        { polynomial := FTA.DenseGCD.gcd classified.factor.polynomial q
          input := branch.sharedInput }
      let sharedChild : ClassifiedEventFactor (q :: conditions) :=
        { factor := sharedFactor
          relations := .cons
            (.equality (FTA.DenseGCD.gcd_toPolynomial_dvd_right
              classified.factor.polynomial q))
            (classified.relations.ofDvd branch.sharedInput
              (FTA.DenseGCD.gcd_toPolynomial_dvd_left
                classified.factor.polynomial q)) }
      have sharedLower : sharedFactor.polynomial.eval root.interval.lower ≠ 0 :=
        divisor_endpoint_ne
          (FTA.DenseGCD.gcd_toPolynomial_dvd_left
            classified.factor.polynomial q) root.lowerClear
      have sharedUpper : sharedFactor.polynomial.eval root.interval.upper ≠ 0 :=
        divisor_endpoint_ne
          (FTA.DenseGCD.gcd_toPolynomial_dvd_left
            classified.factor.polynomial q) root.upperClear
      cases residualKind : branch.residual with
      | constant degreeZero =>
          have sharedCount : sturmRootCount2 sharedFactor.polynomial
              root.interval.lower root.interval.upper ≠ 0 := by
            intro countZero
            let sharedCertificate := FTA.PositiveLowerBound.compute
              branch.sharedInput root.interval root.proper sharedLower
              sharedUpper countZero
            let scalar := (FTA.DenseGCD.leftFactor
              classified.factor.polynomial q).leadingCoeff
            have scalarNonzero : scalar ≠ 0 := by
              exact leadingCoeff_ne_zero branch.residualNonzero
            let parentCertificate : FTA.PositiveLowerBound.Certificate
                classified.factor.polynomial root.interval :=
              FTA.PositiveLowerBound.Certificate.ofScalarProduct scalar
                scalarNonzero sharedCertificate (by
                  intro t
                  have residualValue := eval_eq_leadingCoeff_of_natDegree_eq_zero
                    branch.residualNonzero degreeZero t
                  rw [branch.event_eval_identity, residualValue]
                  ring)
            exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound
              classified.factor.input root parentCertificate
          refine ⟨sharedChild, ?_, ?_⟩
          · simp [refineClassifiedEventFactor, split, residualKind,
              sharedChild, sharedFactor]
          · simpa only [sharedChild, sharedFactor] using sharedCount
      | nonconstant residualInput =>
          let residualFactor : Factor :=
            { polynomial := FTA.DenseGCD.leftFactor
                classified.factor.polynomial q
              input := residualInput }
          let residualChild : ClassifiedEventFactor (q :: conditions) :=
            { factor := residualFactor
              relations := .cons (.coprime branch.residualCoprime)
                (classified.relations.ofDvd residualInput
                  (residualFactor_toPolynomial_dvd_left
                    classified.factor.polynomial q)) }
          have residualLower :
              residualFactor.polynomial.eval root.interval.lower ≠ 0 :=
            divisor_endpoint_ne
              (residualFactor_toPolynomial_dvd_left
                classified.factor.polynomial q) root.lowerClear
          have residualUpper :
              residualFactor.polynomial.eval root.interval.upper ≠ 0 :=
            divisor_endpoint_ne
              (residualFactor_toPolynomial_dvd_left
                classified.factor.polynomial q) root.upperClear
          by_cases sharedCount : sturmRootCount2 sharedFactor.polynomial
              root.interval.lower root.interval.upper ≠ 0
          · refine ⟨sharedChild, ?_, ?_⟩
            · simp [refineClassifiedEventFactor, split, residualKind,
                sharedChild, sharedFactor]
            · simpa only [sharedChild, sharedFactor] using sharedCount
          · have sharedCountZero : sturmRootCount2 sharedFactor.polynomial
                root.interval.lower root.interval.upper = 0 :=
              not_ne_iff.mp sharedCount
            by_cases residualCount : sturmRootCount2 residualFactor.polynomial
                root.interval.lower root.interval.upper ≠ 0
            · refine ⟨residualChild, ?_, ?_⟩
              · simp [refineClassifiedEventFactor, split, residualKind,
                  residualChild, residualFactor]
              · simpa only [residualChild, residualFactor] using residualCount
            · have residualCountZero :
                  sturmRootCount2 residualFactor.polynomial
                    root.interval.lower root.interval.upper = 0 :=
                not_ne_iff.mp residualCount
              let sharedCertificate := FTA.PositiveLowerBound.compute
                branch.sharedInput root.interval root.proper sharedLower
                sharedUpper sharedCountZero
              let residualCertificate := FTA.PositiveLowerBound.compute
                residualInput root.interval root.proper residualLower
                residualUpper residualCountZero
              let productCertificate :=
                FTA.PositiveLowerBound.Certificate.mul sharedCertificate
                  residualCertificate
              let parentCertificate : FTA.PositiveLowerBound.Certificate
                  classified.factor.polynomial root.interval :=
                FTA.PositiveLowerBound.Certificate.ofScalarProduct 1 one_ne_zero
                  productCertificate (by
                    intro t
                    rw [branch.event_eval_identity]
                    change _ = 1 *
                      ((sharedFactor.polynomial * residualFactor.polynomial).eval t)
                    simp [eval_mul, sharedFactor, residualFactor])
              exact
                (FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound
                  classified.factor.input root parentCertificate).elim

/-- A re-isolated child branch selected by its nonzero count in the parent
interval. -/
structure CountOneConditionRefinement
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions)
    (root : CountOneInterval classified.factor.polynomial)
    (q : RatPolynomial) where
  child : ClassifiedEventFactor (q :: conditions)
  member : child ∈ refineClassifiedEventFactor classified q
  parent : CountOneInterval child.factor.polynomial
  refines : parent.interval.Refines root.interval

/-- Execute one condition split, select the first child with nonzero exact
count, and re-isolate its first count-one cell. -/
def refineCountOneCondition
    {conditions : List RatPolynomial}
    (classified : ClassifiedEventFactor conditions)
    (root : CountOneInterval classified.factor.polynomial)
    (q : RatPolynomial) :
    CountOneConditionRefinement classified root q := by
  let children := refineClassifiedEventFactor classified q
  let selected := children.find? fun child => decide
    (sturmRootCount2 child.factor.polynomial
      root.interval.lower root.interval.upper ≠ 0)
  have selectedSome : selected.isSome := by
    rcases refineClassifiedEventFactor_exists_count_ne_zero classified root q with
      ⟨child, member, countNonzero⟩
    apply List.find?_isSome.mpr
    exact ⟨child, member, by simpa only [decide_eq_true_eq] using countNonzero⟩
  cases selectedEq : selected with
  | none =>
      simp [selectedEq] at selectedSome
  | some child =>
      have childMember : child ∈ children :=
        List.mem_of_find?_eq_some selectedEq
      have countNonzero : sturmRootCount2 child.factor.polynomial
          root.interval.lower root.interval.upper ≠ 0 := by
        have found := List.find?_some selectedEq
        simpa only [decide_eq_true_eq] using found
      have childDivides : child.factor.polynomial.toPolynomial ∣
          classified.factor.polynomial.toPolynomial :=
        refineClassifiedEventFactor_dvd classified q childMember
      have lowerClear :
          child.factor.polynomial.eval root.interval.lower ≠ 0 :=
        divisor_endpoint_ne childDivides root.lowerClear
      have upperClear :
          child.factor.polynomial.eval root.interval.upper ≠ 0 :=
        divisor_endpoint_ne childDivides root.upperClear
      let isolation := FTA.SturmIsolation.isolate child.factor.input
        root.interval.lower root.interval.upper root.proper lowerClear upperClear
      cases transducersEq : isolation.transducers with
      | nil =>
          have countZero : sturmRootCount2 child.factor.polynomial
              root.interval.lower root.interval.upper = 0 := by
            simpa only [transducersEq, List.length_nil, Nat.cast_zero,
              mul_zero] using isolation.exactCount
          exact (countNonzero countZero).elim
      | cons parent tail =>
          exact
            { child := child
              member := by simpa only [children] using childMember
              parent := parent
              refines := isolation.refine parent (by simp [transducersEq]) }

/-- One fully classified descendant that follows the algebraic event retained
by an original count-one interval. -/
structure CountOneClassification
    (conditions : List RatPolynomial) (original : Factor)
    (root : CountOneInterval original.polynomial) where
  branch : ClassifiedEventFactor conditions
  member : branch ∈ classifyEventConditions original.input conditions
  divides : branch.factor.polynomial.toPolynomial ∣
    original.polynomial.toPolynomial
  parent : CountOneInterval branch.factor.polynomial
  refines : parent.interval.Refines root.interval

/-- Follow an arbitrary finite condition list through exact gcd splits and
re-isolation.  The recursion order matches `classifyEventConditions`, so the
result is also a member of the ordinary exhaustive classifier output. -/
def followCountOneConditions
    (original : Factor) (root : CountOneInterval original.polynomial) :
    (conditions : List RatPolynomial) →
      CountOneClassification conditions original root
  | [] =>
      { branch :=
          { factor := original
            relations := .nil }
        member := by simp [classifyEventConditions]
        divides := dvd_rfl
        parent := root
        refines := RationalInterval.refines_refl root.interval }
  | q :: conditions =>
      let previous := followCountOneConditions original root conditions
      let refined := refineCountOneCondition previous.branch previous.parent q
      { branch := refined.child
        member := by
          rw [classifyEventConditions, List.mem_flatMap]
          exact ⟨previous.branch, previous.member, refined.member⟩
        divides := dvd_trans
          (refineClassifiedEventFactor_dvd previous.branch q refined.member)
          previous.divides
        parent := refined.parent
        refines := RationalInterval.refines_trans refined.refines
          previous.refines }

/-- Following a count-one factor through the finite condition classifier
retains every exact rational zero of the original factor, both as a zero of
the selected divisor and as a point of its re-isolated parent interval. -/
theorem CountOneClassification.rationalZero_mem
    {conditions : List RatPolynomial} {original : Factor}
    {root : CountOneInterval original.polynomial}
    (classification : CountOneClassification conditions original root)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper)
    (eventZero : original.polynomial.eval t = 0) :
    classification.parent.interval.lower ≤ t ∧
      t ≤ classification.parent.interval.upper ∧
      classification.branch.factor.polynomial.eval t = 0 :=
  FTA.RootCountDivisibility.CountOneInterval.divisor_rationalZero_mem_of_refines
    classification.branch.factor.input original.input root
      classification.parent classification.divides classification.refines
        lower upper eventZero

theorem CountOneClassification.signRefines
    {conditions : List RatPolynomial} {original : Factor}
    {root : CountOneInterval original.polynomial}
    (classification : CountOneClassification conditions original root) :
    (classification.branch.computeEventSigns
      classification.parent).refined.interval.Refines root.interval :=
  RationalInterval.refines_trans
    (classification.branch.computeEventSigns classification.parent).refines
    classification.refines

end CCLCountOneClassification
end FTA
