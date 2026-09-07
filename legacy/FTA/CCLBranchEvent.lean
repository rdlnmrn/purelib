import FTA.CCLBranchPartition
import FTA.CCLCountOneClassification
import FTA.CCLIntersectionEventDecision
import FTA.RootCountDivisibility
import FTA.SturmIsolation

/-!
# Classification of guarded CCL branch events

Every first-member event produced by the combined branch guard must be
interpreted without completing its algebraic parameter.  Executable gcd
splitting classifies the event factor against, in order, the curve common
factor, the projective denominator norm, and the four closed box conditions.
The first two equality bits distinguish genuine curve roots from poles; the
remaining relations compute exact box membership on the same refined
count-one event interval.
-/

namespace FTA
namespace CCLBranchEvent

open CCL
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.CCLPathIntersection
open FTA.CCLIntersectionGuard
open FTA.CCLCountOneClassification
open FTA.CCLIntersectionEventSigns
open FTA.CCLIntersectionSharedFactors
open FTA.CCLIntersectionEventDecision
open FTA.CCLIntersectionPartition
open FTA.CCLBranchPartition
open FTA.SquarefreeFactorization
open FTA.SturmTransducer
open FTA.SturmIsolation
open FTA.RootCountDivisibility

abbrev GaussianPolynomial := DensePolynomial CCL.GaussianRat
abbrev RatPolynomial := DensePolynomial ℚ
abbrev BranchInterval := FTA.SturmTransducer.RationalInterval

/-! ## Dropping already interpreted condition relations -/

/-- Tail of a relation list, retaining alignment with the condition tail. -/
def relationsTail
    {p q : RatPolynomial} {conditions : List RatPolynomial} :
    ConditionRelations p (q :: conditions) → ConditionRelations p conditions
  | .cons _ tail => tail

/-- First equality-or-coprime relation in an aligned relation list. -/
def relationsHead
    {p q : RatPolynomial} {conditions : List RatPolynomial} :
    ConditionRelations p (q :: conditions) → ConditionRelation p q
  | .cons head _ => head

/-- Whether the first condition vanishes identically on this classified
event branch. -/
def relationsHeadIsEquality
    {p q : RatPolynomial} {conditions : List RatPolynomial} :
    ConditionRelations p (q :: conditions) → Bool
  | .cons head _ => head.isEquality

/-- An equality bit at the head of an aligned relation list exposes the
stored sparse-polynomial divisibility certificate. -/
theorem ConditionRelations.headDivides
    {p q : RatPolynomial} {conditions : List RatPolynomial} :
    (relations : ConditionRelations p (q :: conditions)) →
      relationsHeadIsEquality relations = true →
        p.toPolynomial ∣ q.toPolynomial
  | .cons (.equality divides) _, _ => divides
  | .cons (.coprime _) _, equality => by
      simp [relationsHeadIsEquality, ConditionRelation.isEquality] at equality

/-- A non-equality label at the first condition exposes the stored coprime
certificate with its original polynomial label. -/
def ConditionRelations.headCoprimeCondition
    {p q : RatPolynomial} {conditions : List RatPolynomial} :
    (relations : ConditionRelations p (q :: conditions)) →
      relationsHeadIsEquality relations = false → CoprimeCondition p
  | .cons (.equality _) _, nonEquality => by
      simp [relationsHeadIsEquality, ConditionRelation.isEquality]
        at nonEquality
  | .cons (.coprime certificate) _, _ =>
      { polynomial := q, coprime := certificate }

@[simp] theorem ConditionRelations.headCoprimeCondition_polynomial
    {p q : RatPolynomial} {conditions : List RatPolynomial}
    (relations : ConditionRelations p (q :: conditions))
    (nonEquality : relationsHeadIsEquality relations = false) :
    (FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition
      relations nonEquality).polynomial = q := by
  cases relations with
  | cons relation tail =>
      cases relation <;>
        simp [FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition,
          relationsHeadIsEquality, ConditionRelation.isEquality]
          at nonEquality ⊢

theorem ConditionRelations.headCoprimeCondition_mem
    {p q : RatPolynomial} {conditions : List RatPolynomial}
    (relations : ConditionRelations p (q :: conditions))
    (nonEquality : relationsHeadIsEquality relations = false) :
    FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition
        relations nonEquality ∈ relations.coprimeConditions := by
  cases relations with
  | cons relation tail =>
      cases relation <;>
        simp [FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition,
          ConditionRelations.coprimeConditions, relationsHeadIsEquality,
          ConditionRelation.isEquality] at nonEquality ⊢

/-- When the second aligned relation is non-equality, recover its explicit
coprime condition with the original polynomial label. -/
def ConditionRelations.secondCoprimeCondition
    {p first second : RatPolynomial} {conditions : List RatPolynomial} :
    (relations : ConditionRelations p (first :: second :: conditions)) →
      (relationsHead (relationsTail relations)).isEquality = false →
        CoprimeCondition p
  | .cons _ (.cons (.equality _) _), nonEquality => by
      simp [relationsHead, relationsTail, ConditionRelation.isEquality]
        at nonEquality
  | .cons _ (.cons (.coprime certificate) _), _ =>
      { polynomial := second, coprime := certificate }

@[simp] theorem ConditionRelations.secondCoprimeCondition_polynomial
    {p first second : RatPolynomial} {conditions : List RatPolynomial}
    (relations : ConditionRelations p (first :: second :: conditions))
    (nonEquality :
      (relationsHead (relationsTail relations)).isEquality = false) :
    (FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition
      relations nonEquality).polynomial = second := by
  cases relations with
  | cons firstRelation tail =>
      cases tail with
      | cons secondRelation rest =>
          cases secondRelation <;>
            simp [FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition,
              relationsHead, relationsTail, ConditionRelation.isEquality]
              at nonEquality ⊢

theorem ConditionRelations.secondCoprimeCondition_mem
    {p first second : RatPolynomial} {conditions : List RatPolynomial}
    (relations : ConditionRelations p (first :: second :: conditions))
    (nonEquality :
      (relationsHead (relationsTail relations)).isEquality = false) :
    FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition
        relations nonEquality ∈
      relations.coprimeConditions := by
  cases relations with
  | cons firstRelation tail =>
      cases firstRelation <;> cases tail with
      | cons secondRelation rest =>
          cases secondRelation <;>
            simp [FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition,
              ConditionRelations.coprimeConditions, relationsHead,
              relationsTail, ConditionRelation.isEquality] at nonEquality ⊢

@[simp] theorem relationsHeadIsEquality_eq
    {p q : RatPolynomial} {conditions : List RatPolynomial}
    (relations : ConditionRelations p (q :: conditions)) :
    relationsHeadIsEquality relations = (relationsHead relations).isEquality := by
  cases relations
  rfl

/-- Remove the first original condition from a common event-sign result.
An equality relation consumes no coprime sign; a coprime relation consumes
exactly the corresponding head sign certificate. -/
def dropRelationHeadSigns
    {p q : RatPolynomial} {conditions : List RatPolynomial}
    (input : SquarefreeInput p) (parent : CountOneInterval p) :
    (relations : ConditionRelations p (q :: conditions)) →
      CommonEventSigns input relations.coprimeConditions parent →
        CommonEventSigns input (relationsTail relations).coprimeConditions parent
  | .cons (.equality _) _tail, result => result
  | .cons (.coprime _) _tail, result => CommonEventSigns.dropHead result

@[simp] theorem dropRelationHeadSigns_refined
    {p q : RatPolynomial} {conditions : List RatPolynomial}
    (input : SquarefreeInput p) (parent : CountOneInterval p)
    (relations : ConditionRelations p (q :: conditions))
    (result : CommonEventSigns input relations.coprimeConditions parent) :
    (dropRelationHeadSigns input parent relations result).refined =
      result.refined := by
  cases relations with
  | cons relation tail => cases relation <;> rfl

/-! ## Six-condition event branches -/

/-- Refine a squarefree factor of the combined guard into branches carrying
an equality-or-coprime relation to every original arc polynomial. -/
def arcEventBranches
    (factor : Factor) (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    List (ClassifiedEventFactor (arcPolynomials p path box)) :=
  classifyEventConditions factor.input (arcPolynomials p path box)

theorem arcEventBranches_nonempty
    (factor : Factor) (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    arcEventBranches factor p path box ≠ [] :=
  classifyEventConditions_nonempty factor.input (arcPolynomials p path box)

theorem arcEventBranches_cover
    (factor : Factor) (p : GaussianPolynomial) (path : Path) (box : RatBox)
    {t : ℚ} (eventZero : factor.polynomial.eval t = 0) :
    ∃ branch ∈ arcEventBranches factor p path box,
      branch.factor.polynomial.eval t = 0 :=
  classifyEventConditions_covers factor.input (arcPolynomials p path box)
    eventZero

/-- A guarded terminal event cell feeds directly into the exhaustive
six-condition algebraic classifier, preserving a count-one descendant of the
positive squarefree factor without choosing a real root. -/
theorem EventGuardCell.exists_arcEventClassification
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    ∃ factor ∈ decomposition.factors,
      ∃ root : CountOneInterval factor.polynomial,
        root.interval = cell.cell.interval ∧
        ∃ classification : CountOneClassification
            (arcPolynomials p path box) factor root,
          classification.branch ∈ arcEventBranches factor p path box := by
  rcases cell.exists_countOneInterval with
    ⟨factor, factorMember, root, rootInterval⟩
  let classification := followCountOneConditions factor root
    (arcPolynomials p path box)
  exact ⟨factor, factorMember, root, rootInterval, classification, by
    simpa only [arcEventBranches] using classification.member⟩

theorem arcEventBranch_dvd
    (factor : Factor) (p : GaussianPolynomial) (path : Path) (box : RatBox)
    {branch : ClassifiedEventFactor (arcPolynomials p path box)}
    (member : branch ∈ arcEventBranches factor p path box) :
    branch.factor.polynomial.toPolynomial ∣ factor.polynomial.toPolynomial :=
  classifyEventConditions_dvd factor.input member

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

/-- Re-isolate one fully classified divisor branch on the common guarded
root.  The common derivative guard makes the parent factor endpoints clear;
divisibility transfers that clearance to every classified child branch. -/
def isolateArcEventBranch
    {factors : List Factor} {core : BranchInterval}
    (root : GuardedRoot factors core) {factor : Factor}
    (factorMember : factor ∈ factors)
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (branchMember : branch ∈ arcEventBranches factor p path box) :
    IsolationResult branch.factor.polynomial root.interval := by
  have factorLower : factor.polynomial.eval root.interval.lower ≠ 0 :=
    factor_eval_ne_zero_of_eventGuard factorMember root.lowerClear
  have factorUpper : factor.polynomial.eval root.interval.upper ≠ 0 :=
    factor_eval_ne_zero_of_eventGuard factorMember root.upperClear
  have branchDivides := arcEventBranch_dvd factor p path box branchMember
  exact isolate branch.factor.input root.interval.lower root.interval.upper
    root.proper
    (eval_ne_zero_of_toPolynomial_dvd branchDivides factorLower)
    (eval_ne_zero_of_toPolynomial_dvd branchDivides factorUpper)

/-- The curve-common-factor relation is the first relation in the combined
arc condition list. -/
def curveIsEquality
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box)) : Bool := by
  exact relationsHeadIsEquality branch.relations

/-- Explicit common-factor coprime condition carried by a classified event
that is not a curve-root branch. -/
def curveCoprimeCondition
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : curveIsEquality branch = false) :
    CoprimeCondition branch.factor.polynomial :=
  FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition
    branch.relations (by simpa [curveIsEquality] using nonEquality)

theorem curveCoprimeCondition_mem
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : curveIsEquality branch = false) :
    curveCoprimeCondition branch nonEquality ∈
      branch.coprimeConditions := by
  exact FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition_mem
    branch.relations (by simpa [curveIsEquality] using nonEquality)

@[simp] theorem curveCoprimeCondition_polynomial
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : curveIsEquality branch = false) :
    (curveCoprimeCondition branch nonEquality).polynomial =
      PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path) := by
  exact FTA.CCLBranchEvent.ConditionRelations.headCoprimeCondition_polynomial
    branch.relations
      (by simpa [curveIsEquality] using nonEquality)

/-- A non-curve classified event supplies a quantitative positive lower
bound for the curve common factor throughout the classifier's shared rational
interval. -/
def curveNonEqualityCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    (nonEquality : curveIsEquality branch = false) :
    PositiveLowerBound.Certificate
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path))
      (branch.computeEventSigns parent).refined.interval := by
  let condition := curveCoprimeCondition branch nonEquality
  let signs := branch.computeEventSigns parent
  have sign := signs.signs condition
    (curveCoprimeCondition_mem branch nonEquality)
  have commonSign : RationalPolynomialBounds.IntervalSignCertificate
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path))
      signs.refined.interval.lower signs.refined.interval.upper := by
    simpa [condition] using sign
  exact PositiveLowerBound.Certificate.ofIntervalSign commonSign

/-- The common-factor certificate combines with the reduced-pair Bézout
identity to clear both rational coordinates on the same shared interval. -/
def curveNonEqualityClearedCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (nonEquality : curveIsEquality branch = false) :
    PathClearance.Certificate (clearedReal p path) (clearedImag p path)
      (branch.computeEventSigns parent).refined.interval :=
  PathClearance.certificateOfCommonFactor clearedNonzero
    (branch.computeEventSigns parent).refined.interval
      (curveNonEqualityCertificate branch parent nonEquality)

/-- Consequently every affine point in a non-curve event neighborhood has a
strict quantitative polynomial residual bound. -/
def curveNonEqualityAffineCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (nonEquality : curveIsEquality branch = false) :
    ProjectivePathBounds.AffineCertificate p path
      (branch.computeEventSigns parent).refined.interval :=
  ProjectivePathBounds.affineCertificateOfCleared p path
    (branch.computeEventSigns parent).refined.interval
      (curveNonEqualityClearedCertificate branch parent clearedNonzero
        nonEquality)

/-- The equality branch produced by gcd classification is an actual
squarefree divisor of the curve common factor. -/
theorem curveFactor_toPolynomial_dvd
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (curveEquality : curveIsEquality branch = true) :
    branch.factor.polynomial.toPolynomial ∣
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).toPolynomial := by
  exact FTA.CCLBranchEvent.ConditionRelations.headDivides
    branch.relations (by simpa [curveIsEquality] using curveEquality)

/-- The projective-denominator relation is the second relation. -/
def denominatorIsEquality
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box)) : Bool := by
  exact relationsHeadIsEquality (relationsTail branch.relations)

/-- A pole-labelled branch is an exact squarefree divisor of the path
denominator-norm polynomial. -/
theorem denominatorFactor_toPolynomial_dvd
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (denominatorEquality : denominatorIsEquality branch = true) :
    branch.factor.polynomial.toPolynomial ∣
      (denominatorNorm path).toPolynomial := by
  exact FTA.CCLBranchEvent.ConditionRelations.headDivides
    (relationsTail branch.relations)
      (by simpa [denominatorIsEquality] using denominatorEquality)

/-- The explicit coprime denominator-norm condition carried by a non-pole
classified event branch. -/
def denominatorCoprimeCondition
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : denominatorIsEquality branch = false) :
    CoprimeCondition branch.factor.polynomial := by
  let relations : ConditionRelations branch.factor.polynomial
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path) ::
        denominatorNorm path :: conditionPolynomials (boxConditions path box)) :=
    by simpa only [arcPolynomials] using branch.relations
  have secondNonEquality :
      (relationsHead (relationsTail relations)).isEquality = false := by
    simpa [relations, denominatorIsEquality, relationsHeadIsEquality_eq]
      using nonEquality
  exact FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition
    relations secondNonEquality

theorem denominatorCoprimeCondition_mem
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : denominatorIsEquality branch = false) :
    denominatorCoprimeCondition branch nonEquality ∈
      branch.coprimeConditions := by
  let relations : ConditionRelations branch.factor.polynomial
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path) ::
        denominatorNorm path :: conditionPolynomials (boxConditions path box)) :=
    by simpa only [arcPolynomials] using branch.relations
  have secondNonEquality :
      (relationsHead (relationsTail relations)).isEquality = false := by
    simpa [relations, denominatorIsEquality, relationsHeadIsEquality_eq]
      using nonEquality
  have member := FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition_mem
    relations secondNonEquality
  simpa [denominatorCoprimeCondition, relations,
    ClassifiedEventFactor.coprimeConditions, arcPolynomials] using member

@[simp] theorem denominatorCoprimeCondition_polynomial
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (nonEquality : denominatorIsEquality branch = false) :
    (denominatorCoprimeCondition branch nonEquality).polynomial =
      denominatorNorm path := by
  let relations : ConditionRelations branch.factor.polynomial
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path) ::
        denominatorNorm path :: conditionPolynomials (boxConditions path box)) :=
    by simpa only [arcPolynomials] using branch.relations
  have secondNonEquality :
      (relationsHead (relationsTail relations)).isEquality = false := by
    simpa [relations, denominatorIsEquality, relationsHeadIsEquality_eq]
      using nonEquality
  change (FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition
      relations secondNonEquality).polynomial = denominatorNorm path
  exact FTA.CCLBranchEvent.ConditionRelations.secondCoprimeCondition_polynomial
    relations secondNonEquality

/-- Relations to the four box conditions after the curve and denominator
relations have been interpreted. -/
def boxRelations
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box)) :
    ConditionRelations branch.factor.polynomial
      (conditionPolynomials (boxConditions path box)) := by
  simpa only [arcPolynomials] using
    relationsTail (relationsTail branch.relations)

theorem curve_eval_eq_zero_of_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (curveEquality : curveIsEquality branch = true) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval t = 0 := by
  exact (relationsHead branch.relations).eval_eq_zero_of_isEquality eventZero
    (by simpa [curveIsEquality] using curveEquality)

theorem curve_eval_ne_zero_of_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (curveNonEquality : curveIsEquality branch = false) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval t ≠ 0 := by
  exact (relationsHead branch.relations).eval_ne_zero_of_isEquality_false eventZero
    (by simpa [curveIsEquality] using curveNonEquality)

theorem denominator_eval_eq_zero_of_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (denominatorEquality : denominatorIsEquality branch = true) :
    (denominatorNorm path).eval t = 0 := by
  exact (relationsHead (relationsTail branch.relations)).eval_eq_zero_of_isEquality eventZero
    (by simpa [denominatorIsEquality] using denominatorEquality)

theorem denominator_eval_ne_zero_of_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (denominatorNonEquality : denominatorIsEquality branch = false) :
    (denominatorNorm path).eval t ≠ 0 := by
  exact (relationsHead
    (relationsTail branch.relations)).eval_ne_zero_of_isEquality_false eventZero
    (by simpa [denominatorIsEquality] using denominatorNonEquality)

/-- A non-pole classified event has a genuinely nonzero projective path
denominator, not merely a nonzero cleared norm polynomial. -/
theorem path_denominator_ne_of_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (denominatorNonEquality : denominatorIsEquality branch = false) :
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  have normNonzero := denominator_eval_ne_zero_of_event branch eventZero
    denominatorNonEquality
  intro zero
  apply normNonzero
  rw [eval_denominatorNorm, zero]
  simp [CCL.GaussianRat.normSq]

/-- A curve-equality event away from a projective pole is an actual zero of
the Gaussian polynomial on the affine branch path. -/
theorem polynomial_eval_eq_zero_of_curve_event
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    {t : ℚ} (eventZero : branch.factor.polynomial.eval t = 0)
    (curveEquality : curveIsEquality branch = true)
    (denominatorNonEquality : denominatorIsEquality branch = false) :
    p.eval (path.value t) = 0 := by
  have pathDenominator := path_denominator_ne_of_event branch eventZero
    denominatorNonEquality
  have commonZero := curve_eval_eq_zero_of_event branch eventZero curveEquality
  have realZero : (clearedReal p path).eval t = 0 := by
    rw [PathClearance.commonFactor_mul_reducedReal_eval, commonZero, zero_mul]
  have imagZero : (clearedImag p path).eval t = 0 := by
    rw [PathClearance.commonFactor_mul_reducedImag_eval, commonZero, zero_mul]
  have productZero :
      (clearedDenominatorPower p path).eval (PathPolynomial.ofRat t) *
        p.eval (path.value t) = 0 := by
    apply GaussianRat.ext
    · rw [← eval_clearedReal p path t pathDenominator, realZero]
      rfl
    · rw [← eval_clearedImag p path t pathDenominator, imagZero]
      rfl
  exact (mul_eq_zero.mp productZero).resolve_left
    (clearedDenominatorPower_eval_ne p path t pathDenominator)

/-! ## Closed box decision on an event branch -/

/-- Drop the curve and denominator sign entries from the shared event-sign
result, leaving exactly those aligned with `boxRelations`. -/
def boxEventSigns
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial) :
    CommonEventSigns branch.factor.input (boxRelations branch).coprimeConditions
      parent := by
  let allSigns := branch.computeEventSigns parent
  let afterCurve := dropRelationHeadSigns branch.factor.input parent
    branch.relations allSigns
  exact dropRelationHeadSigns branch.factor.input parent
    (relationsTail branch.relations) afterCurve

theorem boxEventSigns_refined
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial) :
    (boxEventSigns branch parent).refined =
      (branch.computeEventSigns parent).refined := by
  simp [boxEventSigns]

/-- Executable closed-box membership bit for one classified guarded event. -/
def boxEventCheck
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial) : Bool :=
  ConditionRelations.closedCheck branch.factor.input parent
    (boxRelations branch) (boxEventSigns branch parent)

/-- The event bit agrees exactly with the four closed box conditions at every
rational event zero in the shared refined interval. -/
theorem boxEventCheck_eq_true_iff
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (boxEventSigns branch parent).refined.interval.lower ≤ t)
    (upper : t ≤ (boxEventSigns branch parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0) :
    boxEventCheck branch parent = true ↔
      (boxConditions path box).HoldsAt t := by
  rw [boxEventCheck]
  exact
    (ConditionRelations.closedCheck_eq_true_iff branch.factor.input parent
      (boxRelations branch) (boxEventSigns branch parent)
      lower upper eventZero).trans
        (conditionPolynomials_holdAt_iff (boxConditions path box) t)

/-- Away from a classified pole, the event bit is exactly affine membership
of the rational branch point in the root box. -/
theorem boxEventCheck_eq_contains
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    {t : ℚ}
    (lower : (boxEventSigns branch parent).refined.interval.lower ≤ t)
    (upper : t ≤ (boxEventSigns branch parent).refined.interval.upper)
    (eventZero : branch.factor.polynomial.eval t = 0)
    (denominatorNonEquality : denominatorIsEquality branch = false) :
    boxEventCheck branch parent = true ↔ box.Contains (path.value t) := by
  have pathDenominator := path_denominator_ne_of_event branch eventZero
    denominatorNonEquality
  exact (boxEventCheck_eq_true_iff branch parent lower upper eventZero).trans
    (contains_value_iff_holdsAt path box t pathDenominator).symm

/-- A failed box bit excludes every affine path point in the shared sign
interval.  This strengthens the event-root statement to the full rational
neighborhood needed by quantitative guard elimination. -/
theorem boxEventCheck_eq_false_excludes_contains
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (parent : CountOneInterval branch.factor.polynomial)
    (boxFalse : boxEventCheck branch parent = false)
    {t : ℚ}
    (lower : (boxEventSigns branch parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (boxEventSigns branch parent).refined.interval.upper)
    (denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    ¬box.Contains (path.value t) := by
  intro contains
  have holds := (contains_value_iff_holdsAt path box t
    denominatorNonzero).mp contains
  have listHolds : ConditionsHoldAt
      (conditionPolynomials (boxConditions path box)) t :=
    (conditionPolynomials_holdAt_iff (boxConditions path box) t).mpr holds
  have excluded := FTA.CCLIntersectionEventDecision.ConditionRelations.not_conditionsHoldAt_of_closedCheck_eq_false
    branch.factor.input parent
      (boxRelations branch) (boxEventSigns branch parent) (by
        simpa only [boxEventCheck] using boxFalse) lower upper
  exact excluded listHolds

/-! ## Executable extraction of relevant curve events -/

/-- A classified count-one event that is an actual curve-common-factor
branch, is not a projective pole, and satisfies all four closed box tests. -/
structure RelevantCurveEvent
    (p : GaussianPolynomial) (path : Path) (box : RatBox) where
  branch : ClassifiedEventFactor (arcPolynomials p path box)
  parent : CountOneInterval branch.factor.polynomial
  curveEquality : curveIsEquality branch = true
  denominatorNonEquality : denominatorIsEquality branch = false
  meetsBox : boxEventCheck branch parent = true

/-- One count-one factor of a terminal guard cell followed through the full
curve/denominator/box relation classifier. -/
structure GuardEventClassification
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) where
  entry : FactorCountOneInterval decomposition.factors
  classification : CountOneClassification (arcPolynomials p path box)
    entry.factor entry.root

/-- Classify every positive factor of a terminal guard cell without choosing
or completing any algebraic root. -/
def EventGuardCell.classifications
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    List (GuardEventClassification p path box cell) :=
  cell.eventIntervals.map fun entry =>
    { entry := entry
      classification := followCountOneConditions entry.factor entry.root
        (arcPolynomials p path box) }

theorem EventGuardCell.classifications_ne_nil
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    CCLBranchEvent.EventGuardCell.classifications cell ≠ [] := by
  simpa [EventGuardCell.classifications] using cell.eventIntervals_ne_nil

/-- Apply the same exact relevance test used by the global event extractor to
one cell-local count-one classification. -/
def GuardEventClassification.relevant?
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (item : GuardEventClassification p path box cell) :
    Option (RelevantCurveEvent p path box) :=
  let branch := item.classification.branch
  let parent := item.classification.parent
  if curveEquality : curveIsEquality branch = true then
    if denominatorNonEquality : denominatorIsEquality branch = false then
      if meetsBox : boxEventCheck branch parent = true then
        some
          { branch := branch
            parent := parent
            curveEquality := curveEquality
            denominatorNonEquality := denominatorNonEquality
            meetsBox := meetsBox }
      else none
    else none
  else none

/-- Exact reason why one classified guard root is not retained as a relevant
affine curve event.  The successful relevance case is represented by `none`:
this type is used only to retain proof-bearing failure certificates. -/
inductive GuardEventIrrelevanceReason
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (item : GuardEventClassification p path box cell) where
  | curveNonEquality
      (proof : curveIsEquality item.classification.branch = false)
  | pole
      (curveEquality : curveIsEquality item.classification.branch = true)
      (denominatorEquality :
        denominatorIsEquality item.classification.branch = true)
  | outsideBox
      (curveEquality : curveIsEquality item.classification.branch = true)
      (denominatorNonEquality :
        denominatorIsEquality item.classification.branch = false)
      (boxFalse : boxEventCheck item.classification.branch
        item.classification.parent = false)

/-- Compute an irrelevance reason, returning `none` exactly for a retained
relevant event. -/
def GuardEventClassification.irrelevanceReason?
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (item : GuardEventClassification p path box cell) :
    Option (GuardEventIrrelevanceReason item) := by
  if curveNonEquality :
      curveIsEquality item.classification.branch = false then
    exact some (.curveNonEquality curveNonEquality)
  else
    have curveEquality :
        curveIsEquality item.classification.branch = true :=
      Bool.eq_true_of_not_eq_false curveNonEquality
    if denominatorEquality :
        denominatorIsEquality item.classification.branch = true then
      exact some (.pole curveEquality denominatorEquality)
    else
      have denominatorNonEquality :
          denominatorIsEquality item.classification.branch = false :=
        Bool.eq_false_of_not_eq_true denominatorEquality
      if boxFalse : boxEventCheck item.classification.branch
          item.classification.parent = false then
        exact some (.outsideBox curveEquality denominatorNonEquality boxFalse)
      else
        exact none

theorem GuardEventClassification.irrelevanceReason?_isSome_iff
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (item : GuardEventClassification p path box cell) :
    item.irrelevanceReason?.isSome ↔ item.relevant? = Option.none := by
  by_cases curveNonEquality :
      curveIsEquality item.classification.branch = false
  · simp [GuardEventClassification.irrelevanceReason?,
      GuardEventClassification.relevant?, curveNonEquality]
  · have curveEquality :
        curveIsEquality item.classification.branch = true :=
      Bool.eq_true_of_not_eq_false curveNonEquality
    by_cases denominatorEquality :
        denominatorIsEquality item.classification.branch = true
    · simp [GuardEventClassification.irrelevanceReason?,
        GuardEventClassification.relevant?, curveNonEquality,
        denominatorEquality]
    · have denominatorNonEquality :
          denominatorIsEquality item.classification.branch = false :=
        Bool.eq_false_of_not_eq_true denominatorEquality
      by_cases boxFalse : boxEventCheck item.classification.branch
          item.classification.parent = false
      · simp [GuardEventClassification.irrelevanceReason?,
          GuardEventClassification.relevant?, curveNonEquality,
          denominatorEquality, boxFalse]
      · have boxTrue : boxEventCheck item.classification.branch
            item.classification.parent = true :=
          Bool.eq_true_of_not_eq_false boxFalse
        simp [GuardEventClassification.irrelevanceReason?,
          GuardEventClassification.relevant?, curveNonEquality,
          denominatorEquality, boxFalse]

/-- Pointwise semantic content of every irrelevance reason at an exact root
of the classified branch: the root is not a curve root, is a projective pole,
or maps outside the closed box. -/
theorem GuardEventIrrelevanceReason.at_event_root
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    {item : GuardEventClassification p path box cell}
    (reason : GuardEventIrrelevanceReason item)
    {t : ℚ}
    (lower : (boxEventSigns item.classification.branch
      item.classification.parent).refined.interval.lower ≤ t)
    (upper : t ≤ (boxEventSigns item.classification.branch
      item.classification.parent).refined.interval.upper)
    (eventZero : item.classification.branch.factor.polynomial.eval t = 0) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval t ≠ 0 ∨
      path.denominator.eval (PathPolynomial.ofRat t) = 0 ∨
      ¬box.Contains (path.value t) := by
  cases reason with
  | curveNonEquality curveNonEquality =>
      exact Or.inl (curve_eval_ne_zero_of_event
        item.classification.branch eventZero curveNonEquality)
  | pole curveEquality denominatorEquality =>
      right
      left
      have normZero := denominator_eval_eq_zero_of_event
        item.classification.branch eventZero denominatorEquality
      rw [eval_denominatorNorm] at normZero
      exact CCL.GaussianRat.normSq_eq_zero.mp normZero
  | outsideBox curveEquality denominatorNonEquality boxFalse =>
      right
      right
      intro contains
      have checkTrue := (boxEventCheck_eq_contains
        item.classification.branch item.classification.parent lower upper
          eventZero denominatorNonEquality).mpr contains
      rw [boxFalse] at checkTrue
      contradiction

/-- Relevant curve-root events extracted directly from every positive factor
of one guarded terminal cell. -/
def EventGuardCell.relevantCurveEvents
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    List (RelevantCurveEvent p path box) :=
  (CCLBranchEvent.EventGuardCell.classifications cell).filterMap fun item =>
    GuardEventClassification.relevant? item

/-- If a guard cell's relevance filter is empty, every one of its exhaustive
classified count-one branches carries a computable irrelevance reason. -/
theorem GuardEventClassification.irrelevanceReason?_isSome_of_cell_empty
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    (empty : CCLBranchEvent.EventGuardCell.relevantCurveEvents cell = [])
    {item : GuardEventClassification p path box cell}
    (itemMember : item ∈
      CCLBranchEvent.EventGuardCell.classifications cell) :
    item.irrelevanceReason?.isSome := by
  apply item.irrelevanceReason?_isSome_iff.mpr
  cases relevantEquation : item.relevant? with
  | none => rfl
  | some event =>
      have eventMember : event ∈
          CCLBranchEvent.EventGuardCell.relevantCurveEvents cell := by
        rw [CCLBranchEvent.EventGuardCell.relevantCurveEvents,
          List.mem_filterMap]
        exact ⟨item, itemMember, relevantEquation⟩
      rw [empty] at eventMember
      simp at eventMember

/-- A classified item retained from a terminal guard cell keeps its
count-one parent inside that exact cell interval. -/
theorem GuardEventClassification.parent_refines_cell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    {item : GuardEventClassification p path box cell}
    (member : item ∈
      CCLBranchEvent.EventGuardCell.classifications cell) :
    item.classification.parent.interval.Refines cell.cell.interval := by
  rw [CCLBranchEvent.EventGuardCell.classifications, List.mem_map] at member
  rcases member with ⟨entry, entryMember, equality⟩
  cases equality
  have rootInterval :=
    cell.cell.leaves.eventIntervals_root_interval entry entryMember
  exact RationalInterval.refines_trans
    (followCountOneConditions entry.factor entry.root
      (arcPolynomials p path box)).refines (by
      rw [rootInterval]
      exact RationalInterval.refines_refl cell.cell.interval)

/-- Cell-local relevance filtering preserves the same terminal-cell
containment. -/
theorem RelevantCurveEvent.parent_refines_of_mem_eventGuardCell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    {cell : EventGuardCell decomposition}
    {event : RelevantCurveEvent p path box}
    (member : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents cell) :
    event.parent.interval.Refines cell.cell.interval := by
  rw [CCLBranchEvent.EventGuardCell.relevantCurveEvents,
    List.mem_filterMap] at member
  rcases member with ⟨item, itemMember, equality⟩
  dsimp only [GuardEventClassification.relevant?] at equality
  split at equality <;> try contradiction
  split at equality <;> try contradiction
  split at equality <;> try contradiction
  simp only [Option.some.injEq] at equality
  cases equality
  exact item.parent_refines_cell itemMember

/-- A retained count-one curve event forces a positive whole-common-factor
count on every clear ambient interval containing it.  This is the executable
divisibility bridge from classified event ownership to the positive branch of
the curve decision. -/
theorem RelevantCurveEvent.commonFactorRootCount2_pos
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (event : RelevantCurveEvent p path box)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (ambient : BranchInterval) (ambientProper : ambient.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval ambient.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval ambient.upper ≠ 0)
    (refines : event.parent.interval.Refines ambient) :
    0 < ProjectivePath.commonFactorRootCount2 p path clearedNonzero
      ambient.lower ambient.upper := by
  simpa [ProjectivePath.commonFactorRootCount2,
    PathClearance.commonFactorRootCount2] using
      factorRootCount2_pos_of_dvd_countOne_refines event.branch.factor.input
        (PathClearance.commonFactor_isZero_false clearedNonzero)
        (curveFactor_toPolynomial_dvd event.branch event.curveEquality)
        ambient ambientProper lowerClear upperClear event.parent refines

/-- Exact finite filter on the isolated first-member events of one classified
branch. -/
def relevantCurveEventsForBranch
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (isolation : IsolationResult branch.factor.polynomial
      isolationRoot) : List (RelevantCurveEvent p path box) :=
  isolation.transducers.filterMap fun parent =>
    if curveEquality : curveIsEquality branch = true then
      if denominatorNonEquality : denominatorIsEquality branch = false then
        if meetsBox : boxEventCheck branch parent = true then
          some
            { branch := branch
              parent := parent
              curveEquality := curveEquality
              denominatorNonEquality := denominatorNonEquality
              meetsBox := meetsBox }
        else none
      else none
    else none

/-- The relevant-event filter retains every exact rational branch zero that is
simultaneously a curve-common-factor zero, avoids the projective denominator,
and satisfies the closed box conditions.  The returned interval is the exact
refined interval later used by parser-owner classification. -/
theorem relevantCurveEventsForBranch_covers
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (branch : ClassifiedEventFactor (arcPolynomials p path box))
    (isolation : IsolationResult branch.factor.polynomial isolationRoot)
    {t : ℚ} (lower : isolationRoot.lower ≤ t)
    (upper : t ≤ isolationRoot.upper)
    (eventZero : branch.factor.polynomial.eval t = 0)
    (commonZero :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval t = 0)
    (denominatorNonzero : (denominatorNorm path).eval t ≠ 0)
    (holds : (boxConditions path box).HoldsAt t) :
    ∃ event ∈ relevantCurveEventsForBranch p path box branch isolation,
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  rcases FTA.PositiveLowerBound.IsolationResult.rationalZero_mem
      branch.factor.input isolation
      lower upper eventZero with
    ⟨parent, parentMember, parentLower, parentUpper⟩
  let signs := boxEventSigns branch parent
  have inside :=
    FTA.PositiveLowerBound.CountOneInterval.rationalZero_mem_of_refines
    branch.factor.input parent signs.refined signs.refines
    parentLower parentUpper eventZero
  have curveEquality : curveIsEquality branch = true := by
    cases equality : curveIsEquality branch with
    | false =>
        exact (curve_eval_ne_zero_of_event branch eventZero equality
          commonZero).elim
    | true => rfl
  have denominatorNonEquality : denominatorIsEquality branch = false := by
    cases equality : denominatorIsEquality branch with
    | false => rfl
    | true =>
        exact (denominatorNonzero
          (denominator_eval_eq_zero_of_event branch eventZero equality)).elim
  have meetsBox : boxEventCheck branch parent = true :=
    (boxEventCheck_eq_true_iff branch parent
      (by simpa only [signs] using inside.1)
      (by simpa only [signs] using inside.2) eventZero).mpr holds
  let event : RelevantCurveEvent p path box :=
    { branch := branch
      parent := parent
      curveEquality := curveEquality
      denominatorNonEquality := denominatorNonEquality
      meetsBox := meetsBox }
  refine ⟨event, ?_, ?_, ?_, ?_⟩
  · rw [relevantCurveEventsForBranch, List.mem_filterMap]
    refine ⟨parent, parentMember, ?_⟩
    simp [curveEquality, denominatorNonEquality, meetsBox, event]
  · simpa only [event, signs] using inside.1
  · simpa only [event, signs] using inside.2
  · exact eventZero

/-- Filtering a classified isolation branch retains the exact count-one
parent from that isolation result. -/
theorem RelevantCurveEvent.parent_refines_of_mem_forBranch
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {branch : ClassifiedEventFactor (arcPolynomials p path box)}
    {isolation : IsolationResult branch.factor.polynomial isolationRoot}
    {event : RelevantCurveEvent p path box}
    (member : event ∈
      relevantCurveEventsForBranch p path box branch isolation) :
    event.parent.interval.Refines isolationRoot := by
  rw [relevantCurveEventsForBranch, List.mem_filterMap] at member
  rcases member with ⟨parent, parentMember, equality⟩
  split at equality
  · split at equality
    · split at equality
      · simp only [Option.some.injEq] at equality
        cases equality
        exact isolation.refine parent parentMember
      · contradiction
    · contradiction
  · contradiction

/-- Run classified gcd branching, exact Sturm isolation, and the relevant
event filter for one squarefree factor of the combined arc guard. -/
def relevantCurveEventsForFactor
    {factors : List Factor} {core : BranchInterval}
    (root : GuardedRoot factors core) (factor : Factor)
    (factorMember : factor ∈ factors)
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    List (RelevantCurveEvent p path box) :=
  (arcEventBranches factor p path box).attach.flatMap fun classified =>
    relevantCurveEventsForBranch p path box classified.1
      (isolateArcEventBranch root factorMember p path box classified.1
        classified.2)

/-- Classified branching and re-isolation retain every exact rational zero of
one squarefree guard factor that has the semantic curve/non-pole/box data. -/
theorem relevantCurveEventsForFactor_covers
    {factors : List Factor} {core : BranchInterval}
    (root : GuardedRoot factors core) (factor : Factor)
    (factorMember : factor ∈ factors)
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper)
    (factorZero : factor.polynomial.eval t = 0)
    (commonZero :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval t = 0)
    (denominatorNonzero : (denominatorNorm path).eval t ≠ 0)
    (holds : (boxConditions path box).HoldsAt t) :
    ∃ event ∈ relevantCurveEventsForFactor root factor factorMember
        p path box,
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  rcases arcEventBranches_cover factor p path box factorZero with
    ⟨branch, branchMember, branchZero⟩
  let classified : { candidate // candidate ∈
      arcEventBranches factor p path box } := ⟨branch, branchMember⟩
  let isolation := isolateArcEventBranch root factorMember p path box
    classified.1 classified.2
  rcases relevantCurveEventsForBranch_covers p path box classified.1
      isolation lower upper branchZero commonZero denominatorNonzero holds with
    ⟨event, eventMember, eventLower, eventUpper, eventZero⟩
  refine ⟨event, ?_, eventLower, eventUpper, eventZero⟩
  rw [relevantCurveEventsForFactor, List.mem_flatMap]
  exact ⟨classified, by simp [classified], eventMember⟩

theorem RelevantCurveEvent.parent_refines_of_mem_forFactor
    {factors : List Factor} {core : BranchInterval}
    {root : GuardedRoot factors core} {factor : Factor}
    {factorMember : factor ∈ factors}
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {event : RelevantCurveEvent p path box}
    (member : event ∈ relevantCurveEventsForFactor root factor factorMember
      p path box) :
    event.parent.interval.Refines root.interval := by
  rw [relevantCurveEventsForFactor, List.mem_flatMap] at member
  rcases member with ⟨classified, _classifiedMember, eventMember⟩
  exact event.parent_refines_of_mem_forBranch eventMember

/-- Aggregate the classified relevant events over every squarefree factor of
one combined arc guard. -/
def relevantCurveEventsForFactors
    {core : BranchInterval} {factors : List Factor}
    (root : GuardedRoot factors core)
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    List (RelevantCurveEvent p path box) :=
  factors.attach.flatMap fun factor =>
    relevantCurveEventsForFactor root factor.1 factor.2 p path box

/-- Aggregating over the squarefree factor list preserves the same rational
event coverage. -/
theorem relevantCurveEventsForFactors_covers
    {core : BranchInterval} {factors : List Factor}
    (root : GuardedRoot factors core)
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper)
    (productZero : (factorProduct factors).eval t = 0)
    (commonZero :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval t = 0)
    (denominatorNonzero : (denominatorNorm path).eval t ≠ 0)
    (holds : (boxConditions path box).HoldsAt t) :
    ∃ event ∈ relevantCurveEventsForFactors root p path box,
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  rcases exists_factor_eval_eq_zero_of_factorProduct_eval_eq_zero productZero with
    ⟨factor, factorMember, factorZero⟩
  rcases relevantCurveEventsForFactor_covers root factor factorMember p path box
      lower upper factorZero commonZero denominatorNonzero holds with
    ⟨event, eventMember, eventLower, eventUpper, eventZero⟩
  let item : { candidate // candidate ∈ factors } := ⟨factor, factorMember⟩
  refine ⟨event, ?_, eventLower, eventUpper, eventZero⟩
  rw [relevantCurveEventsForFactors, List.mem_flatMap]
  exact ⟨item, by simp [item], eventMember⟩

theorem RelevantCurveEvent.parent_refines_of_mem_forFactors
    {core : BranchInterval} {factors : List Factor}
    {root : GuardedRoot factors core}
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {event : RelevantCurveEvent p path box}
    (member : event ∈ relevantCurveEventsForFactors root p path box) :
    event.parent.interval.Refines root.interval := by
  rw [relevantCurveEventsForFactors, List.mem_flatMap] at member
  rcases member with ⟨factor, _factorMember, eventMember⟩
  exact event.parent_refines_of_mem_forFactor eventMember

/-- Total relevant-event extraction from the endpoint-safe partition plan.
A constant nonzero guard has no events; a factored guard isolates and filters
every classified factor branch. -/
def relevantCurveEventsOfPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval} :
    ArcPartitionPlan p path box core →
      List (RelevantCurveEvent p path box)
  | .constant _ => []
  | .factored _decomposition root _partition =>
      relevantCurveEventsForFactors root p path box

/-- A semantic rational curve event in a factored guarded plan is retained by
the plan-level finite event family, together with the final sign-refined
interval needed by parser-owner re-isolation. -/
theorem relevantCurveEventsOfPlan_covers
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    (decomposition : Decomposition (arcGuard p path box))
    (root : GuardedRoot decomposition.factors core)
    (partition : CommonFactorPartition decomposition.factors root.interval)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper)
    (guardZero : (arcGuard p path box).eval t = 0)
    (commonZero :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval t = 0)
    (denominatorNonzero : (denominatorNorm path).eval t ≠ 0)
    (holds : (boxConditions path box).HoldsAt t) :
    ∃ event ∈ relevantCurveEventsOfPlan
        (.factored decomposition root partition),
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  have productZero : (factorProduct decomposition.factors).eval t = 0 := by
    rw [decomposition.eval_identity] at guardZero
    exact (mul_eq_zero.mp guardZero).resolve_left decomposition.scalar_ne_zero
  simpa only [relevantCurveEventsOfPlan] using
    relevantCurveEventsForFactors_covers root p path box lower upper productZero
      commonZero denominatorNonzero holds

/-- Specialization of plan coverage to an actual affine curve root on the
bounded chart.  Cleared-coordinate vanishing, common-factor vanishing, the
guard event, and the non-pole box conditions are all discharged internally. -/
theorem relevantCurveEventsOfPlan_covers_root
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    (decomposition : Decomposition (arcGuard p path box))
    (root : GuardedRoot decomposition.factors core)
    (partition : CommonFactorPartition decomposition.factors root.interval)
    {t : ℚ} (lower : core.lower ≤ t) (upper : t ≤ core.upper)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (path.value t) = 0)
    (contains : box.Contains (path.value t)) :
    ∃ event ∈ relevantCurveEventsOfPlan
        (.factored decomposition root partition),
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  have realZero : (clearedReal p path).eval t = 0 :=
    eval_clearedReal_eq_zero_of_eval_eq_zero p path t pathDenominator
      polynomialZero
  have imagZero : (clearedImag p path).eval t = 0 :=
    eval_clearedImag_eq_zero_of_eval_eq_zero p path t pathDenominator
      polynomialZero
  have commonZero :
      (PathClearance.commonFactor (clearedReal p path)
        (clearedImag p path)).eval t = 0 :=
    PathClearance.commonFactor_eval_eq_zero_of_eval_eq_zero clearedNonzero
      realZero imagZero
  have guardZero : (arcGuard p path box).eval t = 0 := by
    by_contra guardNonzero
    exact (eval_ne_zero_of_mem_arcPolynomials
      (commonFactor_mem_arcPolynomials p path box)
      (PathClearance.commonFactor_isZero_false clearedNonzero)
      guardNonzero) commonZero
  have denominatorNonzero : (denominatorNorm path).eval t ≠ 0 :=
    (eval_denominatorNorm_pos path t pathDenominator).ne'
  have holds : (boxConditions path box).HoldsAt t :=
    (contains_value_iff_holdsAt path box t pathDenominator).mp contains
  exact relevantCurveEventsOfPlan_covers decomposition root partition
    (root.coreRefines.1.trans lower) (upper.trans root.coreRefines.2)
    guardZero commonZero denominatorNonzero holds

/-- The same affine-root coverage for an arbitrary total guarded plan.  The
nonzero-constant case is impossible because its direct lower-bound certificate
excludes the guard zero forced by the curve root. -/
theorem relevantCurveEventsOfPlan_covers_root_nonzero
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    (plan : ArcPartitionPlan p path box core)
    {t : ℚ} (lower : core.lower ≤ t) (upper : t ≤ core.upper)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (pathDenominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (path.value t) = 0)
    (contains : box.Contains (path.value t)) :
    ∃ event ∈ relevantCurveEventsOfPlan plan,
      (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns event.branch event.parent).refined.interval.upper ∧
      event.branch.factor.polynomial.eval t = 0 := by
  cases plan with
  | constant degreeZero =>
      have realZero : (clearedReal p path).eval t = 0 :=
        eval_clearedReal_eq_zero_of_eval_eq_zero p path t pathDenominator
          polynomialZero
      have imagZero : (clearedImag p path).eval t = 0 :=
        eval_clearedImag_eq_zero_of_eval_eq_zero p path t pathDenominator
          polynomialZero
      have commonZero :
          (PathClearance.commonFactor (clearedReal p path)
            (clearedImag p path)).eval t = 0 :=
        PathClearance.commonFactor_eval_eq_zero_of_eval_eq_zero clearedNonzero
          realZero imagZero
      have guardZero : (arcGuard p path box).eval t = 0 := by
        by_contra guardNonzero
        exact (eval_ne_zero_of_mem_arcPolynomials
          (commonFactor_mem_arcPolynomials p path box)
          (PathClearance.commonFactor_isZero_false clearedNonzero)
          guardNonzero) commonZero
      exact ((PositiveLowerBound.Certificate.ofConstant
        (arcGuard_isZero_false p path box) degreeZero core).eval_ne_zero
          lower upper guardZero).elim
  | factored decomposition root partition =>
      exact relevantCurveEventsOfPlan_covers_root decomposition root partition
        lower upper clearedNonzero pathDenominator polynomialZero contains

theorem RelevantCurveEvent.parent_refines_of_mem_factoredPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    {root : GuardedRoot decomposition.factors core}
    {partition : CommonFactorPartition decomposition.factors root.interval}
    {event : RelevantCurveEvent p path box}
    (member : event ∈ relevantCurveEventsOfPlan
      (.factored decomposition root partition)) :
    event.parent.interval.Refines root.interval :=
  event.parent_refines_of_mem_forFactors member

/-- Every non-identically-zero relevant event extracted from a factored
guarded plan yields a positive common-factor root count on that plan's clear
outer interval. -/
theorem RelevantCurveEvent.commonFactorRootCount2_pos_of_mem_factoredPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    {root : GuardedRoot decomposition.factors core}
    {partition : CommonFactorPartition decomposition.factors root.interval}
    {event : RelevantCurveEvent p path box}
    (member : event ∈ relevantCurveEventsOfPlan
      (.factored decomposition root partition))
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    0 < ProjectivePath.commonFactorRootCount2 p path clearedNonzero
      root.interval.lower root.interval.upper :=
  event.commonFactorRootCount2_pos clearedNonzero root.interval root.proper
    (root.commonFactor_lowerClear clearedNonzero)
    (root.commonFactor_upperClear clearedNonzero)
    (event.parent_refines_of_mem_factoredPlan member)

/-- Complete positive-count data recovered from one retained curve event.
The event's count-one interval is nested in the displayed clear ambient cell. -/
structure PositiveCurveEventEvidence
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (event : RelevantCurveEvent p path box) where
  clearedNonzero : (clearedReal p path).isZero = false ∨
    (clearedImag p path).isZero = false
  interval : BranchInterval
  proper : interval.Proper
  lowerClear :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval interval.lower ≠ 0
  upperClear :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval interval.upper ≠ 0
  eventRefines : event.parent.interval.Refines interval
  positive : 0 < ProjectivePath.commonFactorRootCount2 p path
    clearedNonzero interval.lower interval.upper

/-- A relevant algebraic event either exposes an identically-zero cleared
path or supplies a proof-bearing positive curve count on its guarded plan. -/
inductive CurveEventCountDecision
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (event : RelevantCurveEvent p path box) where
  | identicallyZero
      (realZero : (clearedReal p path).isZero = true)
      (imagZero : (clearedImag p path).isZero = true)
  | positive (evidence : PositiveCurveEventEvidence p path box event)

/-- Execute the same coordinate dichotomy for a relevant event classified
directly from one terminal guard cell.  The retained plan item supplies the
guarded outer interval and endpoint clearance; cell membership supplies the
missing refinement chain. -/
def RelevantCurveEvent.decideCountOfEventGuardCell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval} {plan : ArcPartitionPlan p path box core}
    (item : PlanEventGuardCell plan)
    (event : RelevantCurveEvent p path box)
    (member : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents item.cell) :
    CurveEventCountDecision p path box event := by
  match coordinateDecision : ProjectivePath.decideClearedCoordinates p path with
  | .identicallyZero realZero imagZero =>
      exact .identicallyZero realZero imagZero
  | .nonzero clearedNonzero =>
      exact .positive
        { clearedNonzero := clearedNonzero
          interval := item.root.interval
          proper := item.root.proper
          lowerClear := item.root.commonFactor_lowerClear clearedNonzero
          upperClear := item.root.commonFactor_upperClear clearedNonzero
          eventRefines := RationalInterval.refines_trans
            (event.parent_refines_of_mem_eventGuardCell member)
            item.cell_refines_root
          positive := event.commonFactorRootCount2_pos clearedNonzero
            item.root.interval item.root.proper
            (item.root.commonFactor_lowerClear clearedNonzero)
            (item.root.commonFactor_upperClear clearedNonzero)
            (RationalInterval.refines_trans
              (event.parent_refines_of_mem_eventGuardCell member)
              item.cell_refines_root) }

/-- Execute the cleared-coordinate dichotomy and, in the nonzero case,
transfer the retained count-one divisor to the plan's whole common factor. -/
def RelevantCurveEvent.decideCountOfPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : BranchInterval}
    (plan : ArcPartitionPlan p path box core)
    (event : RelevantCurveEvent p path box)
    (member : event ∈ relevantCurveEventsOfPlan plan) :
    CurveEventCountDecision p path box event := by
  match coordinateDecision :
      ProjectivePath.decideClearedCoordinates p path with
  | .identicallyZero realZero imagZero =>
      exact .identicallyZero realZero imagZero
  | .nonzero clearedNonzero =>
      cases plan with
      | constant degreeZero =>
          simp [relevantCurveEventsOfPlan] at member
      | factored decomposition root partition =>
          exact .positive
            { clearedNonzero := clearedNonzero
              interval := root.interval
              proper := root.proper
              lowerClear := root.commonFactor_lowerClear clearedNonzero
              upperClear := root.commonFactor_upperClear clearedNonzero
              eventRefines :=
                event.parent_refines_of_mem_factoredPlan member
              positive :=
                event.commonFactorRootCount2_pos_of_mem_factoredPlan member
                  clearedNonzero }

/-- Retain the source/chart label alongside a relevant event extracted from
its guarded partition. -/
structure SourceRelevantCurveEvent
    (p : GaussianPolynomial) (box : RatBox) where
  partition : SourceChartPartition p box
  event : RelevantCurveEvent p partition.entry.chart.path box

/-- Source-label every relevant curve event classified directly from one
terminal guard cell. -/
def relevantCurveEventsOfSourceEventGuardCell
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) :
    List (SourceRelevantCurveEvent p box) :=
  (CCLBranchEvent.EventGuardCell.relevantCurveEvents
    sourceCell.item.cell).map fun event =>
      ⟨sourceCell.partition, event⟩

/-- Flatten cell-local relevant curve events over an executable source-event
family. -/
def relevantCurveEventsOfSourceEventGuardCells
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCells : List (SourceEventGuardCell p box)) :
    List (SourceRelevantCurveEvent p box) :=
  sourceCells.flatMap relevantCurveEventsOfSourceEventGuardCell

/-- A source-labelled cell-local relevant event retains the terminal guard
cell that produced it. -/
theorem relevantCurveEventsOfSourceEventGuardCells_source
    {p : GaussianPolynomial} {box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    {sourceEvent : SourceRelevantCurveEvent p box}
    (member : sourceEvent ∈
      relevantCurveEventsOfSourceEventGuardCells sourceCells) :
    ∃ sourceCell ∈ sourceCells,
      sourceEvent.partition = sourceCell.partition ∧
      sourceEvent.event.parent.interval.Refines
        sourceCell.item.cell.cell.interval := by
  rw [relevantCurveEventsOfSourceEventGuardCells,
    List.mem_flatMap] at member
  rcases member with ⟨sourceCell, sourceCellMember, eventMember⟩
  rw [relevantCurveEventsOfSourceEventGuardCell,
    List.mem_map] at eventMember
  rcases eventMember with ⟨event, eventMember, equality⟩
  cases equality
  exact ⟨sourceCell, sourceCellMember, rfl,
    event.parent_refines_of_mem_eventGuardCell eventMember⟩

/-- A cell-local relevant event retaining the exact source event cell and its
membership proof, so positive-count evidence remains computable. -/
structure SourceGuardCurveEvent
    (p : GaussianPolynomial) (box : RatBox) where
  sourceCell : SourceEventGuardCell p box
  event : RelevantCurveEvent p
    sourceCell.partition.entry.chart.path box
  eventMember : event ∈
    CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell

def guardCurveEventsOfSourceEventGuardCell
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCell : SourceEventGuardCell p box) :
    List (SourceGuardCurveEvent p box) :=
  (CCLBranchEvent.EventGuardCell.relevantCurveEvents
    sourceCell.item.cell).attach.map fun entry =>
      ⟨sourceCell, entry.1, entry.2⟩

def guardCurveEventsOfSourceEventGuardCells
    {p : GaussianPolynomial} {box : RatBox}
    (sourceCells : List (SourceEventGuardCell p box)) :
    List (SourceGuardCurveEvent p box) :=
  sourceCells.flatMap guardCurveEventsOfSourceEventGuardCell

def SourceGuardCurveEvent.toSourceRelevant
    {p : GaussianPolynomial} {box : RatBox}
    (event : SourceGuardCurveEvent p box) :
    SourceRelevantCurveEvent p box :=
  ⟨event.sourceCell.partition, event.event⟩

def SourceGuardCurveEvent.decideCount
    {p : GaussianPolynomial} {box : RatBox}
    (event : SourceGuardCurveEvent p box) :
    CurveEventCountDecision p
      event.sourceCell.partition.entry.chart.path box event.event :=
  event.event.decideCountOfEventGuardCell event.sourceCell.item
    event.eventMember

def relevantCurveEventsOfSourcePartition
    {p : GaussianPolynomial} {box : RatBox}
    (partition : SourceChartPartition p box) :
    List (SourceRelevantCurveEvent p box) :=
  (relevantCurveEventsOfPlan partition.plan).map fun event =>
    ⟨partition, event⟩

/-- Flatten relevant curve events over the at-most-four guarded chart
partitions of a parser state. -/
def relevantCurveEventsOfSourcePartitions
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box)) :
    List (SourceRelevantCurveEvent p box) :=
  partitions.flatMap relevantCurveEventsOfSourcePartition

/-- Source flattening preserves affine-root coverage and returns the exact
originating chart partition alongside the final event interval. -/
theorem relevantCurveEventsOfSourcePartitions_covers_root_nonzero
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box))
    (partition : SourceChartPartition p box)
    (partitionMember : partition ∈ partitions)
    {t : ℚ} (lower : partition.entry.chart.interval.lower ≤ t)
    (upper : t ≤ partition.entry.chart.interval.upper)
    (clearedNonzero :
      (clearedReal p partition.entry.chart.path).isZero = false ∨
      (clearedImag p partition.entry.chart.path).isZero = false)
    (pathDenominator : partition.entry.chart.path.denominator.eval
      (PathPolynomial.ofRat t) ≠ 0)
    (polynomialZero : p.eval (partition.entry.chart.path.value t) = 0)
    (contains : box.Contains (partition.entry.chart.path.value t)) :
    ∃ sourceEvent ∈ relevantCurveEventsOfSourcePartitions partitions,
      sourceEvent.partition = partition ∧
      (boxEventSigns sourceEvent.event.branch
        sourceEvent.event.parent).refined.interval.lower ≤ t ∧
      t ≤ (boxEventSigns sourceEvent.event.branch
        sourceEvent.event.parent).refined.interval.upper ∧
      sourceEvent.event.branch.factor.polynomial.eval t = 0 := by
  rcases relevantCurveEventsOfPlan_covers_root_nonzero partition.plan
      lower upper clearedNonzero pathDenominator polynomialZero contains with
    ⟨event, eventMember, eventLower, eventUpper, eventZero⟩
  let sourceEvent : SourceRelevantCurveEvent p box := ⟨partition, event⟩
  refine ⟨sourceEvent, ?_, rfl, eventLower, eventUpper, eventZero⟩
  rw [relevantCurveEventsOfSourcePartitions, List.mem_flatMap]
  refine ⟨partition, partitionMember, ?_⟩
  rw [relevantCurveEventsOfSourcePartition, List.mem_map]
  exact ⟨event, eventMember, rfl⟩

/-- Flattening relevant events preserves the originating guarded source
partition. -/
theorem SourceRelevantCurveEvent.partition_mem_of_mem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {candidate : SourceRelevantCurveEvent p box}
    (member : candidate ∈ relevantCurveEventsOfSourcePartitions partitions) :
    candidate.partition ∈ partitions := by
  rw [relevantCurveEventsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨partition, partitionMember, eventMember⟩
  rw [relevantCurveEventsOfSourcePartition, List.mem_map] at eventMember
  rcases eventMember with ⟨event, _eventMember, equality⟩
  cases equality
  exact partitionMember

/-- A source-labelled event is one of the events computed by its retained
guarded partition. -/
theorem SourceRelevantCurveEvent.event_mem_of_mem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {candidate : SourceRelevantCurveEvent p box}
    (member : candidate ∈ relevantCurveEventsOfSourcePartitions partitions) :
    candidate.event ∈ relevantCurveEventsOfPlan candidate.partition.plan := by
  rw [relevantCurveEventsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨partition, _partitionMember, eventMember⟩
  rw [relevantCurveEventsOfSourcePartition, List.mem_map] at eventMember
  rcases eventMember with ⟨event, eventMember, equality⟩
  cases equality
  exact eventMember

/-- Source-labelled execution of the identically-zero/positive-count event
dichotomy, retaining the exact guarded chart plan that produced the event. -/
def SourceRelevantCurveEvent.decideCountOfMem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    (candidate : SourceRelevantCurveEvent p box)
    (member : candidate ∈ relevantCurveEventsOfSourcePartitions partitions) :
    CurveEventCountDecision p candidate.partition.entry.chart.path box
      candidate.event :=
  candidate.event.decideCountOfPlan candidate.partition.plan
    (candidate.event_mem_of_mem member)

theorem RelevantCurveEvent.polynomial_eval_eq_zero
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) {t : ℚ}
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    p.eval (path.value t) = 0 :=
  polynomial_eval_eq_zero_of_curve_event event.branch eventZero
    event.curveEquality event.denominatorNonEquality

theorem RelevantCurveEvent.path_denominator_ne
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) {t : ℚ}
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 :=
  path_denominator_ne_of_event event.branch eventZero
    event.denominatorNonEquality

theorem RelevantCurveEvent.contains
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (event : RelevantCurveEvent p path box) {t : ℚ}
    (lower : (boxEventSigns event.branch event.parent).refined.interval.lower ≤ t)
    (upper : t ≤
      (boxEventSigns event.branch event.parent).refined.interval.upper)
    (eventZero : event.branch.factor.polynomial.eval t = 0) :
    box.Contains (path.value t) :=
  (boxEventCheck_eq_contains event.branch event.parent lower upper eventZero
    event.denominatorNonEquality).mp event.meetsBox

end CCLBranchEvent
end FTA
