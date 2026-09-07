import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.BoxedNames
import CCL.Measure.Basic
import FiniteMeasure.Operational
import FiniteMeasure.Schedule
import RFAP.Measure.BoxContent

/-!
# Finite measure observations of boxed CCL names

This module turns each boxed CCL certificate into a generic finite
observation and supplies arbitrarily small rational-area observations of a
progressive site.  The possible predicate is deliberately allowed to refine:
no intersection of all cylinders and no completed point is asserted.
-/

namespace CCL.FiniteMeasure

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Certificate := CCL.BoxedNames.Certificate
abbrev ProgressiveName := CCL.BoxedNames.ProgressiveName
abbrev BoxCover := RFAP.FiniteMeasure.BoxCover

/-- Positive affine request whose square is strictly below a positive area
budget.  The definition uses only rational arithmetic. -/
def areaRadius (target : Coordinate) : Coordinate :=
  min 1 (target / 4)

theorem areaRadius_pos {target : Coordinate} (positive : 0 < target) :
    0 < areaRadius target := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))

theorem areaRadius_sq_lt {target : Coordinate} (positive : 0 < target) :
    areaRadius target ^ 2 < target := by
  let radius := areaRadius target
  have radiusPositive : 0 < radius := areaRadius_pos positive
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeQuarter : radius ≤ target / 4 := min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq
        (RFAP.ConstructiveFraction.one_mul radius)
  have radiusLtFourRadius : radius < 4 * radius := by
    calc
      radius = 1 * radius :=
        (RFAP.ConstructiveFraction.one_mul radius).symm
      _ < 4 * radius :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) radiusPositive
  have fourRadiusLe : 4 * radius ≤ target := by
    have divided :=
      (RFAP.ConstructiveFraction.le_div_iff_pos
        (by decide : (0 : Coordinate) < 4)).mp radiusLeQuarter
    calc
      4 * radius = radius * 4 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ ≤ target := divided
  exact radiusSquareLe.trans_lt (radiusLtFourRadius.trans_le fourRadiusLe)

namespace Certificate

/-- Squared affine distance used by the neutral finite-observation layer. -/
def affineDistance (left right : Gaussian) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq (left - right)

/-- A boxed CCL certificate is a finitely satisfiable pairwise-small
observation. -/
def toObservation (certificate : Certificate) :
    _root_.FiniteMeasure.Observation Gaussian affineDistance where
  Possible := certificate.Possible
  witness := certificate.witness
  witness_possible :=
    ⟨certificate.witness_nonzero, certificate.witness_represented⟩
  spread := certificate.box.diagonalSq
  spread_nonnegative := certificate.box.diagonalSq_nonneg
  pairwise := by
    intro left right leftPossible rightPossible
    exact certificate.box.normSq_sub_le_diagonalSq
      (certificate.possible_inside leftPossible)
      (certificate.possible_inside rightPossible)

theorem observation_refines {inner outer : Certificate}
    (refines : CCL.BoxedNames.Refines inner outer) :
    _root_.FiniteMeasure.Observation.Refines inner.toObservation
      outer.toObservation :=
  ⟨fun possible => refines.possible_persists possible⟩

end Certificate

namespace ProgressiveName

/-- Generic finite-request observation protocol underlying one boxed CCL
name.  Its accuracy request is expressed directly as a squared-distance
budget, and every returned state remains finite. -/
def toObservation (name : ProgressiveName) :
    _root_.FiniteMeasure.ProgressiveObservation Gaussian
      Certificate.affineDistance where
  State := name.State
  observation state := Certificate.toObservation (name.certificate state)
  initial := name.initial
  request state epsilon positive :=
    name.request state (areaRadius epsilon) (areaRadius_pos positive)
  request_refines state epsilon positive :=
    Certificate.observation_refines
      (name.request_refines state (areaRadius epsilon)
        (areaRadius_pos positive))
  accurate state epsilon positive :=
    (name.accurate state (areaRadius epsilon)
      (areaRadius_pos positive)).trans_lt (areaRadius_sq_lt positive)
  refinesInitial state :=
    Certificate.observation_refines (name.refinesInitial state)

/-- Execute a displayed finite batch of squared-distance requests on a boxed
name.  The result is still one finite CCL state. -/
def runAccuracyRequests (name : ProgressiveName) (state : name.State)
    (requests : List _root_.FiniteMeasure.AccuracyRequest) : name.State :=
  name.toObservation.runRequests state requests

/-- Candidates at the end of a displayed finite CCL request batch meet every
tolerance that occurred in that batch. -/
theorem runAccuracyRequests_pairwise_lt_of_mem
    (name : ProgressiveName) (state : name.State)
    (requests : List _root_.FiniteMeasure.AccuracyRequest)
    (request : _root_.FiniteMeasure.AccuracyRequest)
    (member : request ∈ requests) {left right : Gaussian}
    (leftPossible :
      (name.certificate (name.runAccuracyRequests state requests)).Possible left)
    (rightPossible :
      (name.certificate (name.runAccuracyRequests state requests)).Possible right) :
    Certificate.affineDistance left right < request.tolerance := by
  exact name.toObservation.runRequests_pairwise_lt_of_mem
    state requests request member leftPossible rightPossible

/-- The explicit witness after a finite CCL request batch remains possible
at the distinguished initial certificate. -/
theorem runAccuracyRequests_witness_possible_initial
    (name : ProgressiveName) (state : name.State)
    (requests : List _root_.FiniteMeasure.AccuracyRequest) :
    (name.certificate name.initial).Possible
      (name.certificate
        (name.runAccuracyRequests state requests)).witness := by
  exact name.toObservation.runRequests_witness_possible_initial state requests

/-- The finite refinement certificate used for one rational area request. -/
def areaCertificate (name : ProgressiveName) (state : name.State)
    (target : Coordinate) (positive : 0 < target) : Certificate :=
  name.certificate
    (name.request state (areaRadius target) (areaRadius_pos positive))

theorem areaCertificate_refines (name : ProgressiveName)
    (state : name.State) (target : Coordinate) (positive : 0 < target) :
    CCL.BoxedNames.Refines (name.areaCertificate state target positive)
      (name.certificate state) :=
  name.request_refines state (areaRadius target) (areaRadius_pos positive)

/-- Every candidate admitted by the refined CCL prefix lies in its displayed
one-box cover. -/
theorem areaCertificate_cover (name : ProgressiveName)
    (state : name.State) (target : Coordinate) (positive : 0 < target) :
    (RFAP.FiniteMeasure.BoxCover.mk
      [(name.areaCertificate state target positive).box]).Covers
      (name.areaCertificate state target positive).Possible := by
  intro point possible
  exact ⟨(name.areaCertificate state target positive).box,
    List.mem_cons_self,
    (name.areaCertificate state target positive).possible_inside possible⟩

/-- Every positive rational request produces a finite CCL certificate whose
rational enclosing area is strictly below that request. -/
theorem areaCertificate_content_lt (name : ProgressiveName)
    (state : name.State) (target : Coordinate) (positive : 0 < target) :
    RFAP.FiniteMeasure.boxContent
      (name.areaCertificate state target positive).box < target := by
  apply RFAP.FiniteMeasure.boxContent_lt_of_diagonalSq_lt
  exact (name.accurate state (areaRadius target)
    (areaRadius_pos positive)).trans_lt (areaRadius_sq_lt positive)

theorem areaCover_content_lt (name : ProgressiveName)
    (state : name.State) (target : Coordinate) (positive : 0 < target) :
    RFAP.FiniteMeasure.BoxCover.content
      (RFAP.FiniteMeasure.BoxCover.mk
        [(name.areaCertificate state target positive).box]) <
      target := by
  simpa only [RFAP.FiniteMeasure.BoxCover.content, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      name.areaCertificate_content_lt state target positive

/-- Executable finite process for the shrinking rational area budget of one
boxed CCL name.  Its bounds are `[0, current box area]`; it does not assign a
measure to a completed decoded value. -/
def toAreaProcess (name : ProgressiveName) :
    _root_.FiniteMeasure.BoundProcess where
  State := name.State
  bound state := RFAP.FiniteMeasure.boxContentBound
    (name.certificate state).box
  initial := name.initial
  request state target positive :=
    name.request state (areaRadius target) (areaRadius_pos positive)
  request_refines state target positive := by
    apply RFAP.FiniteMeasure.boxContentBound_refines
    exact (name.request_refines state (areaRadius target)
      (areaRadius_pos positive)).box
  accurate state target positive := by
    rw [RFAP.FiniteMeasure.boxContentBound_width]
    exact name.areaCertificate_content_lt state target positive
  refinesInitial state := by
    apply RFAP.FiniteMeasure.boxContentBound_refines
    exact (name.refinesInitial state).box

theorem toAreaProcess_anchored (name : ProgressiveName) :
    name.toAreaProcess.AnchoredAt 0 := by
  intro state
  exact ⟨le_rfl,
    RFAP.FiniteMeasure.boxContent_nonneg (name.certificate state).box⟩

/-- The shrinking area-budget controller is operationally equivalent to the
exact rational zero process, via finite requests only. -/
theorem toAreaProcess_operationallyEquivalent_zero (name : ProgressiveName) :
    _root_.FiniteMeasure.OperationallyEquivalent name.toAreaProcess
      (_root_.FiniteMeasure.BoundProcess.exact 0) :=
  _root_.FiniteMeasure.operationallyEquivalent_exact_of_anchoredAt
    name.toAreaProcess 0 name.toAreaProcess_anchored

end ProgressiveName

/-! ## Simultaneous observations of a finite family -/

/-- Recursively allocate half of the current budget to the head site and half
to all remaining sites.  Every output remains a complete finite CCL
certificate with its own word, witness, and box. -/
def familyCertificates : (names : List ProgressiveName) →
    (target : Coordinate) → 0 < target → List Certificate
  | [], _, _ => []
  | name :: remaining, target, positive =>
      let half := target / 2
      let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
        (by decide : (0 : Coordinate) < 2)
      name.areaCertificate name.initial half halfPositive ::
        familyCertificates remaining half halfPositive

@[simp] theorem familyCertificates_length (names : List ProgressiveName)
    (target : Coordinate) (positive : 0 < target) :
    (familyCertificates names target positive).length = names.length := by
  induction names generalizing target with
  | nil => rfl
  | cons name remaining inductionHypothesis =>
      simp only [familyCertificates, List.length_cons]
      rw [inductionHypothesis]

/-- Sum of the rational box areas displayed by a finite CCL family. -/
def familyContent (certificates : List Certificate) : Coordinate :=
  (certificates.map fun certificate =>
    RFAP.FiniteMeasure.boxContent certificate.box).sum

/-- Pointwise union of the candidate predicates carried by a displayed
finite certificate family. -/
def familyPossible : List Certificate → Gaussian → Prop
  | [], _ => False
  | certificate :: remaining, point =>
      certificate.Possible point ∨ familyPossible remaining point

/-- One finite box cover obtained by forgetting all certificate data except
the displayed enclosing boxes. -/
def familyCover (certificates : List Certificate) : BoxCover :=
  ⟨certificates.map fun certificate => certificate.box⟩

theorem familyCover_covers : ∀ certificates : List Certificate,
    (familyCover certificates).Covers (familyPossible certificates)
  | [] => by
      intro point impossible
      exact impossible.elim
  | certificate :: remaining => by
      intro point member
      rcases member with head | tail
      · exact ⟨certificate.box, List.mem_cons_self,
          certificate.possible_inside head⟩
      · rcases familyCover_covers remaining point tail with
          ⟨box, boxMember, inside⟩
        exact ⟨box, List.mem_cons_of_mem certificate.box boxMember, inside⟩

theorem familyCover_content (certificates : List Certificate) :
    (familyCover certificates).content = familyContent certificates := by
  induction certificates with
  | nil => rfl
  | cons certificate remaining inductionHypothesis =>
      simp only [familyCover, RFAP.FiniteMeasure.BoxCover.content,
        familyContent, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]

/-- A finite family of progressive CCL sites can be observed simultaneously
inside an arbitrarily small total rational area budget. -/
theorem familyCertificates_content_lt :
    ∀ (names : List ProgressiveName) (target : Coordinate)
      (positive : 0 < target),
      familyContent (familyCertificates names target positive) < target
  | [], target, positive => by
      simpa only [familyCertificates, familyContent, List.map_nil,
        List.sum_nil] using positive
  | name :: remaining, target, positive => by
      let half := target / 2
      have halfPositive : (0 : Coordinate) < half :=
        RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
      have headSmall :=
        name.areaCertificate_content_lt name.initial half halfPositive
      have tailSmall :=
        familyCertificates_content_lt remaining half halfPositive
      dsimp only [familyCertificates, familyContent]
      rw [List.map_cons, List.sum_cons]
      calc
        RFAP.FiniteMeasure.boxContent
              (name.areaCertificate name.initial half halfPositive).box +
            familyContent
              (familyCertificates remaining half halfPositive) <
            half + half :=
          RFAP.ConstructiveFraction.add_lt_add_direct headSmall tailSmall
        _ = target := by
          dsimp only [half]
          calc
            target / 2 + target / 2 = (target / 2) * 2 := by ring1
            _ = target :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2
                (by decide)

/-- The simultaneous finite CCL request returns a genuine finite cover of
the union of all its returned candidate predicates. -/
theorem familyCertificates_cover (names : List ProgressiveName)
    (target : Coordinate) (positive : 0 < target) :
    (familyCover (familyCertificates names target positive)).Covers
      (familyPossible (familyCertificates names target positive)) :=
  familyCover_covers _

theorem familyCertificates_cover_content_lt
    (names : List ProgressiveName) (target : Coordinate)
    (positive : 0 < target) :
    (familyCover (familyCertificates names target positive)).content <
      target := by
  rw [familyCover_content]
  exact familyCertificates_content_lt names target positive

end CCL.FiniteMeasure
