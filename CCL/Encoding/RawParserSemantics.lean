import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.RawParser

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

namespace CCL.RawParserSemantics

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Word := List Bool

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser

/-- The lower row of a product evaluates as the outer lower row applied to
the right factor's affine numerator and denominator. -/
theorem denominator_mul_expanded (left right : Mat2) (tail : Gaussian) :
    denominator (CCL.Mat2.mul left right) tail =
      left.c * numerator right tail + left.d * denominator right tail := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [denominator, numerator, CCL.Mat2.mul, mul_re, mul_im,
      add_re, add_im] <;>
    ring1

/-- Once the inner denominator is nonzero, the product denominator factors
through the inner homographic value. -/
theorem denominator_mul (left right : Mat2) (tail : Gaussian)
    (rightDenominator : denominator right tail ≠ 0) :
    denominator (CCL.Mat2.mul left right) tail =
      denominator left (homographic right tail) * denominator right tail := by
  rw [denominator_mul_expanded]
  have cancel :
      homographic right tail * denominator right tail =
        numerator right tail := by
    unfold homographic
    rw [mul_assoc, inv_eq, inv_mul _ rightDenominator,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  calc
    left.c * numerator right tail + left.d * denominator right tail =
        left.c * (homographic right tail * denominator right tail) +
          left.d * denominator right tail := by rw [cancel]
    _ = denominator left (homographic right tail) *
          denominator right tail := by
      unfold denominator
      ring1

/-- The upper row has the analogous product expansion. -/
theorem numerator_mul_expanded (left right : Mat2) (tail : Gaussian) :
    numerator (CCL.Mat2.mul left right) tail =
      left.a * numerator right tail + left.b * denominator right tail := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [denominator, numerator, CCL.Mat2.mul, mul_re, mul_im,
      add_re, add_im] <;>
    ring1

theorem numerator_mul (left right : Mat2) (tail : Gaussian)
    (rightDenominator : denominator right tail ≠ 0) :
    numerator (CCL.Mat2.mul left right) tail =
      numerator left (homographic right tail) * denominator right tail := by
  rw [numerator_mul_expanded]
  have cancel :
      homographic right tail * denominator right tail =
        numerator right tail := by
    unfold homographic
    rw [mul_assoc, inv_eq, inv_mul _ rightDenominator,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  calc
    left.a * numerator right tail + left.b * denominator right tail =
        left.a * (homographic right tail * denominator right tail) +
          left.b * denominator right tail := by rw [cancel]
    _ = numerator left (homographic right tail) *
          denominator right tail := by
      unfold numerator
      ring1

/-- Exact nonvanishing transport for a product denominator. -/
theorem denominator_mul_ne_iff (left right : Mat2) (tail : Gaussian)
    (rightDenominator : denominator right tail ≠ 0) :
    denominator (CCL.Mat2.mul left right) tail ≠ 0 ↔
      denominator left (homographic right tail) ≠ 0 := by
  rw [denominator_mul left right tail rightDenominator]
  constructor
  · intro productNonzero leftZero
    apply productNonzero
    rw [leftZero, zero_mul]
  · intro leftNonzero
    exact mul_ne_zero_direct leftNonzero rightDenominator

/-- Reassociate a product of four factors without invoking normalization
machinery for inverse expressions. -/
theorem mul_pair_reassociate (a b c d : Gaussian) :
    (a * b) * (c * d) = (a * (b * c)) * d := by
  calc
    (a * b) * (c * d) = ((a * b) * c) * d :=
      (RFAP.ConstructiveGaussian.Gaussian.mul_assoc (a * b) c d).symm
    _ = (a * (b * c)) * d := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc a b c]

/-- Affine homographies compose in decoder-product order. -/
theorem homographic_mul (left right : Mat2) (tail : Gaussian)
    (rightDenominator : denominator right tail ≠ 0)
    (leftDenominator : denominator left (homographic right tail) ≠ 0) :
    homographic (CCL.Mat2.mul left right) tail =
      homographic left (homographic right tail) := by
  have productDenominator :
      denominator (CCL.Mat2.mul left right) tail ≠ 0 :=
    (denominator_mul_ne_iff left right tail rightDenominator).2
      leftDenominator
  rw [show homographic (CCL.Mat2.mul left right) tail =
      numerator (CCL.Mat2.mul left right) tail *
        (denominator (CCL.Mat2.mul left right) tail)⁻¹ by rfl]
  rw [numerator_mul left right tail rightDenominator,
    denominator_mul left right tail rightDenominator]
  rw [show homographic left (homographic right tail) =
      numerator left (homographic right tail) *
        (denominator left (homographic right tail))⁻¹ by rfl]
  let outerDenominator := denominator left (homographic right tail)
  let innerDenominator := denominator right tail
  let valueNumerator := numerator left (homographic right tail)
  have combinedNonzero : outerDenominator * innerDenominator ≠ 0 :=
    mul_ne_zero_direct leftDenominator rightDenominator
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    combinedNonzero
  calc
    ((valueNumerator * innerDenominator) *
          (outerDenominator * innerDenominator)⁻¹) *
        (outerDenominator * innerDenominator) =
        valueNumerator * innerDenominator := by
      rw [mul_assoc, inv_eq, inv_mul _ combinedNonzero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = (valueNumerator * outerDenominator⁻¹) *
        (outerDenominator * innerDenominator) := by
      symm
      calc
        (valueNumerator * outerDenominator⁻¹) *
            (outerDenominator * innerDenominator) =
            (valueNumerator *
                (outerDenominator⁻¹ * outerDenominator)) *
              innerDenominator :=
          mul_pair_reassociate valueNumerator outerDenominator⁻¹
            outerDenominator innerDenominator
        _ = valueNumerator * innerDenominator := by
          rw [inv_eq, inv_mul _ leftDenominator,
            RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- A decoder with nonzero determinant is injective on affine tails whose
displayed denominators are nonzero. -/
theorem homographic_injective
    (matrix : Mat2) {left right : Gaussian}
    (determinant : CCL.Chordal.Mat2.det matrix ≠ 0)
    (leftDenominator : denominator matrix left ≠ 0)
    (rightDenominator : denominator matrix right ≠ 0)
    (images : homographic matrix left = homographic matrix right) :
    left = right := by
  have cross : numerator matrix left * denominator matrix right =
      numerator matrix right * denominator matrix left := by
    rw [show numerator matrix left =
        homographic matrix left * denominator matrix left by
      unfold homographic
      rw [mul_assoc, inv_eq, inv_mul _ leftDenominator,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]]
    rw [show numerator matrix right =
        homographic matrix right * denominator matrix right by
      unfold homographic
      rw [mul_assoc, inv_eq, inv_mul _ rightDenominator,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]]
    rw [images]
    ring1
  have factored :
      CCL.Chordal.Mat2.det matrix * (left + -right) = 0 := by
    calc
      CCL.Chordal.Mat2.det matrix * (left + -right) =
          numerator matrix left * denominator matrix right +
            -(numerator matrix right * denominator matrix left) := by
        unfold CCL.Chordal.Mat2.det numerator denominator
        rw [RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg]
        ring1
      _ = 0 := by rw [cross]; ring1
  have differenceZero : left + -right = 0 := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne determinant
    calc
      (left + -right) * CCL.Chordal.Mat2.det matrix =
          CCL.Chordal.Mat2.det matrix * (left + -right) := by ring1
      _ = 0 := factored
      _ = 0 * CCL.Chordal.Mat2.det matrix := by
        rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · have realDifference := congrArg
      RFAP.ConstructiveGaussian.Gaussian.re differenceZero
    change left.re + -right.re = 0 at realDifference
    apply sub_eq_zero.mp
    calc
      left.re - right.re = left.re + -right.re :=
        _root_.sub_eq_add_neg _ _
      _ = 0 := realDifference
  · have imaginaryDifference := congrArg
      RFAP.ConstructiveGaussian.Gaussian.im differenceZero
    change left.im + -right.im = 0 at imaginaryDifference
    apply sub_eq_zero.mp
    calc
      left.im - right.im = left.im + -right.im :=
        _root_.sub_eq_add_neg _ _
      _ = 0 := imaginaryDifference

/-- Pulling a historical constraint through a newly completed block has its
intended affine meaning. -/
theorem constraint_precompose_iff
    (constraint : Constraint) (block : Mat2) (tail : Gaussian)
    (blockDenominator : denominator block tail ≠ 0) :
    (constraint.precompose block).Holds tail ↔
      constraint.Holds (homographic block tail) := by
  constructor
  · rintro ⟨productDenominator, blockHolds⟩
    have oldDenominator :
        denominator constraint.matrix (homographic block tail) ≠ 0 :=
      (denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).1 productDenominator
    refine ⟨oldDenominator, ?_⟩
    rw [← homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds
  · rintro ⟨oldDenominator, blockHolds⟩
    have productDenominator :
        denominator (CCL.Mat2.mul constraint.matrix block) tail ≠ 0 :=
      (denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).2 oldDenominator
    refine ⟨productDenominator, ?_⟩
    change fullBlockHolds constraint.kind constraint.exponent
      constraint.sector
        (homographic (CCL.Mat2.mul constraint.matrix block) tail)
    rw [homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds

/-- A parser state represents an original affine input via a current affine
tail and the accumulated decoder matrix. -/
def Represents (state : State) (input tail : Gaussian) : Prop :=
  denominator state.matrix tail ≠ 0 ∧
    input = homographic state.matrix tail ∧ state.Holds tail

/-- An invertible parser state has at most one affine tail representing a
fixed input. -/
theorem Represents.tail_unique
    {state : State} {input left right : Gaussian}
    (determinant : CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (leftRepresents : Represents state input left)
    (rightRepresents : Represents state input right) : left = right := by
  apply homographic_injective state.matrix determinant leftRepresents.1
    rightRepresents.1
  exact leftRepresents.2.1.symm.trans rightRepresents.2.1

/-- Before any bit is consumed, the current tail is the original input. -/
theorem initialState_represents (input : Gaussian) :
    Represents initialState input input := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [denominator, initialState, identityMatrix,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add]
    decide
  · change input = ((1 : Gaussian) * input + 0) *
      ((0 : Gaussian) * input + 1)⁻¹
    rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
      RFAP.ConstructiveGaussian.Gaussian.add_zero,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add, inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_one_direct,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  · change (∀ constraint ∈ ([] : List Constraint),
        constraint.Holds input) ∧ True
    exact ⟨fun _constraint member => by
      simp only [List.not_mem_nil] at member, True.intro⟩

theorem sectorOfBits_mem_two_candidates (first second third : Bool) :
    sectorOfBits first second third ∈
      sectorCandidates (.two first second) := by
  cases first <;> cases second <;> cases third <;> decide

/-- Extending the unfinished sector code only shrinks its finite row list. -/
theorem sectorCandidates_mono
    {earlier later : SectorBits}
    (codePrefix : isWordPrefix earlier.word later.word = true)
    {sector : Sector}
    (member : sector ∈ sectorCandidates later) :
    sector ∈ sectorCandidates earlier := by
  rcases List.mem_filter.mp member with ⟨tableMember, laterPrefix⟩
  apply List.mem_filter.mpr
  refine ⟨tableMember, ?_⟩
  exact isWordPrefix_trans codePrefix laterPrefix

/-- The newest completed-block constraint and all rebased historical
constraints recover the predicate of the preceding parser state. -/
theorem completeSector_holds_previous
    (state : State) (kind : BlockKind) (exponent : Nat)
    (first second third : Bool) (tail : Gaussian)
    (phase : state.phase = .sector kind exponent (.two first second))
    (holds :
      (completeSector state kind exponent first second third).Holds tail) :
    state.Holds
      (homographic
        (blockMatrix kind exponent (sectorOfBits first second third)) tail) := by
  let sector := sectorOfBits first second third
  let block := blockMatrix kind exponent sector
  have newest : (Constraint.mk block kind exponent sector).Holds tail := by
    apply holds.1
    change Constraint.mk block kind exponent sector ∈
      Constraint.mk block kind exponent sector ::
        state.history.map (fun item => item.precompose block)
    exact List.mem_cons_self
  have blockDenominator : denominator block tail ≠ 0 := newest.1
  have full :
      fullBlockHolds kind exponent sector (homographic block tail) := newest.2
  constructor
  · intro constraint member
    have mapped : (constraint.precompose block).Holds tail := by
      apply holds.1
      change constraint.precompose block ∈
        (Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block)
      exact List.mem_cons_of_mem _
        (QuotientFreeList.mem_map.mpr ⟨constraint, member, rfl⟩)
    exact (constraint_precompose_iff constraint block tail
      blockDenominator).1 mapped
  · rw [phase]
    exact ⟨full.1, sector,
      sectorOfBits_mem_two_candidates first second third, full.2⟩

/-- Completing the third sector bit changes affine-tail coordinates but
preserves the represented original input. -/
theorem completeSector_represents_previous
    (state : State) (kind : BlockKind) (exponent : Nat)
    (first second third : Bool) (input tail : Gaussian)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Represents
      (completeSector state kind exponent first second third) input tail) :
    Represents state input
      (homographic
        (blockMatrix kind exponent (sectorOfBits first second third)) tail) := by
  let sector := sectorOfBits first second third
  let block := blockMatrix kind exponent sector
  have newest : (Constraint.mk block kind exponent sector).Holds tail := by
    apply represents.2.2.1
    change Constraint.mk block kind exponent sector ∈
      Constraint.mk block kind exponent sector ::
        state.history.map (fun item => item.precompose block)
    exact List.mem_cons_self
  have blockDenominator : denominator block tail ≠ 0 := newest.1
  have productDenominator :
      denominator (CCL.Mat2.mul state.matrix block) tail ≠ 0 := by
    simpa [completeSector, sector, block] using represents.1
  have oldDenominator :
      denominator state.matrix (homographic block tail) ≠ 0 :=
    (denominator_mul_ne_iff state.matrix block tail
      blockDenominator).1 productDenominator
  refine ⟨oldDenominator, ?_, ?_⟩
  · calc
      input = homographic (CCL.Mat2.mul state.matrix block) tail := by
        simpa [completeSector, sector, block] using represents.2.1
      _ = homographic state.matrix (homographic block tail) :=
        homographic_mul state.matrix block tail blockDenominator oldDenominator
  · exact completeSector_holds_previous state kind exponent first second third
      tail phase represents.2.2

theorem step_eq_completeSector
    (state : State) (kind : BlockKind) (exponent : Nat)
    (first second third : Bool)
    (phase : state.phase = .sector kind exponent (.two first second)) :
    step state third =
      completeSector state kind exponent first second third := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  rfl

/-- The affine tail before one bit; only a third sector bit changes it. -/
def previousTail (state : State) (bit : Bool) (tail : Gaussian) : Gaussian :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      homographic
        (blockMatrix kind exponent (sectorOfBits first second bit)) tail
  | _ => tail

theorem represents_with_previous_phase
    (oldPhase newPhase : Phase) (matrix : Mat2)
    (history : List Constraint) (input tail : Gaussian)
    (represents : Represents ⟨newPhase, matrix, history⟩ input tail)
    (active : activeHolds oldPhase tail) :
    Represents ⟨oldPhase, matrix, history⟩ input tail :=
  ⟨represents.1, represents.2.1, represents.2.2.1, active⟩

theorem two_pow_le_succ (count : Nat) :
    (2 : Coordinate) ^ count ≤ (2 : Coordinate) ^ (count + 1) := by
  have powerNonnegative : 0 ≤ (2 : Coordinate) ^ count :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count
  calc
    (2 : Coordinate) ^ count = (2 : Coordinate) ^ count * 1 := by ring1
    _ ≤ (2 : Coordinate) ^ count * 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (by decide) powerNonnegative
    _ = (2 : Coordinate) ^ (count + 1) := by
      rw [pow_succ]

theorem lower_low_active_of_radial_upper
    (count : Nat) (value : Gaussian)
    (upper : (2 : Coordinate) ^ (count + 1) * normSq value < 2) :
    (2 : Coordinate) ^ count * normSq value < 1 := by
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (2 : Coordinate)) _ (by decide)
  calc
    ((2 : Coordinate) ^ count * normSq value) * 2 =
        (2 : Coordinate) ^ (count + 1) * normSq value := by
      rw [pow_succ]
      ring1
    _ < 2 := upper
    _ = (1 : Coordinate) * 2 := by ring1

theorem lower_low_active_of_next
    (count : Nat) (value : Gaussian)
    (next : (2 : Coordinate) ^ (count + 1) * normSq value < 1) :
    (2 : Coordinate) ^ count * normSq value < 1 := by
  let oldValue := (2 : Coordinate) ^ count * normSq value
  have oldNonnegative : 0 ≤ oldValue :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
      (normSq_nonneg value)
  have oneLeTwo : (1 : Coordinate) ≤ 2 := by decide
  calc
    oldValue = oldValue * 1 := by ring1
    _ ≤ oldValue * 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        oneLeTwo oldNonnegative
    _ = (2 : Coordinate) ^ (count + 1) * normSq value := by
      dsimp only [oldValue]
      rw [pow_succ]
      ring1
    _ < 1 := next

theorem step_represents_previous_initial
    (matrix : Mat2) (history : List Constraint) (bit : Bool)
    (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.initial, matrix, history⟩ bit) input tail) :
    Represents ⟨Phase.initial, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Represents
          ⟨Phase.lowUnary 0, matrix, history⟩ input tail := by
        simpa [step] using represents
      exact represents_with_previous_phase .initial (.lowUnary 0) matrix
        history input tail after (by simp [activeHolds])
  | true =>
      have after : Represents
          ⟨Phase.highUnary 1, matrix, history⟩ input tail := by
        simpa [step] using represents
      exact represents_with_previous_phase .initial (.highUnary 1) matrix
        history input tail after (by simp [activeHolds])

theorem step_represents_previous_highUnary
    (count : Nat) (matrix : Mat2) (history : List Constraint) (bit : Bool)
    (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.highUnary count, matrix, history⟩ bit) input tail) :
    Represents ⟨Phase.highUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Represents
          ⟨Phase.sector .initialHigh count .zero,
            matrix, history⟩ input tail := by
        simpa [step] using represents
      have active : activeHolds (.highUnary count) tail :=
        after.2.2.2.1.1
      exact represents_with_previous_phase (.highUnary count)
        (.sector .initialHigh count .zero) matrix history input tail after active
  | true =>
      have after : Represents
          ⟨Phase.highUnary (count + 1), matrix, history⟩ input tail := by
        simpa [step] using represents
      have active : activeHolds (.highUnary count) tail :=
        (two_pow_le_succ count).trans after.2.2.2
      exact represents_with_previous_phase (.highUnary count)
        (.highUnary (count + 1)) matrix history input tail after active

theorem step_represents_previous_lowUnary
    (count : Nat) (matrix : Mat2) (history : List Constraint) (bit : Bool)
    (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.lowUnary count, matrix, history⟩ bit) input tail) :
    Represents ⟨Phase.lowUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Represents
          ⟨Phase.sector .initialLow count .zero,
            matrix, history⟩ input tail := by
        simpa [step] using represents
      cases count with
      | zero =>
          have active : activeHolds (.lowUnary 0) tail := by
            simpa [activeHolds] using after.2.2.2.1.2
          exact represents_with_previous_phase (.lowUnary 0)
            (.sector .initialLow 0 .zero) matrix history input tail after active
      | succ count =>
          have active : activeHolds (.lowUnary (count + 1)) tail :=
            lower_low_active_of_radial_upper count tail after.2.2.2.1.2
          exact represents_with_previous_phase (.lowUnary (count + 1))
            (.sector .initialLow (count + 1) .zero) matrix history input tail
            after active
  | true =>
      have after : Represents
          ⟨Phase.lowUnary (count + 1), matrix, history⟩ input tail := by
        simpa [step] using represents
      cases count with
      | zero =>
          have active : activeHolds (.lowUnary 0) tail := by
            have newer : normSq tail < 1 := by
              simpa [activeHolds] using after.2.2.2
            exact newer.trans (by decide)
          exact represents_with_previous_phase (.lowUnary 0) (.lowUnary 1)
            matrix history input tail after active
      | succ count =>
          have active : activeHolds (.lowUnary (count + 1)) tail :=
            lower_low_active_of_next count tail after.2.2.2
          exact represents_with_previous_phase (.lowUnary (count + 1))
            (.lowUnary (count + 2)) matrix history input tail after active

theorem step_represents_previous_loopUnary
    (count : Nat) (matrix : Mat2) (history : List Constraint) (bit : Bool)
    (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.loopUnary count, matrix, history⟩ bit) input tail) :
    Represents ⟨Phase.loopUnary count, matrix, history⟩ input tail := by
  cases bit with
  | false =>
      have after : Represents
          ⟨Phase.sector .loop count .zero, matrix, history⟩ input tail := by
        simpa [step] using represents
      have active : activeHolds (.loopUnary count) tail :=
        after.2.2.2.1.1
      exact represents_with_previous_phase (.loopUnary count)
        (.sector .loop count .zero) matrix history input tail after active
  | true =>
      have after : Represents
          ⟨Phase.loopUnary (count + 1), matrix, history⟩ input tail := by
        simpa [step] using represents
      have active : activeHolds (.loopUnary count) tail :=
        (two_pow_le_succ count).trans_lt after.2.2.2
      exact represents_with_previous_phase (.loopUnary count)
        (.loopUnary (count + 1)) matrix history input tail after active

theorem step_represents_previous_sector_zero
    (kind : BlockKind) (exponent : Nat) (matrix : Mat2)
    (history : List Constraint) (bit : Bool) (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.sector kind exponent .zero, matrix, history⟩ bit)
        input tail) :
    Represents ⟨Phase.sector kind exponent .zero, matrix, history⟩
      input tail := by
  have after : Represents
      ⟨Phase.sector kind exponent (.one bit),
        matrix, history⟩ input tail := by
    simpa [step] using represents
  rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
  have oldMember : sector ∈ sectorCandidates .zero :=
    sectorCandidates_mono rfl member
  have active : activeHolds (.sector kind exponent .zero) tail :=
    ⟨radial, sector, oldMember, sectorHolds⟩
  exact represents_with_previous_phase (.sector kind exponent .zero)
    (.sector kind exponent (.one bit)) matrix history input tail after active

theorem step_represents_previous_sector_one
    (kind : BlockKind) (exponent : Nat) (first : Bool) (matrix : Mat2)
    (history : List Constraint) (bit : Bool) (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.sector kind exponent (.one first), matrix, history⟩ bit)
        input tail) :
    Represents ⟨Phase.sector kind exponent (.one first), matrix, history⟩
      input tail := by
  have after : Represents
      ⟨Phase.sector kind exponent (.two first bit),
        matrix, history⟩ input tail := by
    simpa [step] using represents
  rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
  have oldMember : sector ∈ sectorCandidates (.one first) :=
    sectorCandidates_mono (by cases first <;> rfl) member
  have active : activeHolds
      (.sector kind exponent (.one first)) tail :=
    ⟨radial, sector, oldMember, sectorHolds⟩
  exact represents_with_previous_phase (.sector kind exponent (.one first))
    (.sector kind exponent (.two first bit)) matrix history input tail
    after active

theorem step_represents_previous_sector_two
    (kind : BlockKind) (exponent : Nat) (first second : Bool) (matrix : Mat2)
    (history : List Constraint) (bit : Bool) (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.sector kind exponent (.two first second), matrix, history⟩
        bit) input tail) :
    Represents ⟨Phase.sector kind exponent (.two first second), matrix, history⟩
      input (previousTail
        ⟨Phase.sector kind exponent (.two first second), matrix, history⟩
        bit tail) := by
  simpa [previousTail, step] using
    completeSector_represents_previous
      ⟨Phase.sector kind exponent (.two first second), matrix, history⟩
      kind exponent first second bit input tail rfl represents

theorem step_represents_previous_sector
    (kind : BlockKind) (exponent : Nat) (bits : SectorBits)
    (matrix : Mat2) (history : List Constraint) (bit : Bool)
    (input tail : Gaussian)
    (represents : Represents
      (step ⟨Phase.sector kind exponent bits, matrix, history⟩ bit)
        input tail) :
    Represents ⟨Phase.sector kind exponent bits, matrix, history⟩ input
      (previousTail ⟨Phase.sector kind exponent bits, matrix, history⟩
        bit tail) := by
  cases bits with
  | zero =>
      have after : Represents
          ⟨Phase.sector kind exponent (.one bit),
            matrix, history⟩ input tail := by
        simpa [step] using represents
      rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
      have oldMember : sector ∈ sectorCandidates .zero :=
        sectorCandidates_mono rfl member
      have active : activeHolds (.sector kind exponent .zero) tail :=
        ⟨radial, sector, oldMember, sectorHolds⟩
      simpa [previousTail] using
        represents_with_previous_phase (.sector kind exponent .zero)
          (.sector kind exponent (.one bit)) matrix history input tail
          after active
  | one first =>
      have after : Represents
          ⟨Phase.sector kind exponent (.two first bit),
            matrix, history⟩ input tail := by
        simpa [step] using represents
      rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
      have oldMember : sector ∈ sectorCandidates (.one first) :=
        sectorCandidates_mono (by cases first <;> rfl) member
      have active : activeHolds
          (.sector kind exponent (.one first)) tail :=
        ⟨radial, sector, oldMember, sectorHolds⟩
      simpa [previousTail] using
        represents_with_previous_phase (.sector kind exponent (.one first))
          (.sector kind exponent (.two first bit)) matrix history input tail
          after active
  | two first second =>
      simpa [previousTail, step] using
        completeSector_represents_previous
          ⟨Phase.sector kind exponent (.two first second), matrix, history⟩
          kind exponent first second bit input tail rfl represents

/-- Reverse one parser bit while preserving the represented original input.
The third sector bit transports the affine tail through the completed block;
all other cases only weaken the active finite predicate. -/
theorem step_represents_previous
    (state : State) (bit : Bool) (input tail : Gaussian)
    (represents : Represents (step state bit) input tail) :
    Represents state input (previousTail state bit tail) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simpa [previousTail] using
        step_represents_previous_initial matrix history bit input tail
          represents
  | highUnary count =>
      simpa [previousTail] using
        step_represents_previous_highUnary count matrix history bit input tail
          represents
  | lowUnary count =>
      simpa [previousTail] using
        step_represents_previous_lowUnary count matrix history bit input tail
          represents
  | loopUnary count =>
      simpa [previousTail] using
        step_represents_previous_loopUnary count matrix history bit input tail
          represents
  | sector kind exponent bits =>
      exact step_represents_previous_sector kind exponent bits matrix history
        bit input tail represents

/-- Forward one bit once its post-state predicate has been established. -/
theorem step_represents_next
    (state : State) (bit : Bool) (input tail : Gaussian)
    (before : Represents state input (previousTail state bit tail))
    (afterHolds : (step state bit).Holds tail) :
    Represents (step state bit) input tail := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial | highUnary | lowUnary | loopUnary =>
      simp only [previousTail] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> simpa [step] using before.1
      · cases bit <;> simpa [step] using before.2.1
  | sector kind exponent bits =>
      cases bits with
      | zero | one =>
          simp only [previousTail] at before
          refine ⟨?_, ?_, afterHolds⟩
          · cases bit <;> simpa [step] using before.1
          · cases bit <;> simpa [step] using before.2.1
      | two first second =>
          let sector := sectorOfBits first second bit
          let block := blockMatrix kind exponent sector
          have newest : (Constraint.mk block kind exponent sector).Holds tail := by
            apply afterHolds.1
            change Constraint.mk block kind exponent sector ∈
              Constraint.mk block kind exponent sector ::
                history.map (fun item => item.precompose block)
            exact List.mem_cons_self
          have blockDenominator : denominator block tail ≠ 0 := newest.1
          have productDenominator :
              denominator (CCL.Mat2.mul matrix block) tail ≠ 0 :=
            (denominator_mul_ne_iff matrix block tail blockDenominator).2
              before.1
          refine ⟨?_, ?_, afterHolds⟩
          · simpa [step, completeSector, sector, block] using productDenominator
          · calc
              input = homographic matrix (homographic block tail) := before.2.1
              _ = homographic (CCL.Mat2.mul matrix block) tail :=
                (homographic_mul matrix block tail blockDenominator
                  before.1).symm
              _ = homographic
                  (step ⟨Phase.sector kind exponent (.two first second),
                    matrix, history⟩ bit).matrix tail := by
                simp [step, completeSector, sector, block]

/-- Forward completion of a semantically valid block. -/
theorem completeSector_represents_next
    (state : State) (kind : BlockKind) (exponent : Nat)
    (first second third : Bool) (input before tail : Gaussian)
    (phase : state.phase = .sector kind exponent (.two first second))
    (beforeRepresents : Represents state input before)
    (beforeEq : homographic
      (blockMatrix kind exponent (sectorOfBits first second third)) tail =
        before)
    (blockDenominator : denominator
      (blockMatrix kind exponent (sectorOfBits first second third)) tail ≠ 0)
    (fullBlock : fullBlockHolds kind exponent
      (sectorOfBits first second third) before)
    (loopActive : activeHolds (.loopUnary 0) tail) :
    Represents (completeSector state kind exponent first second third)
      input tail := by
  let sector := sectorOfBits first second third
  let block := blockMatrix kind exponent sector
  have afterHolds :
      (completeSector state kind exponent first second third).Holds tail := by
    constructor
    · intro constraint member
      change constraint ∈
        (Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block) at member
      rcases List.mem_cons.mp member with newest | older
      · subst constraint
        refine ⟨blockDenominator, ?_⟩
        rw [beforeEq]
        exact fullBlock
      · rcases QuotientFreeList.mem_map.mp older with ⟨old, oldMember, rfl⟩
        apply (constraint_precompose_iff old block tail blockDenominator).2
        rw [beforeEq]
        exact beforeRepresents.2.2.1 old oldMember
    · exact loopActive
  rw [← step_eq_completeSector state kind exponent first second third phase]
  apply step_represents_next state third input tail
  · simpa [previousTail, phase, sector, block, beforeEq] using beforeRepresents
  · simpa [step_eq_completeSector state kind exponent first second third phase]
      using afterHolds

/-- A raw word is represented when its parsed state has a finite affine tail
representing the displayed input. -/
def Represented (word : Word) (input : Gaussian) : Prop :=
  ∃ tail, Represents (parse word) input tail

/-- Removing one final bit preserves representability. -/
theorem represented_drop_last
    {word : Word} {bit : Bool} {input : Gaussian}
    (represented : Represented (word ++ [bit]) input) :
    Represented word input := by
  rcases represented with ⟨tail, represented⟩
  refine ⟨previousTail (parse word) bit tail, ?_⟩
  apply step_represents_previous (parse word) bit input tail
  simpa only [parse_append_singleton] using represented

theorem represented_nil (input : Gaussian) : Represented [] input :=
  ⟨input, initialState_represents input⟩

/-- Every ordinary finite-list prefix of a represented raw word is
represented.  The proof removes the explicit finite suffix from the right. -/
theorem represented_of_prefix
    {shorter word : Word} {input : Gaussian}
    (isPrefix : shorter.IsPrefix word) (represented : Represented word input) :
    Represented shorter input := by
  rcases isPrefix with ⟨suffix, rfl⟩
  have removeReversed : ∀ reversed : Word,
      Represented (shorter ++ reversed.reverse) input →
        Represented shorter input := by
    intro reversed
    induction reversed with
    | nil => simp
    | cons bit remaining inductionHypothesis =>
        intro representedAll
        apply inductionHypothesis
        apply represented_drop_last
          (word := shorter ++ remaining.reverse) (bit := bit)
        simpa only [List.reverse_cons, List.append_assoc] using representedAll
  apply removeReversed suffix.reverse
  simpa only [List.reverse_reverse] using represented

/-- A child bit is semantically possible when its post-state has a finite
affine tail representing the same input. -/
def CanStep (state : State) (input : Gaussian) (bit : Bool) : Prop :=
  ∃ tail, Represents (step state bit) input tail

/-- The two raw child bits are mutually exclusive, including on equality
boundaries assigned by the fixed weak/strict sector convention. -/
theorem not_canStep_false_and_true
    (state : State) (input : Gaussian)
    (determinant : CCL.Chordal.Mat2.det state.matrix ≠ 0) :
    ¬(CanStep state input false ∧ CanStep state input true) := by
  rintro ⟨⟨falseTail, falseRepresents⟩,
    ⟨trueTail, trueRepresents⟩⟩
  have falsePrevious := step_represents_previous state false input falseTail
    falseRepresents
  have truePrevious := step_represents_previous state true input trueTail
    trueRepresents
  have previousEqual := Represents.tail_unique determinant falsePrevious
    truePrevious
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have low := falseRepresents.2.2.2
      have high := trueRepresents.2.2.2
      change normSq falseTail < 2 at low
      change (2 : Coordinate) ^ 1 ≤ normSq falseTail at high
      rw [pow_one] at high
      exact (not_lt_of_ge high) low
  | highUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | lowUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have lower := falseRepresents.2.2.2.1.1
      have upper := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | loopUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge upper) lower
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp only [previousTail] at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            CCL.Sectors.Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix : isWordPrefix [false] falseSector.code = true :=
            (List.mem_filter.mp falseMember).2
          have truePrefix : isWordPrefix [true] falseSector.code = true :=
            (List.mem_filter.mp trueMember).2
          cases falseSector <;> simp_all
      | one first =>
          simp only [previousTail] at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            CCL.Sectors.Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix :
              isWordPrefix [first, false] falseSector.code = true :=
            (List.mem_filter.mp falseMember).2
          have truePrefix :
              isWordPrefix [first, true] falseSector.code = true :=
            (List.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;> simp_all
      | two first second =>
          let falseSector := sectorOfBits first second false
          let trueSector := sectorOfBits first second true
          let falseBlock := blockMatrix kind exponent falseSector
          let trueBlock := blockMatrix kind exponent trueSector
          have falseNewest :
              (Constraint.mk falseBlock kind exponent falseSector).Holds
                falseTail := by
            apply falseRepresents.2.2.1
            change Constraint.mk falseBlock kind exponent falseSector ∈
              Constraint.mk falseBlock kind exponent falseSector ::
                history.map (fun item => item.precompose falseBlock)
            exact List.mem_cons_self
          have trueNewest :
              (Constraint.mk trueBlock kind exponent trueSector).Holds
                trueTail := by
            apply trueRepresents.2.2.1
            change Constraint.mk trueBlock kind exponent trueSector ∈
              Constraint.mk trueBlock kind exponent trueSector ::
                history.map (fun item => item.precompose trueBlock)
            exact List.mem_cons_self
          have falseHolds : falseSector.Holds
              (normalizedValue kind exponent
                (homographic falseBlock falseTail)) := falseNewest.2.2
          have trueHolds : trueSector.Holds
              (normalizedValue kind exponent
                (homographic trueBlock trueTail)) := trueNewest.2.2
          change homographic falseBlock falseTail =
            homographic trueBlock trueTail at previousEqual
          have normalizedEqual := congrArg
            (normalizedValue kind exponent) previousEqual
          rw [normalizedEqual] at falseHolds
          have sectorEqual :=
            CCL.Sectors.Sector.holds_unique falseHolds trueHolds
          cases first <;> cases second <;>
            simp [falseSector, trueSector, sectorOfBits] at sectorEqual

theorem canStep_unique
    {state : State} {input : Gaussian} {left right : Bool}
    (determinant : CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (leftPossible : CanStep state input left)
    (rightPossible : CanStep state input right) : left = right := by
  cases left <;> cases right
  · rfl
  · exact (not_canStep_false_and_true state input determinant
      ⟨leftPossible, rightPossible⟩).elim
  · exact (not_canStep_false_and_true state input determinant
      ⟨rightPossible, leftPossible⟩).elim
  · rfl

/-- Two represented one-bit children of the same prefix carry the same bit. -/
theorem represented_child_unique
    {word : Word} {input : Gaussian} {left right : Bool}
    (leftRepresented : Represented (word ++ [left]) input)
    (rightRepresented : Represented (word ++ [right]) input) :
    left = right := by
  apply canStep_unique (parse_det_ne word)
  · rcases leftRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [parse_append_singleton] using represented⟩
  · rcases rightRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [parse_append_singleton] using represented⟩

end CCL.RawParserSemantics
