import CCL.Encoding.RawParser

/-!
# Affine semantics of raw-parser transitions

The raw parser evaluates its retained constraints on the current affine tail,
not directly on the original encoder input.  This module records the algebra
needed to relate those two coordinates.  In particular, homographies compose
in the same order as parser matrices, denominator nonvanishing is transported
exactly, and precomposed historical constraints have their intended meaning.
-/

namespace CCL
namespace RawParserSemantics

open GaussianRat

abbrev QI := GaussianRat

/-- The affine denominator of a decoder matrix at a tail. -/
def denominator (matrix : Mat2 QI) (tail : QI) : QI :=
  matrix.c * tail + matrix.d

/-- The affine numerator of a decoder matrix at a tail. -/
def numerator (matrix : Mat2 QI) (tail : QI) : QI :=
  matrix.a * tail + matrix.b

/-- The lower row of a matrix product evaluates as the expected affine
combination of the right factor's numerator and denominator. -/
theorem denominator_mul_expanded (left right : Mat2 QI) (tail : QI) :
    denominator (Mat2.mul left right) tail =
      left.c * (right.a * tail + right.b) +
        left.d * denominator right tail := by
  ext <;>
    simp only [denominator, Mat2.mul, mul_re, mul_im, add_re, add_im] <;>
    ring

/-- After the right denominator is known nonzero, the product denominator is
the product of the outer affine denominator and the right denominator. -/
theorem denominator_mul (left right : Mat2 QI) (tail : QI)
    (rightDenominator : denominator right tail ≠ 0) :
    denominator (Mat2.mul left right) tail =
      denominator left (RatBox.homographic right tail) *
        denominator right tail := by
  rw [denominator_mul_expanded]
  unfold denominator at rightDenominator ⊢
  unfold RatBox.homographic
  have cancel :
      ((right.a * tail + right.b) * inv (right.c * tail + right.d)) *
          (right.c * tail + right.d) = right.a * tail + right.b := by
    rw [mul_assoc, inv_mul _ rightDenominator, mul_one]
  calc
    left.c * (right.a * tail + right.b) +
          left.d * (right.c * tail + right.d) =
        left.c *
            (((right.a * tail + right.b) * inv (right.c * tail + right.d)) *
              (right.c * tail + right.d)) +
          left.d * (right.c * tail + right.d) := by rw [cancel]
    _ = (left.c *
          ((right.a * tail + right.b) * inv (right.c * tail + right.d)) +
          left.d) * (right.c * tail + right.d) := by ring

/-- The upper row of a matrix product obeys the analogous affine identity. -/
theorem numerator_mul_expanded (left right : Mat2 QI) (tail : QI) :
    numerator (Mat2.mul left right) tail =
      left.a * (right.a * tail + right.b) +
        left.b * denominator right tail := by
  ext <;>
    simp only [numerator, denominator, Mat2.mul, mul_re, mul_im, add_re,
      add_im] <;>
    ring

/-- The product numerator is the outer numerator times the right
denominator. -/
theorem numerator_mul (left right : Mat2 QI) (tail : QI)
    (rightDenominator : denominator right tail ≠ 0) :
    numerator (Mat2.mul left right) tail =
      numerator left (RatBox.homographic right tail) *
        denominator right tail := by
  rw [numerator_mul_expanded]
  unfold denominator at rightDenominator
  unfold numerator denominator
  unfold RatBox.homographic
  have cancel :
      ((right.a * tail + right.b) * inv (right.c * tail + right.d)) *
          (right.c * tail + right.d) = right.a * tail + right.b := by
    rw [mul_assoc, inv_mul _ rightDenominator, mul_one]
  calc
    left.a * (right.a * tail + right.b) +
          left.b * (right.c * tail + right.d) =
        left.a *
            (((right.a * tail + right.b) * inv (right.c * tail + right.d)) *
              (right.c * tail + right.d)) +
          left.b * (right.c * tail + right.d) := by rw [cancel]
    _ = (left.a *
          ((right.a * tail + right.b) * inv (right.c * tail + right.d)) +
          left.b) * (right.c * tail + right.d) := by ring

/-- Exact nonvanishing transport for the lower row of a matrix product. -/
theorem denominator_mul_ne_iff (left right : Mat2 QI) (tail : QI)
    (rightDenominator : denominator right tail ≠ 0) :
    denominator (Mat2.mul left right) tail ≠ 0 ↔
      denominator left (RatBox.homographic right tail) ≠ 0 := by
  rw [denominator_mul left right tail rightDenominator]
  exact mul_ne_zero_iff_right rightDenominator

/-- Affine homographies compose in parser matrix-product order whenever both
displayed denominators are nonzero. -/
theorem homographic_mul (left right : Mat2 QI) (tail : QI)
    (rightDenominator : denominator right tail ≠ 0)
    (leftDenominator :
      denominator left (RatBox.homographic right tail) ≠ 0) :
    RatBox.homographic (Mat2.mul left right) tail =
      RatBox.homographic left (RatBox.homographic right tail) := by
  have productDenominator : denominator (Mat2.mul left right) tail ≠ 0 :=
    (denominator_mul_ne_iff left right tail rightDenominator).mpr
      leftDenominator
  rw [show RatBox.homographic (Mat2.mul left right) tail =
      numerator (Mat2.mul left right) tail *
        inv (denominator (Mat2.mul left right) tail) by rfl]
  rw [numerator_mul left right tail rightDenominator,
    denominator_mul left right tail rightDenominator]
  rw [show RatBox.homographic left (RatBox.homographic right tail) =
      numerator left (RatBox.homographic right tail) *
        inv (denominator left (RatBox.homographic right tail)) by rfl]
  apply mul_right_cancel_of_ne (mul_ne_zero leftDenominator rightDenominator)
  rw [mul_assoc, inv_mul _ (mul_ne_zero leftDenominator rightDenominator),
    mul_one]
  calc
    numerator left (RatBox.homographic right tail) * denominator right tail =
        numerator left (RatBox.homographic right tail) *
          (inv (denominator left (RatBox.homographic right tail)) *
            denominator left (RatBox.homographic right tail)) *
          denominator right tail := by
      rw [inv_mul _ leftDenominator, mul_one]
    _ = numerator left (RatBox.homographic right tail) *
          inv (denominator left (RatBox.homographic right tail)) *
          (denominator left (RatBox.homographic right tail) *
            denominator right tail) := by ring

/-- An invertible decoder homography is injective on affine tails where both
denominators are nonzero. -/
theorem homographic_injective
    (matrix : Mat2 QI) {left right : QI}
    (determinant : matrix.det ≠ 0)
    (leftDenominator : denominator matrix left ≠ 0)
    (rightDenominator : denominator matrix right ≠ 0)
    (images : RatBox.homographic matrix left =
      RatBox.homographic matrix right) :
    left = right := by
  have leftDenominator' : matrix.c * left + matrix.d ≠ 0 :=
    leftDenominator
  have rightDenominator' : matrix.c * right + matrix.d ≠ 0 :=
    rightDenominator
  have cross :
      numerator matrix left * denominator matrix right =
        numerator matrix right * denominator matrix left := by
    rw [show numerator matrix left =
        RatBox.homographic matrix left * denominator matrix left by
      unfold numerator denominator RatBox.homographic
      rw [_root_.mul_assoc, inv_mul _ leftDenominator', mul_one]]
    rw [show numerator matrix right =
        RatBox.homographic matrix right * denominator matrix right by
      unfold numerator denominator RatBox.homographic
      rw [_root_.mul_assoc, inv_mul _ rightDenominator', mul_one]]
    rw [images]
    ring
  have factored : matrix.det * (left + -right) = 0 := by
    calc
      matrix.det * (left + -right) =
          numerator matrix left * denominator matrix right +
            -(numerator matrix right * denominator matrix left) := by
        unfold Mat2.det numerator denominator
        rw [GaussianRat.sub_eq_add_neg]
        ring
      _ = 0 := by rw [cross, add_neg_cancel]
  rcases mul_eq_zero.mp factored with zero | difference
  · exact (determinant zero).elim
  · apply GaussianRat.ext
    · have realPart := congrArg GaussianRat.re difference
      simp only [add_re, neg_re, zero_re] at realPart
      linarith
    · have imaginaryPart := congrArg GaussianRat.im difference
      simp only [add_im, neg_im, zero_im] at imaginaryPart
      linarith

/-- Precomposition of a retained historical constraint is exactly evaluation
of the old constraint at the right-factor homographic image. -/
theorem constraint_precompose_iff
    (constraint : RawParser.Constraint) (block : Mat2 QI) (tail : QI)
    (blockDenominator : denominator block tail ≠ 0) :
    (constraint.precompose block).Holds tail ↔
      constraint.Holds (RatBox.homographic block tail) := by
  constructor
  · rintro ⟨productDenominator, blockHolds⟩
    have oldDenominator :
        denominator constraint.matrix (RatBox.homographic block tail) ≠ 0 :=
      (denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).mp productDenominator
    refine ⟨oldDenominator, ?_⟩
    rw [← homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds
  · rintro ⟨oldDenominator, blockHolds⟩
    have productDenominator :
        denominator (Mat2.mul constraint.matrix block) tail ≠ 0 :=
      (denominator_mul_ne_iff constraint.matrix block tail
        blockDenominator).mpr oldDenominator
    refine ⟨productDenominator, ?_⟩
    change RawParser.fullBlockHolds constraint.kind constraint.exponent
      constraint.sector
        (RatBox.homographic (Mat2.mul constraint.matrix block) tail)
    rw [homographic_mul constraint.matrix block tail blockDenominator
      oldDenominator]
    exact blockHolds

/-- A parser state represents an original affine input through its accumulated
matrix and a current affine tail. -/
def Represents (state : RawParser.State) (input tail : QI) : Prop :=
  denominator state.matrix tail ≠ 0 ∧
    input = RatBox.homographic state.matrix tail ∧
    state.Holds tail

/-- An invertible parser state has at most one affine tail representing a
fixed original input. -/
theorem Represents.tail_unique
    {state : RawParser.State} {input left right : QI}
    (determinant : state.matrix.det ≠ 0)
    (leftRepresents : Represents state input left)
    (rightRepresents : Represents state input right) :
    left = right := by
  apply homographic_injective state.matrix determinant leftRepresents.1
    rightRepresents.1
  exact leftRepresents.2.1.symm.trans rightRepresents.2.1

/-- Before any bit is consumed, the current tail is the original input. -/
theorem initialState_represents (input : QI) :
    Represents RawParser.initialState input input := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hre := congrArg GaussianRat.re h
    norm_num [denominator, RawParser.initialState,
      RawParser.identityMatrix] at hre
  · have inverseOne : inv (1 : QI) = 1 := by
      rw [← inv_eq]
      exact inv_one
    apply GaussianRat.ext <;>
      simp [RatBox.homographic, RawParser.initialState,
        RawParser.identityMatrix, inverseOne]
  · simp [RawParser.State.Holds, RawParser.initialState,
      RawParser.activeHolds]

/-- The sector selected by three raw bits is one of the two rows compatible
with the first two bits. -/
theorem sectorOfBits_mem_two_candidates (first second third : Bool) :
    RawParser.sectorOfBits first second third ∈
      RawParser.sectorCandidates (.two first second) := by
  cases first <;> cases second <;> cases third <;> native_decide

/-- Extending a partial sector code can only shrink its candidate list. -/
theorem sectorCandidates_mono
    {earlier later : RawParser.SectorBits}
    (codePrefix : earlier.word <+: later.word) {sector : Sector}
    (member : sector ∈ RawParser.sectorCandidates later) :
    sector ∈ RawParser.sectorCandidates earlier := by
  rcases List.mem_filter.mp member with ⟨tableMember, laterPrefix⟩
  apply List.mem_filter.mpr
  refine ⟨tableMember, ?_⟩
  simp only [decide_eq_true_eq] at laterPrefix ⊢
  exact codePrefix.trans laterPrefix

/-- Reading the third sector bit moves to a new affine tail.  The newest
constraint recovers the complete old block predicate, while every mapped
historical constraint recovers its old meaning at the block image. -/
theorem completeSector_holds_previous
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool) (tail : QI)
    (phase : state.phase = .sector kind exponent (.two first second))
    (holds :
      (RawParser.completeSector state kind exponent first second third).Holds
        tail) :
    state.Holds
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent
          (RawParser.sectorOfBits first second third)) tail) := by
  let sector := RawParser.sectorOfBits first second third
  let block := RawParser.blockMatrix kind exponent sector
  have newest :
      (RawParser.Constraint.mk block kind exponent sector).Holds tail := by
    apply holds.1
    simp [RawParser.completeSector, sector, block]
  have blockDenominator : denominator block tail ≠ 0 := newest.1
  have full :
      RawParser.fullBlockHolds kind exponent sector
        (RatBox.homographic block tail) := newest.2
  constructor
  · intro constraint member
    have mapped : (constraint.precompose block).Holds tail := by
      apply holds.1
      change constraint.precompose block ∈
        (RawParser.Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block)
      exact List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨constraint, member, rfl⟩)
    exact (constraint_precompose_iff constraint block tail
      blockDenominator).mp mapped
  · rw [phase]
    exact ⟨full.1, sector, sectorOfBits_mem_two_candidates first second third,
      full.2⟩

/-- The complete represented original input is invariant when the third
sector bit changes affine-tail coordinates. -/
theorem completeSector_represents_previous
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool) (input tail : QI)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Represents
      (RawParser.completeSector state kind exponent first second third)
        input tail) :
    Represents state input
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent
          (RawParser.sectorOfBits first second third)) tail) := by
  let sector := RawParser.sectorOfBits first second third
  let block := RawParser.blockMatrix kind exponent sector
  have newest :
      (RawParser.Constraint.mk block kind exponent sector).Holds tail := by
    apply represents.2.2.1
    simp [RawParser.completeSector, sector, block]
  have blockDenominator : denominator block tail ≠ 0 := newest.1
  have productDenominator :
      denominator (Mat2.mul state.matrix block) tail ≠ 0 := by
    simpa [RawParser.completeSector, sector, block] using represents.1
  have oldDenominator :
      denominator state.matrix (RatBox.homographic block tail) ≠ 0 :=
    (denominator_mul_ne_iff state.matrix block tail
      blockDenominator).mp productDenominator
  refine ⟨oldDenominator, ?_, ?_⟩
  · calc
      input = RatBox.homographic (Mat2.mul state.matrix block) tail := by
        simpa [RawParser.completeSector, sector, block] using represents.2.1
      _ = RatBox.homographic state.matrix
          (RatBox.homographic block tail) :=
        homographic_mul state.matrix block tail blockDenominator oldDenominator
  · exact completeSector_holds_previous state kind exponent first second third
      tail phase represents.2.2

theorem step_eq_completeSector
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool)
    (phase : state.phase = .sector kind exponent (.two first second)) :
    RawParser.step state third =
      RawParser.completeSector state kind exponent first second third := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  rfl

/-- The affine tail before a raw bit.  Only the third sector bit completes a
block and therefore changes coordinates. -/
def previousTail (state : RawParser.State) (bit : Bool) (tail : QI) : QI :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      RatBox.homographic
        (RawParser.blockMatrix kind exponent
          (RawParser.sectorOfBits first second bit)) tail
  | _ => tail

private theorem represents_with_previous_phase
    (oldPhase newPhase : RawParser.Phase) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) (input tail : QI)
    (represents : Represents ⟨newPhase, matrix, history⟩ input tail)
    (active : RawParser.activeHolds oldPhase tail) :
    Represents ⟨oldPhase, matrix, history⟩ input tail := by
  exact ⟨represents.1, represents.2.1, represents.2.2.1, active⟩

/-- Reverse one parser bit while preserving the represented original input.
For a completed sector this uses the block homography; in every other phase
the affine tail is unchanged and the newer active predicate implies the older
one. -/
theorem step_represents_previous
    (state : RawParser.State) (bit : Bool) (input tail : QI)
    (represents : Represents (RawParser.step state bit) input tail) :
    Represents state input (previousTail state bit tail) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit with
      | false =>
          have after : Represents
              ⟨RawParser.Phase.lowUnary 0, matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          simpa [previousTail] using
            represents_with_previous_phase .initial (.lowUnary 0) matrix
              history input tail after (by simp [RawParser.activeHolds])
      | true =>
          have after : Represents
              ⟨RawParser.Phase.highUnary 1, matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          simpa [previousTail] using
            represents_with_previous_phase .initial (.highUnary 1) matrix
              history input tail after (by simp [RawParser.activeHolds])
  | highUnary count =>
      cases bit with
      | false =>
          have after : Represents
              ⟨RawParser.Phase.sector .initialHigh count .zero,
                matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          have active : RawParser.activeHolds (.highUnary count) tail :=
            after.2.2.2.1.1
          simpa [previousTail] using
            represents_with_previous_phase (.highUnary count)
              (.sector .initialHigh count .zero) matrix history input tail
              after active
      | true =>
          have after : Represents
              ⟨RawParser.Phase.highUnary (count + 1), matrix, history⟩
                input tail := by
            simpa [RawParser.step] using represents
          have powerLe : (2 : ℚ) ^ count ≤ (2 : ℚ) ^ (count + 1) := by
            rw [pow_succ]
            have positive : 0 ≤ (2 : ℚ) ^ count := by positivity
            nlinarith
          have active : RawParser.activeHolds (.highUnary count) tail :=
            powerLe.trans after.2.2.2
          simpa [previousTail] using
            represents_with_previous_phase (.highUnary count)
              (.highUnary (count + 1)) matrix history input tail after active
  | lowUnary count =>
      cases bit with
      | false =>
          have after : Represents
              ⟨RawParser.Phase.sector .initialLow count .zero,
                matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          cases count with
          | zero =>
              have active : RawParser.activeHolds (.lowUnary 0) tail := by
                simpa [RawParser.activeHolds] using after.2.2.2.1.2
              simpa [previousTail] using
                represents_with_previous_phase (.lowUnary 0)
                  (.sector .initialLow 0 .zero) matrix history input tail
                  after active
          | succ count =>
              have upper := after.2.2.2.1.2
              have active : RawParser.activeHolds (.lowUnary (count + 1)) tail := by
                simp only [RawParser.activeHolds]
                rw [pow_succ] at upper
                nlinarith
              simpa [previousTail] using
                represents_with_previous_phase (.lowUnary (count + 1))
                  (.sector .initialLow (count + 1) .zero) matrix history
                  input tail after active
      | true =>
          have after : Represents
              ⟨RawParser.Phase.lowUnary (count + 1), matrix, history⟩
                input tail := by
            simpa [RawParser.step] using represents
          cases count with
          | zero =>
              have newer := after.2.2.2
              have active : RawParser.activeHolds (.lowUnary 0) tail := by
                simp only [RawParser.activeHolds, pow_zero, _root_.one_mul] at newer ⊢
                nlinarith
              simpa [previousTail] using
                represents_with_previous_phase (.lowUnary 0) (.lowUnary 1)
                  matrix history input tail after active
          | succ count =>
              have newer := after.2.2.2
              have normNonnegative := normSq_nonneg tail
              have active : RawParser.activeHolds (.lowUnary (count + 1)) tail := by
                simp only [RawParser.activeHolds]
                simp only [RawParser.activeHolds] at newer
                rw [pow_succ] at newer
                have powerNonnegative : 0 ≤ (2 : ℚ) ^ count := by positivity
                nlinarith
              simpa [previousTail] using
                represents_with_previous_phase (.lowUnary (count + 1))
                  (.lowUnary (count + 2)) matrix history input tail after active
  | loopUnary count =>
      cases bit with
      | false =>
          have after : Represents
              ⟨RawParser.Phase.sector .loop count .zero,
                matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          have active : RawParser.activeHolds (.loopUnary count) tail :=
            after.2.2.2.1.1
          simpa [previousTail] using
            represents_with_previous_phase (.loopUnary count)
              (.sector .loop count .zero) matrix history input tail after active
      | true =>
          have after : Represents
              ⟨RawParser.Phase.loopUnary (count + 1), matrix, history⟩
                input tail := by
            simpa [RawParser.step] using represents
          have powerLe : (2 : ℚ) ^ count ≤ (2 : ℚ) ^ (count + 1) := by
            rw [pow_succ]
            have positive : 0 ≤ (2 : ℚ) ^ count := by positivity
            nlinarith
          have active : RawParser.activeHolds (.loopUnary count) tail :=
            lt_of_le_of_lt powerLe after.2.2.2
          simpa [previousTail] using
            represents_with_previous_phase (.loopUnary count)
              (.loopUnary (count + 1)) matrix history input tail after active
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          have after : Represents
              ⟨RawParser.Phase.sector kind exponent (.one bit),
                matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
          have oldMember : sector ∈ RawParser.sectorCandidates .zero :=
            sectorCandidates_mono (by simp [RawParser.SectorBits.word]) member
          have active : RawParser.activeHolds
              (.sector kind exponent .zero) tail :=
            ⟨radial, sector, oldMember, sectorHolds⟩
          simpa [previousTail] using
            represents_with_previous_phase (.sector kind exponent .zero)
              (.sector kind exponent (.one bit)) matrix history input tail
              after active
      | one first =>
          have after : Represents
              ⟨RawParser.Phase.sector kind exponent (.two first bit),
                matrix, history⟩ input tail := by
            simpa [RawParser.step] using represents
          rcases after.2.2.2 with ⟨radial, sector, member, sectorHolds⟩
          have oldMember :
              sector ∈ RawParser.sectorCandidates (.one first) :=
            sectorCandidates_mono (by simp [RawParser.SectorBits.word]) member
          have active : RawParser.activeHolds
              (.sector kind exponent (.one first)) tail :=
            ⟨radial, sector, oldMember, sectorHolds⟩
          simpa [previousTail] using
            represents_with_previous_phase (.sector kind exponent (.one first))
              (.sector kind exponent (.two first bit)) matrix history input tail
              after active
      | two first second =>
          simpa [previousTail, RawParser.step] using
            completeSector_represents_previous
              ⟨RawParser.Phase.sector kind exponent (.two first second),
                matrix, history⟩ kind exponent first second bit input tail
              rfl represents

/-- Forward one parser bit once its post-state predicate has been established.
This is the converse coordinate transport used when following an actual
encoder trace. -/
theorem step_represents_next
    (state : RawParser.State) (bit : Bool) (input tail : QI)
    (before : Represents state input (previousTail state bit tail))
    (afterHolds : (RawParser.step state bit).Holds tail) :
    Represents (RawParser.step state bit) input tail := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp only [previousTail] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> simpa [RawParser.step] using before.1
      · cases bit <;> simpa [RawParser.step] using before.2.1
  | highUnary count =>
      simp only [previousTail] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> simpa [RawParser.step] using before.1
      · cases bit <;> simpa [RawParser.step] using before.2.1
  | lowUnary count =>
      simp only [previousTail] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> simpa [RawParser.step] using before.1
      · cases bit <;> simpa [RawParser.step] using before.2.1
  | loopUnary count =>
      simp only [previousTail] at before
      refine ⟨?_, ?_, afterHolds⟩
      · cases bit <;> simpa [RawParser.step] using before.1
      · cases bit <;> simpa [RawParser.step] using before.2.1
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp only [previousTail] at before
          refine ⟨?_, ?_, afterHolds⟩
          · cases bit <;> simpa [RawParser.step] using before.1
          · cases bit <;> simpa [RawParser.step] using before.2.1
      | one first =>
          simp only [previousTail] at before
          refine ⟨?_, ?_, afterHolds⟩
          · cases bit <;> simpa [RawParser.step] using before.1
          · cases bit <;> simpa [RawParser.step] using before.2.1
      | two first second =>
          let sector := RawParser.sectorOfBits first second bit
          let block := RawParser.blockMatrix kind exponent sector
          have newest :
              (RawParser.Constraint.mk block kind exponent sector).Holds tail := by
            apply afterHolds.1
            simp [RawParser.step, RawParser.completeSector, sector, block]
          have blockDenominator : denominator block tail ≠ 0 := newest.1
          have productDenominator :
              denominator (Mat2.mul matrix block) tail ≠ 0 :=
            (denominator_mul_ne_iff matrix block tail blockDenominator).mpr
              before.1
          refine ⟨?_, ?_, afterHolds⟩
          · simpa [RawParser.step, RawParser.completeSector, sector, block] using
              productDenominator
          · calc
              input = RatBox.homographic matrix
                  (RatBox.homographic block tail) := before.2.1
              _ = RatBox.homographic (Mat2.mul matrix block) tail :=
                (homographic_mul matrix block tail blockDenominator
                  before.1).symm
              _ = RatBox.homographic
                  (RawParser.step
                    ⟨RawParser.Phase.sector kind exponent (.two first second),
                      matrix, history⟩ bit).matrix tail := by
                simp [RawParser.step, RawParser.completeSector, sector, block]

/-- Forward completion of a semantically valid nonterminal block. -/
theorem completeSector_represents_next
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool) (input before tail : QI)
    (phase : state.phase = .sector kind exponent (.two first second))
    (beforeRepresents : Represents state input before)
    (beforeEq :
      RatBox.homographic
        (RawParser.blockMatrix kind exponent
          (RawParser.sectorOfBits first second third)) tail = before)
    (blockDenominator :
      denominator
        (RawParser.blockMatrix kind exponent
          (RawParser.sectorOfBits first second third)) tail ≠ 0)
    (fullBlock : RawParser.fullBlockHolds kind exponent
      (RawParser.sectorOfBits first second third) before)
    (loopActive : RawParser.activeHolds (.loopUnary 0) tail) :
    Represents
      (RawParser.completeSector state kind exponent first second third)
      input tail := by
  let sector := RawParser.sectorOfBits first second third
  let block := RawParser.blockMatrix kind exponent sector
  have afterHolds :
      (RawParser.completeSector state kind exponent first second third).Holds
        tail := by
    constructor
    · intro constraint member
      change constraint ∈
        (RawParser.Constraint.mk block kind exponent sector) ::
          state.history.map (fun item => item.precompose block) at member
      rcases List.mem_cons.mp member with newest | older
      · subst constraint
        refine ⟨blockDenominator, ?_⟩
        rw [beforeEq]
        exact fullBlock
      · rcases List.mem_map.mp older with ⟨old, oldMember, rfl⟩
        apply (constraint_precompose_iff old block tail blockDenominator).mpr
        rw [beforeEq]
        exact beforeRepresents.2.2.1 old oldMember
    · exact loopActive
  rw [← step_eq_completeSector state kind exponent first second third phase]
  apply step_represents_next state third input tail
  · simpa [previousTail, phase, sector, block, beforeEq] using beforeRepresents
  · simpa [step_eq_completeSector state kind exponent first second third phase]
      using afterHolds

/-- A bit is semantically possible when the corresponding next parser state
has an affine tail representing the same original input. -/
def CanStep (state : RawParser.State) (input : QI) (bit : Bool) : Prop :=
  ∃ tail, Represents (RawParser.step state bit) input tail

/-- The two raw child bits are mutually exclusive for an invertible parser
state.  This includes equality boundaries: the fixed weak/strict convention
and the unique eight-sector row assign them to exactly one child. -/
theorem not_canStep_false_and_true
    (state : RawParser.State) (input : QI)
    (determinant : state.matrix.det ≠ 0) :
    ¬(CanStep state input false ∧ CanStep state input true) := by
  rintro ⟨⟨falseTail, falseRepresents⟩, ⟨trueTail, trueRepresents⟩⟩
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
      change (2 : ℚ) ^ 1 ≤ normSq falseTail at high
      norm_num at high
      linarith
  | highUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      change normSq falseTail < (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) ≤ normSq falseTail at lower
      linarith
  | lowUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have lower := falseRepresents.2.2.2.1.1
      have upper := trueRepresents.2.2.2
      change 1 ≤ (2 : ℚ) ^ count * normSq falseTail at lower
      change (2 : ℚ) ^ count * normSq falseTail < 1 at upper
      linarith
  | loopUnary count =>
      simp only [previousTail] at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      change normSq falseTail ≤ (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) < normSq falseTail at lower
      linarith
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp only [previousTail] at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual := Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix : [false] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp falseMember).2
          have truePrefix : [true] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp trueMember).2
          cases falseSector <;> simp_all
      | one first =>
          simp only [previousTail] at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual := Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix : [first, false] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp falseMember).2
          have truePrefix : [first, true] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;> simp_all
      | two first second =>
          let falseSector := RawParser.sectorOfBits first second false
          let trueSector := RawParser.sectorOfBits first second true
          let falseBlock := RawParser.blockMatrix kind exponent falseSector
          let trueBlock := RawParser.blockMatrix kind exponent trueSector
          have falseNewest :
              (RawParser.Constraint.mk falseBlock kind exponent falseSector).Holds
                falseTail := by
            apply falseRepresents.2.2.1
            simp [RawParser.step, RawParser.completeSector, falseSector,
              falseBlock]
          have trueNewest :
              (RawParser.Constraint.mk trueBlock kind exponent trueSector).Holds
                trueTail := by
            apply trueRepresents.2.2.1
            simp [RawParser.step, RawParser.completeSector, trueSector,
              trueBlock]
          have falseHolds : falseSector.Holds
              (RawParser.normalizedValue kind exponent
                (RatBox.homographic falseBlock falseTail)) := falseNewest.2.2
          have trueHolds : trueSector.Holds
              (RawParser.normalizedValue kind exponent
                (RatBox.homographic trueBlock trueTail)) := trueNewest.2.2
          change RatBox.homographic falseBlock falseTail =
            RatBox.homographic trueBlock trueTail at previousEqual
          have normalizedEqual := congrArg
            (RawParser.normalizedValue kind exponent) previousEqual
          rw [normalizedEqual] at falseHolds
          have sectorEqual := Sector.holds_unique falseHolds trueHolds
          cases first <;> cases second <;>
            simp [falseSector, trueSector, RawParser.sectorOfBits] at sectorEqual

/-- Consequently, any two semantically possible next bits are equal. -/
theorem canStep_unique
    {state : RawParser.State} {input : QI} {left right : Bool}
    (determinant : state.matrix.det ≠ 0)
    (leftPossible : CanStep state input left)
    (rightPossible : CanStep state input right) :
    left = right := by
  cases left <;> cases right
  · rfl
  · exact (not_canStep_false_and_true state input determinant
      ⟨leftPossible, rightPossible⟩).elim
  · exact (not_canStep_false_and_true state input determinant
      ⟨rightPossible, leftPossible⟩).elim
  · rfl

/-- A finite raw word is affinely represented when its parsed state has a
current tail representing the displayed original input.  Terminal completed
words are deliberately excluded: their continuation coordinate is `ω`, not
an affine Gaussian rational. -/
def Represented (word : Prefix.Word) (input : QI) : Prop :=
  ∃ tail, Represents (RawParser.parse word) input tail

/-- Removing the final bit from a represented word preserves
representability, with the previous affine tail reconstructed by
`step_represents_previous`. -/
theorem represented_drop_last
    {word : Prefix.Word} {bit : Bool} {input : QI}
    (represented : Represented (word ++ [bit]) input) :
    Represented word input := by
  rcases represented with ⟨tail, represented⟩
  refine ⟨previousTail (RawParser.parse word) bit tail, ?_⟩
  apply step_represents_previous (RawParser.parse word) bit input tail
  simpa [RawParser.parse, List.foldl_append] using represented

/-- Every ordinary list prefix of a represented raw word is represented. -/
theorem represented_of_prefix
    {shorter word : Prefix.Word} {input : QI}
    (isPrefix : shorter <+: word) (represented : Represented word input) :
    Represented shorter input := by
  rcases isPrefix with ⟨suffix, rfl⟩
  induction suffix using List.reverseRecOn with
  | nil => simpa using represented
  | append_singleton suffix bit inductionHypothesis =>
      apply inductionHypothesis
      apply represented_drop_last (word := shorter ++ suffix) (bit := bit)
      simpa [List.append_assoc] using represented

/-- At a fixed represented prefix, two represented one-bit children carry
the same bit. -/
theorem represented_child_unique
    {word : Prefix.Word} {input : QI} {left right : Bool}
    (leftRepresented : Represented (word ++ [left]) input)
    (rightRepresented : Represented (word ++ [right]) input) :
    left = right := by
  apply canStep_unique (RawParser.parse_det_ne word)
  · rcases leftRepresented with ⟨tail, represented⟩
    exact ⟨tail, by
      simpa [RawParser.parse, List.foldl_append] using represented⟩
  · rcases rightRepresented with ⟨tail, represented⟩
    exact ⟨tail, by
      simpa [RawParser.parse, List.foldl_append] using represented⟩

/-- Determinism at every finite depth: two affinely represented words for the
same input and of the same length are identical. -/
theorem represented_eq_of_length_eq
    {left right : Prefix.Word} {input : QI}
    (length : left.length = right.length)
    (leftRepresented : Represented left input)
    (rightRepresented : Represented right input) :
    left = right := by
  induction left using List.reverseRecOn generalizing right with
  | nil =>
      have rightNil : right = [] := by simpa using length.symm
      subst right
      rfl
  | append_singleton left leftBit inductionHypothesis =>
      induction right using List.reverseRecOn with
      | nil => simp at length
      | append_singleton right rightBit =>
          have prefixLength : left.length = right.length := by
            simpa using length
          have leftPrefix : Represented left input :=
            represented_drop_last leftRepresented
          have rightPrefix : Represented right input :=
            represented_drop_last rightRepresented
          have prefixEqual := inductionHypothesis prefixLength leftPrefix
            rightPrefix
          subst right
          have bitEqual := represented_child_unique leftRepresented
            rightRepresented
          rw [bitEqual]

end RawParserSemantics
end CCL
