import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.TransducerGrammar
import CCL.Progressive.TransducerSemantics

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace CCL.ProgressiveMachineSemantics

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Mode := CCL.ProgressiveTransducer.Mode
abbrev Machine := CCL.ProgressiveTransducer.Machine

open RFAP.ConstructiveGaussian.Gaussian
open CCL.ProgressiveTransducer
open CCL.ProgressiveTransducerGrammar
open CCL.ProgressiveCharts

/-! ## Matrix effect of complete controller chunks -/

def regularBlockKind : RegularKind →
    CCL.RawParser.BlockKind
  | .initialHigh => .initialHigh
  | .loop => .loop

private theorem fold_initial_high_matrix
    (parser : CCL.RawParser.State)
    (phase : parser.phase = .initial) :
    ([true].foldl CCL.RawParser.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

private theorem fold_initial_low_entry_matrix
    (parser : CCL.RawParser.State)
    (phase : parser.phase = .initial) :
    ([false, true].foldl CCL.RawParser.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

private theorem fold_low_unary_matrix
    (parser : CCL.RawParser.State) (count : Nat)
    (phase : parser.phase = .lowUnary count) :
    ([true].foldl CCL.RawParser.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

private theorem fold_regular_unary_matrix
    (parser : CCL.RawParser.State) (kind : RegularKind)
    (count : Nat)
    (phase : parser.phase = regularRawPhase kind count) :
    ([true].foldl CCL.RawParser.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      cases kind <;> simp only [regularRawPhase] at phase <;>
        subst parserPhase <;> rfl

private theorem fold_residual_unary_matrix
    (parser : CCL.RawParser.State) (count : Nat)
    (phase : parser.phase = .loopUnary count) :
    ([true].foldl CCL.RawParser.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      rfl

private theorem fold_initial_low_sector_matrix
    (parser : CCL.RawParser.State)
    (phase : parser.phase = .initial)
    (sector : CCL.Sectors.Sector) :
    ((false :: false :: sector.code).foldl
      CCL.RawParser.step parser).matrix =
        CCL.Mat2.mul parser.matrix
          (CCL.RawParser.blockMatrix .initialLow 0 sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      cases sector <;> rfl

private theorem fold_low_sector_matrix
    (parser : CCL.RawParser.State) (count : Nat)
    (phase : parser.phase = .lowUnary count)
    (sector : CCL.Sectors.Sector) :
    ((false :: sector.code).foldl CCL.RawParser.step parser).matrix =
      CCL.Mat2.mul parser.matrix
        (CCL.RawParser.blockMatrix .initialLow count sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      simp only at phase
      subst parserPhase
      cases sector <;> rfl

private theorem fold_regular_sector_matrix
    (parser : CCL.RawParser.State) (kind : RegularKind)
    (count : Nat) (phase : parser.phase = regularRawPhase kind count)
    (sector : CCL.Sectors.Sector) :
    ((false :: sector.code).foldl CCL.RawParser.step parser).matrix =
      CCL.Mat2.mul parser.matrix
        (CCL.RawParser.blockMatrix
          (regularBlockKind kind) count sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      cases kind <;> simp only [regularRawPhase] at phase <;>
        subst parserPhase <;> cases sector <;> rfl

namespace SemanticMode

/-- Candidate predicate of the finite process state carried by a controller
mode. -/
def possible : (mode : Mode) → Gaussian → Prop
  | .initial current => current.process.Possible current.state
  | .low current => current.process.Possible current.state
  | .loop current => current.process.Possible current.state
  | .residual current => current.process.Possible current.state

/-- Affine tail before the unfinished initial/high/low/loop block, or the
homogeneous inverse tail after a completed sector.  The powers undo only the
normalization represented by the current unary counter; the parser matrix is
unchanged until a sector code is complete. -/
def parserTail : (mode : Mode) → Gaussian → Proj
  | .initial _current, value => CCL.Proj.affine value
  | .low current, value =>
      CCL.Proj.affine ((natPow gamma current.count)⁻¹ * value)
  | .loop current, value =>
      CCL.Proj.affine (natPow gamma current.count * value)
  | .residual _current, value => ⟨1, gamma * value⟩

theorem parserTail_valid (mode : Mode) (value : Gaussian) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      (parserTail mode value) := by
  cases mode with
  | initial current | low current | loop current =>
      exact CCL.Chordal.Proj.affine_hasNonzeroCoordinate _
  | residual current =>
      change (1 : Gaussian) ≠ 0 ∨ gamma * value ≠ 0
      exact Or.inl (by decide)

end SemanticMode

/-! ## Unary normalization identities -/

private theorem gamma_ne : gamma ≠ 0 := by decide

theorem regularUnary_value (count : Nat) (value : Gaussian) :
    natPow gamma (count + 1) * (gamma⁻¹ * value) =
      natPow gamma count * value := by
  have cancellation : gamma * gamma⁻¹ = 1 :=
    RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel gamma gamma_ne
  rw [natPow_succ]
  calc
    natPow gamma count * gamma * (gamma⁻¹ * value) =
        natPow gamma count * (gamma * gamma⁻¹) * value := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im] <;> ring1
    _ = natPow gamma count * value := by
      rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem lowUnary_value (count : Nat) (value : Gaussian) :
    (natPow gamma (count + 1))⁻¹ * (gamma * value) =
      (natPow gamma count)⁻¹ * value := by
  let power := natPow gamma count
  let nextPower := natPow gamma (count + 1)
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne count
  have nextPowerNonzero : nextPower ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne (count + 1)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    nextPowerNonzero
  have nextIdentity : nextPower = power * gamma := by
    simp only [nextPower, power, natPow_succ]
  have nextCancellation : nextPower⁻¹ * nextPower = 1 :=
    RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
      nextPower nextPowerNonzero
  have powerCancellation : power⁻¹ * power = 1 :=
    RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel power powerNonzero
  calc
    (nextPower⁻¹ * (gamma * value)) * nextPower = gamma * value := by
      rw [show nextPower⁻¹ * (gamma * value) * nextPower =
          (nextPower⁻¹ * nextPower) * (gamma * value) by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [mul_re, mul_im] <;> ring1,
        nextCancellation, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = (power⁻¹ * value) * nextPower := by
      rw [nextIdentity]
      calc
        gamma * value = value * gamma :=
          RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
        _ = (power⁻¹ * power) * (value * gamma) := by
          rw [powerCancellation,
            RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = (power⁻¹ * value) * (power * gamma) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;> ring1

theorem regularNormalized_scaled (kind : RegularKind)
    (count : Nat) (value : Gaussian) :
    CCL.RawParser.normalizedValue (regularBlockKind kind) count
        (natPow gamma count * value) = value := by
  cases kind <;>
    simp only [CCL.RawParser.normalizedValue]
  all_goals
    let power := natPow gamma count
    have powerNonzero : power ≠ 0 :=
      natPow_ne_zero_direct gamma gamma_ne count
    have cancellation : power * power⁻¹ = 1 :=
      RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
    calc
      power * value * power⁻¹ = (power * power⁻¹) * value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [mul_re, mul_im] <;> ring1
      _ = value := by
        rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.one_mul]

private theorem lowNormalized_unscaled (count : Nat) (value : Gaussian) :
    CCL.RawParser.normalizedValue .initialLow count
        ((natPow gamma count)⁻¹ * value) = value := by
  let power := natPow gamma count
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne count
  have cancellation : power * power⁻¹ = 1 :=
    RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
  simp only [CCL.RawParser.normalizedValue]
  calc
    power * (power⁻¹ * value) = (power * power⁻¹) * value :=
      (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
    _ = value := by
      rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.one_mul]

theorem loop_candidate_norm_lower (current : LoopState)
    (state : current.process.State) {value : Gaussian}
    (possible : current.process.Possible state value) :
    1 ≤ normSq value := by
  have coefficientAboveOne :
      1 < (current.domain.weight + 1) / current.domain.weight := by
    apply (RFAP.ConstructiveFraction.lt_div_iff_pos
      current.domain.weightPositive).2
    calc
      1 * current.domain.weight = current.domain.weight := by ring1
      _ < current.domain.weight + 1 := by
        calc
          current.domain.weight = 0 + current.domain.weight := by ring1
          _ < 1 + current.domain.weight :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct
              (by decide) current.domain.weight
          _ = current.domain.weight + 1 := add_comm _ _
  exact (coefficientAboveOne.trans current.domain.coefficient_lt).le.trans
    (current.domain.lower state possible)

/-- The normalized affine inverse chart carried after an apart decision is
projectively the same tail as the preceding homogeneous residual chart. -/
theorem normalizedInverse_tail_equivalent
    (residualProcess : Process) (base : residualProcess.State)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (residualProcess.ball base)) (count : Nat)
    {state : (normalizedInverseProcess residualProcess base certificate
      count).State} {tail : Gaussian}
    (possible : (normalizedInverseProcess residualProcess base certificate
      count).Possible state tail) :
    ∃ residual : Gaussian,
      residualProcess.Possible base residual ∧
      (CCL.Proj.affine (natPow gamma count * tail)).Equivalent
        ⟨1, gamma * residual⟩ := by
  rcases normalizedInverse_candidate_semantics residualProcess base
      certificate count possible with
    ⟨residual, residualPossible, residualNonzero, tailEqual⟩
  refine ⟨residual, residualPossible, ?_⟩
  let power := natPow gamma count
  let product := gamma * residual
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne count
  have productNonzero : product ≠ 0 :=
    mul_ne_zero_direct gamma_ne residualNonzero
  have powerCancellation : power * power⁻¹ = 1 :=
    RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
  have scaledIdentity : power * tail = product⁻¹ := by
    rw [tailEqual]
    change power * (power⁻¹ * product⁻¹) = product⁻¹
    calc
      power * (power⁻¹ * product⁻¹) =
          (power * power⁻¹) * product⁻¹ :=
        (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
      _ = product⁻¹ := by
        rw [powerCancellation,
          RFAP.ConstructiveGaussian.Gaussian.one_mul]
  simp only [CCL.Proj.Equivalent, CCL.Proj.affine]
  rw [scaledIdentity]
  change product⁻¹ * product = 1 * 1
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
    product productNonzero

/-! ## Local and persistent exactness -/

/-- Exact meaning of one whole nonempty controller chunk.  This relation is
local in the finite raw-parser state: every candidate admitted after the
chunk comes from a candidate admitted before it, and the parser action gives
the same projective point. -/
def ExactEmission (mode : Mode) (emission : Emission) : Prop :=
  ∀ (parser : CCL.RawParser.State),
    CCL.Chordal.Mat2.det parser.matrix ≠ 0 →
      parser.phase = modeRawPhase mode →
      ∀ {tail : Gaussian}, SemanticMode.possible emission.next tail →
        ∃ previous : Gaussian,
          SemanticMode.possible mode previous ∧
            (CCL.Mat2.act
              (emission.bits.foldl CCL.RawParser.step parser).matrix
              (SemanticMode.parserTail emission.next tail)).Equivalent
                (CCL.Mat2.act parser.matrix
                  (SemanticMode.parserTail mode previous))

/-- Compose one locally exact chunk with an already exact finite prefix. -/
private theorem extend_exact
    (origin : Process) (originState : origin.State)
    (mode : Mode) (word : List Bool) (emission : Emission)
    (phase : (CCL.RawParser.parse word).phase =
      modeRawPhase mode)
    (before : ∀ {tail : Gaussian}, SemanticMode.possible mode tail →
      ∃ value : Gaussian,
        origin.Possible originState value ∧
          (CCL.Mat2.act (CCL.RawParser.parse word).matrix
            (SemanticMode.parserTail mode tail)).Equivalent
              (CCL.Proj.affine value))
    (chunkExact : ExactEmission mode emission) :
    ∀ {tail : Gaussian}, SemanticMode.possible emission.next tail →
      ∃ value : Gaussian,
        origin.Possible originState value ∧
          (CCL.Mat2.act
            (CCL.RawParser.parse (word ++ emission.bits)).matrix
            (SemanticMode.parserTail emission.next tail)).Equivalent
              (CCL.Proj.affine value) := by
  intro tail possible
  rcases chunkExact (CCL.RawParser.parse word)
      (CCL.RawParser.parse_det_ne word) phase possible with
    ⟨previous, previousPossible, localExact⟩
  rcases before previousPossible with ⟨value, valuePossible, beforeExact⟩
  refine ⟨value, valuePossible, ?_⟩
  rw [CCL.RawParser.parse_append]
  exact CCL.Chordal.Proj.equivalent_trans
    localExact beforeExact
    (CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      (CCL.RawParser.parse_det_ne word)
      (SemanticMode.parserTail_valid mode previous))
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate value)

/-! ## Exact controller transitions -/

/-- Every ordinary normalized-loop decision is exact, including a completed
safe sector whose residual may be exactly zero. -/
theorem loopStep_exact (current : LoopState) :
    ExactEmission (.loop current) (loopStep current) := by
  unfold ExactEmission
  intro parser _determinant phase
  unfold loopStep
  split
  · intro tail possible
    simp only [SemanticMode.possible] at possible
    rcases unaryScaled_candidate_semantics current.process
        (current.domain.refinedState current.state) possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [fold_regular_unary_matrix parser current.kind current.count phase]
    simp only [SemanticMode.parserTail]
    rw [tailEqual, regularUnary_value]
    exact CCL.Proj.Equivalent.refl _
  · rename_i sector certificate decisionEqual
    intro residual possible
    simp only [SemanticMode.possible] at possible
    rcases possible with
      ⟨sourceValue, sourcePossible, residualEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    let rawValue := natPow gamma current.count * sourceValue
    have normalizedIdentity :
        CCL.RawParser.normalizedValue
          (regularBlockKind current.kind) current.count rawValue =
            sourceValue :=
      regularNormalized_scaled current.kind current.count sourceValue
    have blockExact :=
      CCL.ProgressiveTransducerSemantics.blockHomogeneous_exact
        (regularBlockKind current.kind) current.count sector rawValue
    rw [fold_regular_sector_matrix parser current.kind current.count phase
      sector, CCL.Mat2.act_mul]
    apply CCL.Mat2.act_respects_equivalent
    simp only [SemanticMode.parserTail]
    rw [residualEqual]
    rw [normalizedIdentity] at blockExact
    exact blockExact

/-- When the live normalized-loop controller selects a sector, its actual
post-emission homogeneous residual candidates satisfy the redundant
half-contraction estimate.  Unary transitions are deliberately absent from
this count: they change only the exponent of the next ordinary block. -/
theorem loopStep_sector_pair_contraction
    (current : LoopState) (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state)))
    (_selected : current.domain.decide current.state =
      .sector sector certificate)
    {leftResidual rightResidual : Gaussian}
    (leftPossible :
      (residualProcess current.process
        (current.domain.refinedState current.state) sector).Possible
          (residualInitial current.process
            (current.domain.refinedState current.state) sector) leftResidual)
    (rightPossible :
      (residualProcess current.process
        (current.domain.refinedState current.state) sector).Possible
          (residualInitial current.process
            (current.domain.refinedState current.state) sector) rightResidual) :
    let leftTail : Proj := ⟨1, gamma * leftResidual⟩
    let rightTail : Proj := ⟨1, gamma * rightResidual⟩
    CCL.Chordal.chordalSq
        (CCL.Mat2.act
          (CCL.RawParser.blockMatrix
            (regularBlockKind current.kind) current.count sector)
          leftTail)
        (CCL.Mat2.act
          (CCL.RawParser.blockMatrix
            (regularBlockKind current.kind) current.count sector)
          rightTail) ≤
      (1 / 2 : Coordinate) *
        CCL.Chordal.chordalSq leftTail rightTail := by
  dsimp only
  rcases leftPossible with
    ⟨leftSource, leftSourcePossible, leftResidualEqual⟩
  rcases rightPossible with
    ⟨rightSource, rightSourcePossible, rightResidualEqual⟩
  let leftRaw := natPow gamma current.count * leftSource
  let rightRaw := natPow gamma current.count * rightSource
  have leftNormalized :
      CCL.RawParser.normalizedValue
          (regularBlockKind current.kind) current.count leftRaw =
        leftSource :=
    regularNormalized_scaled current.kind current.count leftSource
  have rightNormalized :
      CCL.RawParser.normalizedValue
          (regularBlockKind current.kind) current.count rightRaw =
        rightSource :=
    regularNormalized_scaled current.kind current.count rightSource
  have leftNorm : 1 ≤ normSq leftSource :=
    loop_candidate_norm_lower current
      (current.domain.refinedState current.state) leftSourcePossible
  have rightNorm : 1 ≤ normSq rightSource :=
    loop_candidate_norm_lower current
      (current.domain.refinedState current.state) rightSourcePossible
  have leftSafe : CCL.RedundantSectors.Safe sector leftSource :=
    CCL.RedundantOutput.safe_of_contains certificate
      (current.process.possible_inside leftSourcePossible)
  have rightSafe : CCL.RedundantSectors.Safe sector rightSource :=
    CCL.RedundantOutput.safe_of_contains certificate
      (current.process.possible_inside rightSourcePossible)
  have leftRawNorm :
      1 ≤ normSq (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count leftRaw) := by
    rw [leftNormalized]
    exact leftNorm
  have rightRawNorm :
      1 ≤ normSq (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count rightRaw) := by
    rw [rightNormalized]
    exact rightNorm
  have leftRawSafe : CCL.RedundantSectors.Safe sector
      (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count leftRaw) := by
    rw [leftNormalized]
    exact leftSafe
  have rightRawSafe : CCL.RedundantSectors.Safe sector
      (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count rightRaw) := by
    rw [rightNormalized]
    exact rightSafe
  have contraction :=
    CCL.ProgressiveTransducerSemantics.safeBlockHomogeneous_pair_contraction
        (regularBlockKind current.kind) current.count sector
        leftRaw rightRaw leftRawNorm rightRawNorm leftRawSafe rightRawSafe
  rw [leftNormalized, rightNormalized] at contraction
  rw [leftResidualEqual, rightResidualEqual]
  exact contraction

/-- The total initial chart selection is exact in all three outcomes: high
unary, direct sector, and entry into the low unary chart. -/
theorem initialStep_exact (current : InitialState) :
    ExactEmission (.initial current) (step (.initial current)) := by
  change ExactEmission (.initial current) (initialStep current)
  generalize hStep : initialStep current = emission
  unfold ExactEmission
  intro parser _determinant phase tail possible
  unfold initialStep at hStep
  simp only at hStep
  split at hStep
  · split at hStep
    · cases hStep
      simp only [SemanticMode.possible] at possible
      rcases unaryScaled_candidate_semantics current.process
          (initialRefinedState current.process current.state) possible with
        ⟨sourceValue, sourcePossible, tailEqual⟩
      have previousPossible :
          current.process.Possible current.state sourceValue :=
        current.process.refine_persists current.state _ _ sourcePossible
      refine ⟨sourceValue, previousPossible, ?_⟩
      rw [fold_initial_high_matrix parser phase]
      simp only [SemanticMode.parserTail]
      rw [tailEqual, regularUnary_value]
      simp only [natPow_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]
      exact CCL.Proj.Equivalent.refl _
    · rename_i sector certificate decisionEqual
      cases hStep
      simp only [SemanticMode.possible] at possible
      rcases possible with
        ⟨sourceValue, sourcePossible, residualEqual⟩
      have previousPossible :
          current.process.Possible current.state sourceValue :=
        current.process.refine_persists current.state _ _ sourcePossible
      refine ⟨sourceValue, previousPossible, ?_⟩
      have blockExact :=
        CCL.ProgressiveTransducerSemantics.blockHomogeneous_exact
          CCL.RawParser.BlockKind.initialLow 0 sector sourceValue
      rw [fold_initial_low_sector_matrix parser phase sector,
        CCL.Mat2.act_mul]
      apply CCL.Mat2.act_respects_equivalent
      simp only [SemanticMode.parserTail]
      rw [residualEqual]
      simpa only [CCL.RawParser.normalizedValue, natPow_zero,
        RFAP.ConstructiveGaussian.Gaussian.one_mul] using blockExact
  · cases hStep
    simp only [SemanticMode.possible] at possible
    rcases upscaled_candidate_semantics current.process
        (initialRefinedState current.process current.state) 1 possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [fold_initial_low_entry_matrix parser phase]
    simp only [SemanticMode.parserTail]
    rw [tailEqual, nextLowState_count]
    have unaryIdentity := lowUnary_value 0 sourceValue
    simp only [natPow_succ, natPow_zero,
      RFAP.ConstructiveGaussian.Gaussian.one_mul] at unaryIdentity ⊢
    rw [unaryIdentity]
    simp only [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_one_direct,
      RFAP.ConstructiveGaussian.Gaussian.one_mul]
    exact CCL.Proj.Equivalent.refl
      (CCL.Mat2.act parser.matrix (CCL.Proj.affine sourceValue))

/-- Both initial-low outcomes preserve the exact raw-parser coordinate. -/
theorem lowStep_exact (current : LowState) :
    ExactEmission (.low current) (step (.low current)) := by
  change ExactEmission (.low current) (lowStep current)
  generalize hStep : lowStep current = emission
  unfold ExactEmission
  intro parser _determinant phase tail possible
  unfold lowStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    simp only [SemanticMode.possible] at possible
    rcases possible with
      ⟨sourceValue, sourcePossible, residualEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    let rawValue := (natPow gamma current.count)⁻¹ * sourceValue
    have normalizedIdentity :
        CCL.RawParser.normalizedValue .initialLow
          current.count rawValue = sourceValue :=
      lowNormalized_unscaled current.count sourceValue
    have blockExact :=
      CCL.ProgressiveTransducerSemantics.blockHomogeneous_exact
        CCL.RawParser.BlockKind.initialLow current.count
          (CCL.Sectors.Sector.select
            (current.process.ball
              (initialRefinedState current.process current.state)).center)
          rawValue
    rw [fold_low_sector_matrix parser current.count phase
      (CCL.Sectors.Sector.select
        (current.process.ball
          (initialRefinedState current.process current.state)).center),
      CCL.Mat2.act_mul]
    apply CCL.Mat2.act_respects_equivalent
    simp only [SemanticMode.parserTail]
    rw [residualEqual]
    rw [normalizedIdentity] at blockExact
    exact blockExact
  · cases hStep
    simp only [SemanticMode.possible] at possible
    rcases upscaled_candidate_semantics current.process
        (initialRefinedState current.process current.state) 1 possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    rw [fold_low_unary_matrix parser current.count phase]
    simp only [SemanticMode.parserTail]
    rw [tailEqual, nextLowState_count]
    have unaryIdentity := lowUnary_value current.count sourceValue
    simp only [natPow_succ, natPow_zero,
      RFAP.ConstructiveGaussian.Gaussian.one_mul] at unaryIdentity ⊢
    rw [unaryIdentity]
    exact CCL.Proj.Equivalent.refl _

/-- Residual padding is semantically stationary.  Once finite apartness is
visible, the silent change to a normalized affine inverse chart is exactly
the same projective tail, after which `loopStep_exact` applies. -/
theorem residualStep_exact (current : ResidualState) :
    ExactEmission (.residual current) (step (.residual current)) := by
  change ExactEmission (.residual current) (residualStep current)
  generalize hStep : residualStep current = emission
  unfold ExactEmission
  intro parser determinant phase tail possible
  unfold residualStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    simp only [SemanticMode.possible] at possible
    have previousPossible :
        current.process.Possible current.state tail :=
      current.process.refine_persists current.state _ _ possible
    refine ⟨tail, previousPossible, ?_⟩
    rw [fold_residual_unary_matrix parser current.count phase]
    simp only [SemanticMode.parserTail]
    exact CCL.Proj.Equivalent.refl _
  · rename_i certificate decisionEqual
    cases hStep
    simp only [SemanticMode.possible] at possible
    let requestedCount := current.count + 1
    let refined :=
      CCL.ArithmeticController.residualState
        current.process current.state requestedCount
    have upperBoundAtRefined : ∀ {value : Gaussian},
        current.process.Possible refined value →
          normSq value ≤ current.upper := by
      intro value valuePossible
      exact current.upperBound
        (current.process.refine_persists current.state _ _ valuePossible)
    let nextProcess := normalizedInverseProcess current.process refined
      certificate current.count
    let nextState := normalizedInverseInitial current.process refined
      certificate current.count
    let nextDomain := normalizedInverseLoopDomain current.process refined
      certificate current.count current.upper upperBoundAtRefined
      current.upperStrict
    let next : LoopState :=
      { kind := .loop
        count := current.count
        process := nextProcess
        state := nextState
        domain := nextDomain }
    have nextPhase : parser.phase = modeRawPhase (.loop next) := by
      simpa [modeRawPhase, regularRawPhase, next] using phase
    rcases loopStep_exact next parser determinant nextPhase possible with
      ⟨inverseTail, inversePossible, loopExact⟩
    have inversePossible' :
        (normalizedInverseProcess current.process refined certificate
          current.count).Possible
            (normalizedInverseInitial current.process refined certificate
              current.count) inverseTail := by
      exact inversePossible
    rcases normalizedInverse_tail_equivalent current.process refined
        certificate current.count inversePossible' with
      ⟨residual, residualAtRefined, chartEquivalent⟩
    have residualAtCurrent :
        current.process.Possible current.state residual :=
      current.process.refine_persists current.state _ _ residualAtRefined
    refine ⟨residual, residualAtCurrent, ?_⟩
    have chartEquivalent' :
        (SemanticMode.parserTail (.loop next) inverseTail).Equivalent
          (SemanticMode.parserTail (.residual current) residual) := by
      simpa only [SemanticMode.parserTail, next] using chartEquivalent
    have actedChartEquivalent :=
      CCL.Mat2.act_respects_equivalent parser.matrix chartEquivalent'
    exact CCL.Chordal.Proj.equivalent_trans
      loopExact actedChartEquivalent
      (CCL.Chordal.Mat2.act_hasNonzeroCoordinate determinant
        (SemanticMode.parserTail_valid (.loop next) inverseTail))
      (CCL.Chordal.Mat2.act_hasNonzeroCoordinate determinant
        (SemanticMode.parserTail_valid (.residual current) residual))

/-- Every quantitative controller decision preserves the exact projective
meaning of the unchanged raw CCL grammar. -/
theorem step_exact : ∀ mode : Mode, ExactEmission mode (step mode)
  | .initial current => initialStep_exact current
  | .low current => lowStep_exact current
  | .loop current => loopStep_exact current
  | .residual current => residualStep_exact current

/-- A semantic certificate for one buffered machine.  `origin` and
`originState` are finite process data, not a completed value. -/
structure ExactCursor (origin : Process) (originState : origin.State)
    (machine : Machine) : Prop where
  grammar : Machine.GrammarInvariant machine
  exact : ∀ {tail : Gaussian}, SemanticMode.possible machine.mode tail →
    ∃ value : Gaussian,
      origin.Possible originState value ∧
        (CCL.Mat2.act
          (CCL.RawParser.parse
            (CCL.ProgressiveTransducerGrammar.Machine.committed
              machine)).matrix
          (SemanticMode.parserTail machine.mode tail)).Equivalent
            (CCL.Proj.affine value)

/-- The empty cursor is exact: its parser matrix and quantitative chart are
both the identity. -/
theorem ExactCursor.initial (origin : Process) (originState : origin.State) :
    ExactCursor origin originState (Machine.initial origin originState) :=
  { grammar := Machine.initial_invariant origin originState
    exact := by
      intro tail possible
      refine ⟨tail, possible, ?_⟩
      simp [Machine.initial,
        CCL.ProgressiveTransducerGrammar.Machine.committed,
        SemanticMode.parserTail, CCL.RawParser.parse,
        CCL.RawParser.initialState,
        CCL.RawParser.identityMatrix, CCL.Mat2.act,
        CCL.Proj.affine, CCL.Proj.Equivalent] }

/-- Exposing one bit preserves both the raw grammar and exact projective
meaning.  Pending bits merely move across the buffer; an empty buffer invokes
one of the exact whole-chunk transitions above. -/
theorem ExactCursor.nextBit
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine) :
    ExactCursor origin originState
      (CCL.ProgressiveTransducer.nextBit machine).2 := by
  refine
    { grammar := nextBit_invariant machine cursor.grammar
      exact := ?_ }
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil =>
          let emission := step mode
          have phase := cursor.grammar
          change (CCL.RawParser.parse (emitted ++ [])).phase =
            modeRawPhase mode at phase
          rw [List.append_nil] at phase
          have before : ∀ {tail : Gaussian},
              SemanticMode.possible mode tail →
                ∃ value : Gaussian,
                  origin.Possible originState value ∧
                    (CCL.Mat2.act
                      (CCL.RawParser.parse emitted).matrix
                      (SemanticMode.parserTail mode tail)).Equivalent
                        (CCL.Proj.affine value) := by
            intro tail possible
            have result := cursor.exact possible
            change ∃ value : Gaussian,
              origin.Possible originState value ∧
                (CCL.Mat2.act
                  (CCL.RawParser.parse (emitted ++ [])).matrix
                  (SemanticMode.parserTail mode tail)).Equivalent
                    (CCL.Proj.affine value) at result
            rw [List.append_nil] at result
            exact result
          intro tail possible
          have afterPossible :
              SemanticMode.possible emission.next tail := by
            change SemanticMode.possible
              (consumeEmission emitted emission).2.mode tail at possible
            rw [consumeEmission_mode] at possible
            exact possible
          have result := extend_exact origin originState mode emitted
            emission phase before (step_exact mode) afterPossible
          rw [show (CCL.ProgressiveTransducer.nextBit
            ({ mode := mode, emitted := emitted, pending := [] } :
              Machine)).2 =
              (consumeEmission emitted emission).2 by rfl,
            consumeEmission_committed, consumeEmission_mode]
          exact result
      | cons bit rest =>
          intro tail possible
          change SemanticMode.possible mode tail at possible
          have result := cursor.exact possible
          change ∃ value : Gaussian,
            origin.Possible originState value ∧
              (CCL.Mat2.act
                (CCL.RawParser.parse
                  ((emitted ++ [bit]) ++ rest)).matrix
                (SemanticMode.parserTail mode tail)).Equivalent
                  (CCL.Proj.affine value)
          rw [List.append_assoc, List.singleton_append]
          exact result

/-- Any finite requested number of bits preserves the exact cursor. -/
theorem ExactCursor.advance
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine) : ∀ count : Nat,
    ExactCursor origin originState
      (CCL.ProgressiveTransducer.advance machine count)
  | 0 => cursor
  | count + 1 => (cursor.nextBit.advance count)

namespace Named

/-- Every progressive arithmetic name starts with an exact empty raw cursor. -/
theorem machine_exact (name : Named) :
    ExactCursor name.process name.state name.machine :=
  ExactCursor.initial name.process name.state

/-- Every finite prefix requested from a progressive arithmetic name remains
an exact raw CCL prefix for some candidate admitted by the original finite
process state. -/
theorem advance_exact (name : Named) (count : Nat) :
    ExactCursor name.process name.state (advance name.machine count) :=
  (machine_exact name).advance count

/-- Pointwise form of `advance_exact`, convenient for arithmetic clients:
every tail admitted by the quantitative sidecar after a finite request
reconstructs an original process candidate through the pure raw parser. -/
theorem advance_candidate_exact (name : Named) (count : Nat)
    {tail : Gaussian}
    (possible : SemanticMode.possible (advance name.machine count).mode tail) :
    ∃ value : Gaussian,
      name.process.Possible name.state value ∧
        (CCL.Mat2.act
          (CCL.RawParser.parse
            (Machine.committed (advance name.machine count))).matrix
          (SemanticMode.parserTail
            (advance name.machine count).mode tail)).Equivalent
              (CCL.Proj.affine value) :=
  (advance_exact name count).exact possible

end Named

end CCL.ProgressiveMachineSemantics
