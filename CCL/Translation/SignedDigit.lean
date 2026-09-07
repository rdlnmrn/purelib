import CCL.Translation.ProgressiveCCL

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace CCL.FiniteTranslation.SignedDigit

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation

open RFAP.ConstructiveGaussian.Gaussian

inductive Digit where
  | negative
  | zero
  | positive
deriving DecidableEq, Repr

namespace Digit

def value : Digit → Coordinate
  | .negative => -1
  | .zero => 0
  | .positive => 1

end Digit

/-- Signed binary prefix value.  The first list entry has weight `1/2`, the
next `1/4`, and so on. -/
def prefixValue : List Digit → Coordinate
  | [] => 0
  | digit :: remaining =>
      (digit.value + prefixValue remaining) * (1 / 2)

def Bounded (value : Coordinate) : Prop :=
  -1 ≤ value ∧ value ≤ 1

/-- The deterministic encoder uses the negative digit strictly below zero and
the positive digit otherwise.  The unused zero digit creates overlap and
nonunique finite observations without making boundary selection partial. -/
def select (value : Coordinate) : Digit :=
  if value < 0 then .negative else .positive

def residual (digit : Digit) (value : Coordinate) : Coordinate :=
  2 * value - digit.value

theorem select_residual_bounded {value : Coordinate}
    (bounded : Bounded value) : Bounded (residual (select value) value) := by
  unfold select
  split
  · rename_i negative
    change -1 ≤ 2 * value - (-1 : Coordinate) ∧
      2 * value - (-1 : Coordinate) ≤ 1
    have doubledLower : (-2 : Coordinate) ≤ 2 * value := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bounded.1 (by decide : (0 : Coordinate) ≤ 2)
      rw [show (2 : Coordinate) * -1 = -2 by decide] at scaled
      exact scaled
    have doubledUpper : 2 * value ≤ 0 := by
      have nonpositive := le_of_lt negative
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          nonpositive (by decide : (0 : Coordinate) ≤ 2)
      rw [show (2 : Coordinate) * 0 = 0 by decide] at scaled
      exact scaled
    constructor
    · calc
        (-1 : Coordinate) = -2 - (-1) := by decide
        _ ≤ 2 * value - (-1) := sub_le_sub_right doubledLower _
    · calc
        2 * value - (-1 : Coordinate) ≤ 0 - (-1) :=
          sub_le_sub_right doubledUpper _
        _ = 1 := by decide
  · rename_i nonnegative
    change -1 ≤ 2 * value - (1 : Coordinate) ∧
      2 * value - (1 : Coordinate) ≤ 1
    have zeroLe : (0 : Coordinate) ≤ value := le_of_not_gt nonnegative
    have doubledLower : (0 : Coordinate) ≤ 2 * value := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          zeroLe (by decide : (0 : Coordinate) ≤ 2)
      rw [show (2 : Coordinate) * 0 = 0 by decide] at scaled
      exact scaled
    have doubledUpper : 2 * value ≤ 2 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bounded.2 (by decide : (0 : Coordinate) ≤ 2)
      rw [show (2 : Coordinate) * 1 = 2 by decide] at scaled
      exact scaled
    constructor
    · calc
        (-1 : Coordinate) = 0 - 1 := by decide
        _ ≤ 2 * value - 1 := sub_le_sub_right doubledLower _
    · calc
        2 * value - (1 : Coordinate) ≤ 2 - 1 :=
          sub_le_sub_right doubledUpper _
        _ = 1 := by decide

/-- A finite signed-digit encoding with its remaining normalized residual. -/
structure Encoding (value : Coordinate) (depth : Nat) where
  digits : List Digit
  length_eq : digits.length = depth
  finalResidual : Coordinate
  final_bounded : Bounded finalResidual
  reconstruct : value = prefixValue digits +
    finalResidual * (1 / 2 : Coordinate) ^ depth

/-- Structural finite encoder. -/
def encode (value : Coordinate) (bounded : Bounded value) :
    (depth : Nat) → Encoding value depth
  | 0 =>
      { digits := []
        length_eq := rfl
        finalResidual := value
        final_bounded := bounded
        reconstruct := by simp [prefixValue] }
  | depth + 1 =>
      let digit := select value
      let next := residual digit value
      let encoded := encode next (select_residual_bounded bounded) depth
      { digits := digit :: encoded.digits
        length_eq := by simp [encoded.length_eq]
        finalResidual := encoded.finalResidual
        final_bounded := encoded.final_bounded
        reconstruct := by
          have first : value =
              (digit.value + next) * (1 / 2 : Coordinate) := by
            dsimp only [next, residual]
            calc
              value = value * (2 * (1 / 2 : Coordinate)) := by
                rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
                ring1
              _ = (digit.value + (2 * value - digit.value)) *
                  (1 / 2 : Coordinate) := by ring1
          calc
            value = (digit.value + next) * (1 / 2 : Coordinate) := first
            _ = (digit.value +
                  (prefixValue encoded.digits + encoded.finalResidual *
                    (1 / 2 : Coordinate) ^ depth)) * (1 / 2) :=
              congrArg (fun candidate : Coordinate =>
                (digit.value + candidate) * (1 / 2)) encoded.reconstruct
            _ = prefixValue (digit :: encoded.digits) +
                encoded.finalResidual * (1 / 2 : Coordinate) ^ (depth + 1) := by
              simp only [prefixValue, pow_succ]
              ring1 }

/-- The closed normalized cylinder determined by a signed-digit word. -/
def Encoding.Contains {value : Coordinate} {depth : Nat}
    (encoding : Encoding value depth) (candidate : Coordinate) : Prop :=
  prefixValue encoding.digits - (1 / 2 : Coordinate) ^ depth ≤ candidate ∧
    candidate ≤ prefixValue encoding.digits + (1 / 2 : Coordinate) ^ depth

theorem Encoding.contains_value {value : Coordinate} {depth : Nat}
    (encoding : Encoding value depth) : encoding.Contains value := by
  let factor := (1 / 2 : Coordinate) ^ depth
  have factorNonnegative : 0 ≤ factor :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) depth
  have lowerProduct : -factor ≤ encoding.finalResidual * factor := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        encoding.final_bounded.1 factorNonnegative
    calc
      -factor = (-1 : Coordinate) * factor := by ring1
      _ ≤ encoding.finalResidual * factor := scaled
  have upperProduct : encoding.finalResidual * factor ≤ factor := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        encoding.final_bounded.2 factorNonnegative
    calc
      encoding.finalResidual * factor ≤ (1 : Coordinate) * factor := scaled
      _ = factor := by ring1
  change
    prefixValue encoding.digits - factor ≤ value ∧
      value ≤ prefixValue encoding.digits + factor
  exact ⟨by
      calc
        prefixValue encoding.digits - factor ≤
            prefixValue encoding.digits + encoding.finalResidual * factor :=
          calc
            prefixValue encoding.digits - factor =
                -factor + prefixValue encoding.digits := by ring1
            _ ≤ encoding.finalResidual * factor +
                prefixValue encoding.digits :=
              RFAP.ConstructiveFraction.add_le_add_right_direct
                lowerProduct _
            _ = prefixValue encoding.digits +
                encoding.finalResidual * factor := by ring1
        _ = value := encoding.reconstruct.symm,
    by
      calc
        value = prefixValue encoding.digits +
            encoding.finalResidual * factor := encoding.reconstruct
        _ ≤ prefixValue encoding.digits + factor :=
          calc
            prefixValue encoding.digits + encoding.finalResidual * factor =
                encoding.finalResidual * factor +
                  prefixValue encoding.digits := by ring1
            _ ≤ factor + prefixValue encoding.digits :=
              RFAP.ConstructiveFraction.add_le_add_right_direct
                upperProduct _
            _ = prefixValue encoding.digits + factor := by ring1⟩

/-- One complex signed-digit cell with a shared scale and depth. -/
structure Cell where
  scale : Coordinate
  scale_pos : 0 < scale
  depth : Nat
  realDigits : List Digit
  imagDigits : List Digit
  real_length : realDigits.length = depth
  imag_length : imagDigits.length = depth

namespace Cell

def factor (cell : Cell) : Coordinate :=
  (1 / 2 : Coordinate) ^ cell.depth

def tail (cell : Cell) : Coordinate := cell.scale * cell.factor

theorem tail_nonneg (cell : Cell) : 0 ≤ cell.tail :=
  RFAP.ConstructiveFraction.mul_nonneg_direct cell.scale_pos.le
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) cell.depth)

def center (cell : Cell) : Gaussian :=
  ⟨cell.scale * prefixValue cell.realDigits,
    cell.scale * prefixValue cell.imagDigits⟩

def Contains (cell : Cell) (value : Gaussian) : Prop :=
  cell.center.re - cell.tail ≤ value.re ∧
    value.re ≤ cell.center.re + cell.tail ∧
    cell.center.im - cell.tail ≤ value.im ∧
    value.im ≤ cell.center.im + cell.tail

theorem contains_center (cell : Cell) : cell.Contains cell.center :=
  ⟨sub_le_self _ cell.tail_nonneg,
    le_add_of_nonneg_right cell.tail_nonneg,
    sub_le_self _ cell.tail_nonneg,
    le_add_of_nonneg_right cell.tail_nonneg⟩

def Refines (inner outer : Cell) : Prop :=
  ∀ {value : Gaussian}, inner.Contains value → outer.Contains value

theorem refines_refl (cell : Cell) : cell.Refines cell :=
  fun inside => inside

theorem refines_trans {inner middle outer : Cell}
    (innerMiddle : inner.Refines middle)
    (middleOuter : middle.Refines outer) : inner.Refines outer :=
  fun inside => middleOuter (innerMiddle inside)

def precisionSq (cell : Cell) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius (2 * cell.scale ^ 2) cell.depth

theorem precisionSq_nonneg (cell : Cell) : 0 ≤ cell.precisionSq :=
  CCL.FiniteGeometric.quarterRadius_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.sq_nonneg_direct cell.scale)) cell.depth

end Cell

def representation : CCL.FiniteTranslation.FiniteRepresentation where
  Observation := Cell
  Possible cell value := cell.Contains value
  witness cell := cell.center
  witness_possible cell := cell.contains_center
  Refines inner outer := inner.Refines outer
  refines_refl := Cell.refines_refl
  refines_trans := Cell.refines_trans
  possible_persists refines possible := refines possible
  precisionSq cell := cell.precisionSq
  precisionSq_nonneg cell := cell.precisionSq_nonneg
  boundary := .redundant

/-! ## Executable encoding and quantitative geometry -/

theorem encode_digits_prefix (value : Coordinate) (bounded : Bounded value)
    (depth extra : Nat) :
    (encode value bounded depth).digits.IsPrefix
      (encode value bounded (depth + extra)).digits := by
  induction depth generalizing value with
  | zero => exact List.nil_prefix
  | succ depth inductionHypothesis =>
      let digit := select value
      let next := residual digit value
      have nextBounded : Bounded next := select_residual_bounded bounded
      rw [show depth + 1 + extra = (depth + extra) + 1 by omega]
      change (digit :: (encode next nextBounded depth).digits).IsPrefix
        (digit :: (encode next nextBounded (depth + extra)).digits)
      rcases inductionHypothesis next nextBounded with ⟨suffix, identity⟩
      refine ⟨suffix, ?_⟩
      simpa only [List.cons_append] using congrArg (List.cons digit) identity

theorem normalized_bounded {value scale : Coordinate}
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value ∧ value ≤ scale) :
    Bounded (value / scale) := by
  constructor
  · apply (RFAP.ConstructiveFraction.le_div_iff_pos scalePositive).2
    calc
      (-1 : Coordinate) * scale = -scale := by ring1
      _ ≤ value := bounds.1
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).2
    calc
      value ≤ scale := bounds.2
      _ = 1 * scale := by ring1

/-- Encode one displayed Gaussian rational in a shared signed-digit square. -/
def Cell.ofPoint (value : Gaussian) (scale : Coordinate)
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value.re ∧ value.re ≤ scale ∧
      -scale ≤ value.im ∧ value.im ≤ scale)
    (depth : Nat) : Cell :=
  let realEncoding := encode (value.re / scale)
    (normalized_bounded scalePositive ⟨bounds.1, bounds.2.1⟩) depth
  let imagEncoding := encode (value.im / scale)
    (normalized_bounded scalePositive ⟨bounds.2.2.1, bounds.2.2.2⟩) depth
  { scale := scale
    scale_pos := scalePositive
    depth := depth
    realDigits := realEncoding.digits
    imagDigits := imagEncoding.digits
    real_length := realEncoding.length_eq
    imag_length := imagEncoding.length_eq }

theorem Cell.ofPoint_contains (value : Gaussian) (scale : Coordinate)
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value.re ∧ value.re ≤ scale ∧
      -scale ≤ value.im ∧ value.im ≤ scale)
    (depth : Nat) :
    (Cell.ofPoint value scale scalePositive bounds depth).Contains value := by
  let realEncoding := encode (value.re / scale)
    (normalized_bounded scalePositive ⟨bounds.1, bounds.2.1⟩) depth
  let imagEncoding := encode (value.im / scale)
    (normalized_bounded scalePositive ⟨bounds.2.2.1, bounds.2.2.2⟩) depth
  have realInside := realEncoding.contains_value
  have imagInside := imagEncoding.contains_value
  have realLower :=
    (RFAP.ConstructiveFraction.le_div_iff_pos scalePositive).1 realInside.1
  have realUpper :=
    (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).1 realInside.2
  have imagLower :=
    (RFAP.ConstructiveFraction.le_div_iff_pos scalePositive).1 imagInside.1
  have imagUpper :=
    (RFAP.ConstructiveFraction.div_le_iff_pos scalePositive).1 imagInside.2
  change
    scale * prefixValue realEncoding.digits -
          scale * (1 / 2 : Coordinate) ^ depth ≤ value.re ∧
      value.re ≤ scale * prefixValue realEncoding.digits +
          scale * (1 / 2 : Coordinate) ^ depth ∧
      scale * prefixValue imagEncoding.digits -
          scale * (1 / 2 : Coordinate) ^ depth ≤ value.im ∧
      value.im ≤ scale * prefixValue imagEncoding.digits +
          scale * (1 / 2 : Coordinate) ^ depth
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      scale * prefixValue realEncoding.digits -
          scale * (1 / 2 : Coordinate) ^ depth =
        (prefixValue realEncoding.digits -
          (1 / 2 : Coordinate) ^ depth) * scale := by ring1
      _ ≤ value.re := realLower
  · calc
      value.re ≤ (prefixValue realEncoding.digits +
          (1 / 2 : Coordinate) ^ depth) * scale := realUpper
      _ = scale * prefixValue realEncoding.digits +
          scale * (1 / 2 : Coordinate) ^ depth := by ring1
  · calc
      scale * prefixValue imagEncoding.digits -
          scale * (1 / 2 : Coordinate) ^ depth =
        (prefixValue imagEncoding.digits -
          (1 / 2 : Coordinate) ^ depth) * scale := by ring1
      _ ≤ value.im := imagLower
  · calc
      value.im ≤ (prefixValue imagEncoding.digits +
          (1 / 2 : Coordinate) ^ depth) * scale := imagUpper
      _ = scale * prefixValue imagEncoding.digits +
          scale * (1 / 2 : Coordinate) ^ depth := by ring1

private theorem sq_le_sq_of_bounds {value bound : Coordinate}
    (lower : -bound ≤ value) (upper : value ≤ bound) :
    value ^ 2 ≤ bound ^ 2 := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (bound - value) * (bound + value) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct upper)
        (by
          have shifted :=
            RFAP.ConstructiveFraction.add_le_add_right_direct lower bound
          calc
            0 = -bound + bound := by ring1
            _ ≤ value + bound := shifted
            _ = bound + value := by ring1)
    _ = bound ^ 2 - value ^ 2 := by ring1

/-- Any two readings of a signed-digit cell have the explicit squared
distance bound `8 * tail²`. -/
theorem Cell.normSq_sub_le_eight_tailSq {cell : Cell}
    {left right : Gaussian} (leftInside : cell.Contains left)
    (rightInside : cell.Contains right) :
    normSq (left - right) ≤ 8 * cell.tail ^ 2 := by
  have leftRealSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ left.re - cell.center.re :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct leftInside.1 _)
    (by
      calc
        left.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            leftInside.2.1 _
        _ = cell.tail := by ring1)
  have leftImagSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ left.im - cell.center.im :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            leftInside.2.2.1 _)
    (by
      calc
        left.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            leftInside.2.2.2 _
        _ = cell.tail := by ring1)
  have leftBound : normSq (left - cell.center) ≤ 2 * cell.tail ^ 2 := by
    change (left.re - cell.center.re) ^ 2 +
      (left.im - cell.center.im) ^ 2 ≤ _
    exact
      (RFAP.ConstructiveFraction.add_le_add_direct
        leftRealSquare leftImagSquare).trans_eq (by ring1)
  have rightRealSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ right.re - cell.center.re :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct rightInside.1 _)
    (by
      calc
        right.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            rightInside.2.1 _
        _ = cell.tail := by ring1)
  have rightImagSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ right.im - cell.center.im :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            rightInside.2.2.1 _)
    (by
      calc
        right.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct
            rightInside.2.2.2 _
        _ = cell.tail := by ring1)
  have rightForward : normSq (right - cell.center) ≤
      2 * cell.tail ^ 2 := by
    change (right.re - cell.center.re) ^ 2 +
      (right.im - cell.center.im) ^ 2 ≤ _
    exact
      (RFAP.ConstructiveFraction.add_le_add_direct
        rightRealSquare rightImagSquare).trans_eq (by ring1)
  have rightBound : normSq (cell.center - right) ≤
      2 * cell.tail ^ 2 := by
    have identity : cell.center - right = -(right - cell.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [identity, normSq_neg]
    exact rightForward
  calc
    normSq (left - right) ≤
        2 * (normSq (left - cell.center) +
          normSq (cell.center - right)) :=
      normSq_sub_le_via left cell.center right
    _ ≤ 2 * ((2 * cell.tail ^ 2) + (2 * cell.tail ^ 2)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.add_le_add_direct leftBound rightBound)
        (by decide)
    _ = 8 * cell.tail ^ 2 := by ring1

private theorem half_pow_sq (depth : Nat) :
    ((1 / 2 : Coordinate) ^ depth) ^ 2 =
      (1 / 4 : Coordinate) ^ depth := by
  induction depth with
  | zero => decide
  | succ depth inductionHypothesis =>
      rw [pow_succ, pow_succ]
      calc
        (((1 / 2 : Coordinate) ^ depth) * (1 / 2)) ^ 2 =
            (((1 / 2 : Coordinate) ^ depth) ^ 2) * (1 / 2) ^ 2 := by
          ring1
        _ = (1 / 4 : Coordinate) ^ depth * (1 / 2) ^ 2 := by
          rw [inductionHypothesis]
        _ = (1 / 4 : Coordinate) ^ depth * (1 / 4) := by
          rw [show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]

theorem Cell.precisionSq_eq_two_tailSq (cell : Cell) :
    cell.precisionSq = 2 * cell.tail ^ 2 := by
  rw [Cell.precisionSq, CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  unfold Cell.tail Cell.factor
  calc
    2 * cell.scale ^ 2 * (1 / 4 : Coordinate) ^ cell.depth =
        2 * cell.scale ^ 2 *
          (((1 / 2 : Coordinate) ^ cell.depth) ^ 2) := by
      rw [half_pow_sq]
    _ = 2 * (cell.scale * (1 / 2 : Coordinate) ^ cell.depth) ^ 2 := by
      ring1

def Cell.toBall (cell : Cell) : CCL.ArithmeticEnclosures.Ball :=
  { center := cell.center
    radiusSq := 2 * cell.tail ^ 2
    radiusSq_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct cell.tail) }

theorem Cell.toBall_contains {cell : Cell} {value : Gaussian}
    (inside : cell.Contains value) : cell.toBall.Contains value := by
  change (value.re - cell.center.re) ^ 2 +
    (value.im - cell.center.im) ^ 2 ≤ 2 * cell.tail ^ 2
  have realSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ value.re - cell.center.re := sub_le_sub_right inside.1 _)
    (by
      calc
        value.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          sub_le_sub_right inside.2.1 _
        _ = cell.tail := by ring1)
  have imagSquare := sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ value.im - cell.center.im :=
          sub_le_sub_right inside.2.2.1 _)
    (by
      calc
        value.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          sub_le_sub_right inside.2.2.2 _
        _ = cell.tail := by ring1)
  exact
    (RFAP.ConstructiveFraction.add_le_add_direct realSquare imagSquare).trans_eq
      (by ring1)

/-- Forget signed syntax while retaining its exact closed-square enclosure as
a Gaussian-rational ball. -/
def toBall : CCL.FiniteTranslation.ObservationMap representation
    CCL.FiniteTranslation.ballRepresentation where
  map cell := cell.toBall
  covers inside := Cell.toBall_contains inside
  coherent := by
    intro inner outer refines
    refine ⟨inner.center, ?_, ?_⟩
    · exact inner.toBall.contains_center
    · exact Cell.toBall_contains (refines inner.contains_center)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le cell := by
    change 2 * cell.tail ^ 2 ≤ cell.precisionSq + 0
    rw [cell.precisionSq_eq_two_tailSq]
    exact le_of_eq (by ring1)
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 2 }
  costBound _ := 2
  cost_le _ := Nat.le_refl 2

/-! ## Translation from finite fast-Cauchy observations -/

def ambientScale (approximation : Approximation) : Coordinate :=
  approximation.centerBound + 1

theorem ambientScale_pos (approximation : Approximation) :
    0 < ambientScale approximation :=
  add_pos_of_nonneg_of_pos approximation.centerBound_nonneg (by decide)

private theorem centerBound_le_ambientScale_sq
    (approximation : Approximation) :
    approximation.centerBound ≤ ambientScale approximation ^ 2 := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ approximation.centerBound ^ 2 +
        approximation.centerBound + 1 :=
      add_nonneg
        (add_nonneg
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          approximation.centerBound_nonneg) (by decide)
    _ = ambientScale approximation ^ 2 - approximation.centerBound := by
      unfold ambientScale
      ring1

theorem sample_coordinate_bounds (approximation : Approximation)
    (index : Nat) :
    -ambientScale approximation ≤ (approximation.sample index).re ∧
      (approximation.sample index).re ≤ ambientScale approximation ∧
      -ambientScale approximation ≤ (approximation.sample index).im ∧
      (approximation.sample index).im ≤ ambientScale approximation := by
  have normBound := (approximation.sample_bounded index).trans
    (centerBound_le_ambientScale_sq approximation)
  have realSquare : (approximation.sample index).re ^ 2 ≤
      ambientScale approximation ^ 2 := by
    calc
      (approximation.sample index).re ^ 2 ≤
          (approximation.sample index).re ^ 2 +
            (approximation.sample index).im ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ ≤ ambientScale approximation ^ 2 := normBound
  have imagSquare : (approximation.sample index).im ^ 2 ≤
      ambientScale approximation ^ 2 := by
    calc
      (approximation.sample index).im ^ 2 ≤
          (approximation.sample index).re ^ 2 +
            (approximation.sample index).im ^ 2 :=
        le_add_of_nonneg_left
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ ≤ ambientScale approximation ^ 2 := normBound
  have scaleNonnegative := (ambientScale_pos approximation).le
  exact
    ⟨RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
        scaleNonnegative realSquare,
      RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
        scaleNonnegative realSquare,
      RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
        scaleNonnegative imagSquare,
      RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
        scaleNonnegative imagSquare⟩

def requestDepth (approximation : Approximation)
    (request : CCL.FiniteTranslation.Request) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (2 * ambientScale approximation ^ 2) 0 request.targetSq

/-- A random-access approximation request translated into two persistent
redundant signed-digit prefixes. -/
def fromApproximation (approximation : Approximation) :
    CCL.FiniteTranslation.FiniteRealizer
      (CCL.FiniteTranslation.approximationRepresentation approximation)
      representation where
  translate index request := by
    let refined := approximation.refineIndex index request.targetSq
      request.positive
    let depth := requestDepth approximation request
    let output := Cell.ofPoint (approximation.sample refined)
      (ambientScale approximation) (ambientScale_pos approximation)
      (sample_coordinate_bounds approximation refined) depth
    exact
      { source' := refined
        output := output
        source_refines := approximation.refineIndex_ge index
          request.targetSq request.positive
        relates := fun sourceValue targetValue =>
          normSq (targetValue - sourceValue) ≤
            approximation.radiusSq refined + 8 * output.tail ^ 2
        source_to_target := by
          rintro sourceValue ⟨later, order, rfl⟩
          refine ⟨approximation.sample refined,
            Cell.ofPoint_contains _ _ _ _ _, ?_⟩
          have closeForward := approximation.later_close order
          have closeReverse :
              normSq (approximation.sample refined -
                approximation.sample later) ≤ approximation.radiusSq refined := by
            have identity : approximation.sample refined -
                approximation.sample later =
              -(approximation.sample later - approximation.sample refined) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact closeForward
          exact closeReverse.trans
            (le_add_of_nonneg_right
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                (RFAP.ConstructiveFraction.sq_nonneg_direct output.tail)))
        target_to_source := by
          intro targetValue targetPossible
          refine ⟨approximation.sample refined,
            approximation.sample_possible refined, ?_⟩
          have pairBound := Cell.normSq_sub_le_eight_tailSq targetPossible
            (Cell.ofPoint_contains _ _ _ _ _)
          exact pairBound.trans
            (le_add_of_nonneg_left
              (approximation.radiusSq_nonneg refined))
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change CCL.FiniteGeometric.quarterRadius
              (2 * ambientScale approximation ^ 2) depth <
            request.targetSq + 0
          calc
            CCL.FiniteGeometric.quarterRadius
                (2 * ambientScale approximation ^ 2) depth <
                request.targetSq :=
              CCL.FiniteGeometric.firstQuarterBelow_accurate _
                (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                  (RFAP.ConstructiveFraction.sq_nonneg_direct _))
                0 request.targetSq request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 2 * depth
            arithmeticSteps := 2 * depth + 3 }
        costBound := 4 * depth + 4
        cost_le := by
          change 1 + 2 * depth + (2 * depth + 3) ≤ 4 * depth + 4
          omega }

/-- Nat-indexed executable entry point which hides the representation's
definitionally equal observation type from clients. -/
def fromApproximationAt (approximation : Approximation) (index : Nat)
    (request : CCL.FiniteTranslation.Request) :=
  (fromApproximation approximation).translate index request

@[simp] theorem fromApproximationAt_depth (approximation : Approximation)
    (index : Nat) (request : CCL.FiniteTranslation.Request) :
    (fromApproximationAt approximation index request).output.depth =
      requestDepth approximation request := rfl

@[simp] theorem fromApproximationAt_real_length
    (approximation : Approximation) (index : Nat)
    (request : CCL.FiniteTranslation.Request) :
    (fromApproximationAt approximation index request).output.realDigits.length =
      requestDepth approximation request :=
  (fromApproximationAt approximation index request).output.real_length

@[simp] theorem fromApproximationAt_imag_length
    (approximation : Approximation) (index : Nat)
    (request : CCL.FiniteTranslation.Request) :
    (fromApproximationAt approximation index request).output.imagDigits.length =
      requestDepth approximation request :=
  (fromApproximationAt approximation index request).output.imag_length

@[simp] theorem fromApproximationAt_costBound
    (approximation : Approximation) (index : Nat)
    (request : CCL.FiniteTranslation.Request) :
    (fromApproximationAt approximation index request).costBound =
      4 * requestDepth approximation request + 4 := rfl

theorem fromApproximationAt_finite_data (approximation : Approximation)
    (index : Nat) (request : CCL.FiniteTranslation.Request) :
    let result := fromApproximationAt approximation index request
    result.output.depth = requestDepth approximation request ∧
      result.output.realDigits.length = requestDepth approximation request ∧
      result.output.imagDigits.length = requestDepth approximation request ∧
      result.costBound = 4 * requestDepth approximation request + 4 := by
  dsimp only
  exact ⟨fromApproximationAt_depth approximation index request,
    fromApproximationAt_real_length approximation index request,
    fromApproximationAt_imag_length approximation index request,
    fromApproximationAt_costBound approximation index request⟩

theorem fromApproximationAt_precision (approximation : Approximation)
    (index : Nat) (request : CCL.FiniteTranslation.Request) :
    representation.precisionSq
        (fromApproximationAt approximation index request).output <
      request.targetSq := by
  let result := fromApproximationAt approximation index request
  calc
    representation.precisionSq result.output <
        request.targetSq + result.precisionLoss := result.precision
    _ = request.targetSq := by
      change request.targetSq + 0 = request.targetSq
      ring1

theorem fromApproximationAt_toBall_precision (approximation : Approximation)
    (index : Nat) (request : CCL.FiniteTranslation.Request) :
    CCL.FiniteTranslation.ballRepresentation.precisionSq
        (toBall.map
          (fromApproximationAt approximation index request).output) <
      request.targetSq := by
  let output := (fromApproximationAt approximation index request).output
  calc
    CCL.FiniteTranslation.ballRepresentation.precisionSq
        (toBall.map output) ≤
      representation.precisionSq output + toBall.precisionLoss output :=
        toBall.precision_le output
    _ = representation.precisionSq output := by
      change representation.precisionSq output + 0 = _
      ring1
    _ < request.targetSq :=
      fromApproximationAt_precision approximation index request

/-- Concrete syntactic redundancy: two unequal length-two words have exactly
the same rational prefix value. -/
theorem nonunique_prefix_center :
    prefixValue [Digit.positive, Digit.negative] =
      prefixValue [Digit.zero, Digit.positive] := by
  decide

theorem nonunique_prefix_syntax :
    [Digit.positive, Digit.negative] ≠
      [Digit.zero, Digit.positive] := by
  decide

end CCL.FiniteTranslation.SignedDigit
