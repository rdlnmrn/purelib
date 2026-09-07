import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Normalization
import CCL.Geometry.Projective
import mathlib.RFAP.ConstructiveFraction
import Lean.Elab.Tactic.Omega

/-!
# Constructive one-dimensional baseline algorithms

Executable versions of the real continued-fraction and continued-logarithm
algorithms used for comparison in the CCL manuscript.  Both encoders recurse
on the displayed natural measure and decode in explicit constructive rational
coordinates.
-/

namespace CCL.BaselineAlgorithms

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- Transitivity of finite projective equivalence using the explicit
constructive-rational cancellation theorem, rather than a derived domain
instance. -/
theorem equivalent_trans_of_mid_q {left middle right : CCL.Proj Coordinate}
    (leftMiddle : left.Equivalent middle)
    (middleRight : middle.Equivalent right)
    (middleDenominatorNonzero : middle.q ≠ 0) :
    left.Equivalent right := by
  dsimp only [CCL.Proj.Equivalent] at leftMiddle middleRight ⊢
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    middleDenominatorNonzero
  calc
    (left.p * right.q) * middle.q =
        right.q * (left.p * middle.q) := by ring1
    _ = right.q * (middle.p * left.q) := by rw [leftMiddle]
    _ = left.q * (middle.p * right.q) := by ring1
    _ = left.q * (right.p * middle.q) := by rw [middleRight]
    _ = (right.p * left.q) * middle.q := by ring1

/-- Nonnegative Euclidean remainder, converted to a natural number. -/
def remNat (numerator : Int) (denominator : Nat) : Nat :=
  (numerator % (denominator : Int)).toNat

theorem remNat_lt (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator) :
    remNat numerator denominator < denominator := by
  have denominatorPositive : (0 : Int) < denominator :=
    Int.ofNat_lt.mpr positive
  have remainderNonnegative := Int.emod_nonneg numerator
    (Int.ne_of_gt denominatorPositive)
  have remainderLess := Int.emod_lt_of_pos numerator denominatorPositive
  rw [remNat, Int.toNat_lt remainderNonnegative]
  exact remainderLess

theorem remNat_pos (numerator : Int) {denominator : Nat}
    (positive : 0 < denominator)
    (remainderNonzero : numerator % (denominator : Int) ≠ 0) :
    0 < remNat numerator denominator := by
  have denominatorNonzero : (denominator : Int) ≠ 0 :=
    Int.ne_of_gt (Int.ofNat_lt.mpr positive)
  have remainderNonnegative := Int.emod_nonneg numerator denominatorNonzero
  cases remainderIdentity : numerator % (denominator : Int) with
  | ofNat remainder =>
      rw [remNat, remainderIdentity]
      change 0 < remainder
      have remainderPositive : 0 < remainder := by
        apply Nat.pos_of_ne_zero
        intro remainderZero
        apply remainderNonzero
        rw [remainderIdentity, remainderZero]
        rfl
      exact remainderPositive
  | negSucc remainder =>
      have remainderNegative :
          numerator % (denominator : Int) < 0 := by
        rw [remainderIdentity]
        omega
      exact ((not_lt_of_ge remainderNonnegative) remainderNegative).elim

/-- Fuel-bounded Euclidean recursion for the standard rational
continued-fraction encoder.  A call whose denominator is at most the fuel
cannot exhaust the fuel because every nonterminal remainder is smaller than
the preceding denominator. -/
def cfEncodeFuel : (fuel : Nat) → (numerator : Int) →
    (denominator : Nat) → 0 < denominator → List Int
  | 0, _, _, _ => []
  | fuel + 1, numerator, denominator, positive =>
      let quotient := numerator / (denominator : Int)
      let remainder := numerator % (denominator : Int)
      if remainderZero : remainder = 0 then
        [quotient]
      else
        quotient :: cfEncodeFuel fuel (denominator : Int)
          (remNat numerator denominator)
          (remNat_pos numerator positive remainderZero)

/-- Algorithm 4.1: the standard rational continued-fraction encoder.  The
displayed denominator is also a sufficient recursion budget. -/
def cfEncode (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : List Int :=
  cfEncodeFuel denominator numerator denominator positive

/-- Finite projective decoder for standard partial quotients. -/
def cfDecode : List Int → CCL.Proj Coordinate
  | [] => CCL.Proj.omega
  | quotient :: digits =>
      CCL.Mat2.act (CCL.Mat2.cf (quotient : Coordinate) 1)
        (cfDecode digits)

@[simp] theorem cfDecode_singleton (quotient : Int) :
    cfDecode [quotient] =
      ⟨(quotient : Coordinate), 1⟩ := by
  ext <;>
    simp only [cfDecode, CCL.Mat2.act, CCL.Mat2.cf, CCL.Proj.omega,
      mul_one, mul_zero, add_zero]

private theorem cfEncodeFuel_reconstruct : ∀ (fuel : Nat)
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator),
    denominator ≤ fuel →
      (cfDecode (cfEncodeFuel fuel numerator denominator positive)).Equivalent
        ⟨(numerator : Coordinate), (denominator : Coordinate)⟩
  | 0, numerator, 0, positive, bounded =>
      (Nat.not_lt_zero 0 positive).elim
  | 0, numerator, denominator + 1, positive, bounded =>
      (Nat.not_succ_le_zero denominator bounded).elim
  | fuel + 1, numerator, denominator, positive, bounded => by
      rw [cfEncodeFuel]
      split
      · rename_i remainderZero
        rw [cfDecode_singleton]
        dsimp only [CCL.Proj.Equivalent]
        have divisionIdentity :=
          Int.ediv_mul_cancel_of_emod_eq_zero remainderZero
        have castIdentity := congrArg (fun value : Int =>
          (value : Coordinate)) divisionIdentity
        simpa only [QuotientFreeRing.intCast_mul, Int.cast_natCast, mul_one]
          using castIdentity
      · rename_i remainderNonzero
        let remainder := remNat numerator denominator
        have remainderPositive : 0 < remainder :=
          remNat_pos numerator positive remainderNonzero
        have remainderLess : remainder < denominator :=
          remNat_lt numerator positive
        have remainderBound : remainder ≤ fuel :=
          Nat.lt_succ_iff.mp (remainderLess.trans_le bounded)
        have tail := cfEncodeFuel_reconstruct fuel
          (denominator : Int) remainder remainderPositive remainderBound
        have acted := CCL.Mat2.act_respects_equivalent
          (CCL.Mat2.cf
            ((numerator / (denominator : Int) : Int) : Coordinate) 1)
          tail
        have denominatorNonzero : (denominator : Int) ≠ 0 :=
          Int.ne_of_gt (Int.ofNat_lt.mpr positive)
        have remainderNonnegative :=
          Int.emod_nonneg numerator denominatorNonzero
        have remainderCast : (remainder : Int) =
            numerator % (denominator : Int) := by
          simp only [remainder, remNat,
            Int.toNat_of_nonneg remainderNonnegative]
        have divisionIdentity :=
          Int.ediv_mul_add_emod numerator (denominator : Int)
        have displayedIdentity :
            ((numerator / (denominator : Int) : Int) : Coordinate) *
                (denominator : Coordinate) + (remainder : Coordinate) =
              (numerator : Coordinate) := by
          have castIdentity := congrArg (fun value : Int =>
            (value : Coordinate)) divisionIdentity
          rw [← remainderCast] at castIdentity
          simpa only [Int.cast_add, QuotientFreeRing.intCast_mul, Int.cast_natCast]
            using castIdentity
        have step :
            (CCL.Mat2.act
              (CCL.Mat2.cf
                ((numerator / (denominator : Int) : Int) : Coordinate) 1)
              (⟨(denominator : Coordinate),
                (remainder : Coordinate)⟩ : CCL.Proj Coordinate)).Equivalent
              ⟨(numerator : Coordinate),
                (denominator : Coordinate)⟩ := by
          dsimp only [CCL.Proj.Equivalent, CCL.Mat2.act, CCL.Mat2.cf]
          simp only [one_mul, zero_mul, add_zero]
          rw [displayedIdentity]
        exact equivalent_trans_of_mid_q acted step
          (by
            simpa only [CCL.Mat2.act, CCL.Mat2.cf, one_mul, zero_mul,
              add_zero, Int.cast_natCast] using
              (ne_of_gt (RFAP.ConstructiveFraction.natCast_pos_direct
                positive)))

/-- Proposition 4.1: the executable finite continued fraction reconstructs
its displayed rational input. -/
theorem cfEncode_reconstruct (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) :
    (cfDecode (cfEncode numerator denominator positive)).Equivalent
      ⟨(numerator : Coordinate), (denominator : Coordinate)⟩ := by
  unfold cfEncode
  exact cfEncodeFuel_reconstruct denominator numerator denominator positive
    (Nat.le_refl denominator)

/-- Certified scale consolidation for the real continued logarithm. -/
structure CLScale (numerator denominator : Nat) where
  exponent : Nat
  lower : 2 ^ exponent * denominator ≤ numerator
  upper : numerator < 2 ^ (exponent + 1) * denominator

/-- Bounded construction of the unique scale putting `p/q` in `[1,2)`. -/
def clScale (numerator denominator : Nat) (positive : 0 < denominator)
    (ordered : denominator ≤ numerator) : CLScale numerator denominator := by
  if highBranch : 2 * denominator ≤ numerator then
    let result := CCL.Normalization.high numerator denominator
      positive highBranch
    exact ⟨result.exponent, result.lower, result.upper⟩
  else
    exact ⟨0, by simpa only [Nat.pow_zero, Nat.one_mul] using ordered,
      by
        change numerator < 2 * denominator
        exact Nat.lt_of_not_ge highBranch⟩

private theorem difference_le_of_lt_two_mul {numerator normalized : Nat}
    (upper : numerator < 2 * normalized) :
    numerator - normalized ≤ normalized :=
  Nat.sub_le_of_le_add (by
    simpa only [two_mul] using Nat.le_of_lt upper)

/-- Fuel-bounded recursion for the real continued-logarithm encoder.  A call
whose numerator is at most the fuel cannot exhaust the fuel because each
nonterminal normalized numerator is strictly smaller. -/
def clEncodeFuel : (fuel : Nat) → (numerator denominator : Nat) →
    0 < denominator → denominator ≤ numerator → List Bool
  | 0, _, _, _, _ => []
  | fuel + 1, numerator, denominator, positive, ordered =>
      if equal : numerator = denominator then
        []
      else
        let scale := clScale numerator denominator positive ordered
        let normalized := 2 ^ scale.exponent * denominator
        if terminal : normalized = numerator then
          List.replicate scale.exponent true
        else
          List.replicate scale.exponent true ++ false ::
            clEncodeFuel fuel normalized (numerator - normalized)
              (Nat.sub_pos_of_lt
                (lt_of_le_of_ne scale.lower terminal))
              (by
                have upper : numerator < 2 * normalized := by
                  calc
                    numerator <
                        2 ^ (scale.exponent + 1) * denominator :=
                      scale.upper
                    _ = 2 * normalized := by
                      simp only [normalized, Nat.pow_succ,
                        Nat.mul_comm, Nat.mul_left_comm]
                exact difference_le_of_lt_two_mul upper)

/-- Algorithm 4.2: the real continued-logarithm encoder.  The displayed
numerator is also a sufficient recursion budget. -/
def clEncode (numerator denominator : Nat) (positive : 0 < denominator)
    (ordered : denominator ≤ numerator) : List Bool :=
  clEncodeFuel numerator numerator denominator positive ordered

/-- Decoder branches for the real continued-logarithm bitstream. -/
def clDecode : List Bool → CCL.Proj Coordinate
  | [] => ⟨1, 1⟩
  | true :: bits =>
      CCL.Mat2.act (CCL.Mat2.scale (2 : Coordinate)) (clDecode bits)
  | false :: bits =>
      CCL.Mat2.act (CCL.Mat2.cf (1 : Coordinate) 1) (clDecode bits)

@[simp] theorem clDecode_nil : clDecode [] = ⟨1, 1⟩ := rfl

theorem clDecode_replicate_true (exponent : Nat) :
    clDecode (List.replicate exponent true) =
      ⟨(2 : Coordinate) ^ exponent, 1⟩ := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      simp only [List.replicate_succ, clDecode, inductionHypothesis,
        CCL.Mat2.act, CCL.Mat2.scale]
      apply CCL.Proj.ext
      · simp only [pow_succ, mul_one, add_zero]
        exact mul_comm _ _
      · simp only [mul_one, zero_mul, zero_add]

theorem clDecode_replicate_true_append (exponent : Nat) (bits : List Bool) :
    clDecode (List.replicate exponent true ++ bits) =
      CCL.Mat2.act (CCL.Mat2.scale ((2 : Coordinate) ^ exponent))
        (clDecode bits) := by
  induction exponent with
  | zero =>
      apply CCL.Proj.ext <;>
        dsimp only [List.replicate, List.nil_append, pow_zero,
          CCL.Mat2.act, CCL.Mat2.scale] <;>
        ring1
  | succ exponent inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append, clDecode,
        inductionHypothesis]
      apply CCL.Proj.ext
      · simp only [CCL.Mat2.act, CCL.Mat2.scale, pow_succ,
          add_zero, zero_mul]
        ring1
      · simp only [CCL.Mat2.act, CCL.Mat2.scale, add_zero, zero_mul]
        ring1

private theorem clEncodeFuel_reconstruct : ∀ (fuel numerator denominator : Nat)
    (positive : 0 < denominator) (ordered : denominator ≤ numerator),
    numerator ≤ fuel →
      (clDecode
        (clEncodeFuel fuel numerator denominator positive ordered)).Equivalent
        ⟨(numerator : Coordinate), (denominator : Coordinate)⟩
  | 0, 0, denominator, positive, ordered, bounded => by
      have denominatorZero : denominator = 0 :=
        Nat.eq_zero_of_le_zero ordered
      subst denominator
      exact (Nat.not_lt_zero 0 positive).elim
  | 0, numerator + 1, denominator, positive, ordered, bounded =>
      (Nat.not_succ_le_zero numerator bounded).elim
  | fuel + 1, numerator, denominator, positive, ordered, bounded => by
      rw [clEncodeFuel]
      split
      · rename_i equal
        subst numerator
        dsimp only [clDecode, CCL.Proj.Equivalent]
        ring1
      · rename_i notEqual
        let scale := clScale numerator denominator positive ordered
        let normalized := 2 ^ scale.exponent * denominator
        change
          (clDecode
            (if terminal : normalized = numerator then
              List.replicate scale.exponent true
            else
              List.replicate scale.exponent true ++ false ::
                clEncodeFuel fuel normalized
                  (numerator - normalized) _ _)).Equivalent
            ⟨(numerator : Coordinate), (denominator : Coordinate)⟩
        split
        · rename_i terminal
          rw [clDecode_replicate_true]
          dsimp only [CCL.Proj.Equivalent]
          have castTerminal := congrArg (fun value : Nat =>
            (value : Coordinate)) terminal
          dsimp only [normalized] at castTerminal
          rw [Nat.cast_mul, Nat.cast_pow] at castTerminal
          simpa only [Nat.cast_ofNat, mul_one] using castTerminal
        · rename_i nonterminal
          have normalizedLe : normalized ≤ numerator := scale.lower
          have normalizedLt : normalized < numerator :=
            lt_of_le_of_ne normalizedLe nonterminal
          have newPositive : 0 < numerator - normalized :=
            Nat.sub_pos_of_lt normalizedLt
          have upper : numerator < 2 * normalized := by
            calc
              numerator < 2 ^ (scale.exponent + 1) * denominator :=
                scale.upper
              _ = 2 * normalized := by
                simp only [normalized, Nat.pow_succ,
                  Nat.mul_comm, Nat.mul_left_comm]
          have newOrdered : numerator - normalized ≤ normalized :=
            difference_le_of_lt_two_mul upper
          have normalizedBound : normalized ≤ fuel :=
            Nat.lt_succ_iff.mp (normalizedLt.trans_le bounded)
          have tail := clEncodeFuel_reconstruct fuel normalized
            (numerator - normalized) newPositive newOrdered normalizedBound
          have afterFalse := CCL.Mat2.act_respects_equivalent
            (CCL.Mat2.cf (1 : Coordinate) 1) tail
          have afterScale := CCL.Mat2.act_respects_equivalent
            (CCL.Mat2.scale ((2 : Coordinate) ^ scale.exponent))
            afterFalse
          rw [clDecode_replicate_true_append]
          have step :
              (CCL.Mat2.act
                (CCL.Mat2.scale ((2 : Coordinate) ^ scale.exponent))
                (CCL.Mat2.act (CCL.Mat2.cf (1 : Coordinate) 1)
                  (⟨(normalized : Coordinate),
                    ((numerator - normalized : Nat) : Coordinate)⟩ :
                    CCL.Proj Coordinate))).Equivalent
                ⟨(numerator : Coordinate),
                  (denominator : Coordinate)⟩ := by
            dsimp only [CCL.Proj.Equivalent, CCL.Mat2.act,
              CCL.Mat2.scale, CCL.Mat2.cf]
            rw [Nat.cast_sub normalizedLe]
            dsimp only [normalized]
            rw [Nat.cast_mul, Nat.cast_pow]
            ring1
          apply equivalent_trans_of_mid_q afterScale step
          simpa only [CCL.Mat2.act, CCL.Mat2.scale, CCL.Mat2.cf,
            one_mul, zero_mul, add_zero, zero_add] using
            (ne_of_gt (RFAP.ConstructiveFraction.natCast_pos_direct
              (Nat.mul_pos (Nat.two_pow_pos scale.exponent) positive)))

/-- Proposition 4.2: the executable finite continued-logarithm word
reconstructs its displayed positive rational input. -/
theorem clEncode_reconstruct (numerator denominator : Nat)
    (positive : 0 < denominator) (ordered : denominator ≤ numerator) :
    (clDecode (clEncode numerator denominator positive ordered)).Equivalent
      ⟨(numerator : Coordinate), (denominator : Coordinate)⟩ := by
  unfold clEncode
  exact clEncodeFuel_reconstruct numerator numerator denominator positive
    ordered (Nat.le_refl numerator)

end CCL.BaselineAlgorithms
