import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian

/-!
# Choice-free finite eight-sector table

The predicates and selector are the exact finite table from the CCL-1 paper,
specialized to explicit constructive fractions.  The geometric estimates are
proved from displayed polynomial identities and direct order lemmas; no
linear-programming tactic or inherited ordered-field compatibility theorem is
part of their dependency closure.
-/

namespace CCL.Sectors

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- The eight representatives in the paper's displayed cyclic order. -/
inductive Sector where
  | east | northEast | north | northWest
  | west | southWest | south | southEast
deriving DecidableEq, Repr

namespace Sector

/-- The ordinary three-bit octant code. -/
def code : Sector → List Bool
  | east => [false, false, false]
  | northEast => [false, false, true]
  | north => [false, true, false]
  | northWest => [false, true, true]
  | west => [true, false, false]
  | southWest => [true, false, true]
  | south => [true, true, false]
  | southEast => [true, true, true]

@[simp] theorem code_length (sector : Sector) : sector.code.length = 3 := by
  cases sector <;> rfl

/-- Constructive Gaussian representative selected by a row. -/
def rep : Sector → Gaussian
  | east => ⟨1, 0⟩
  | northEast => ⟨1, 1⟩
  | north => ⟨0, 1⟩
  | northWest => ⟨-1, 1⟩
  | west => ⟨-1, 0⟩
  | southWest => ⟨-1, -1⟩
  | south => ⟨0, -1⟩
  | southEast => ⟨1, -1⟩

/-- Exact rational predicate in the corresponding row of table (6.1). -/
def Holds : Sector → Gaussian → Prop
  | east, z => 1 / 2 ≤ z.re ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | northEast, z => 1 / 2 ≤ z.re ∧ 1 / 2 ≤ z.im
  | north, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 1 / 2 ≤ z.im
  | northWest, z => z.re ≤ -1 / 2 ∧ 1 / 2 ≤ z.im
  | west, z => z.re ≤ -1 / 2 ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | southWest, z => z.re ≤ -1 / 2 ∧ z.im ≤ -1 / 2
  | south, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ z.im ≤ -1 / 2
  | southEast, z => 1 / 2 ≤ z.re ∧ z.im ≤ -1 / 2

instance holdsDecidable (sector : Sector) (z : Gaussian) :
    Decidable (sector.Holds z) := by
  cases sector <;> simp only [Holds] <;> infer_instance

/-- Deterministic sector selection with the paper's boundary convention. -/
def select (z : Gaussian) : Sector :=
  if 1 / 2 ≤ z.re then
    if 1 / 2 ≤ z.im then northEast
    else if z.im ≤ -1 / 2 then southEast
    else east
  else if z.re ≤ -1 / 2 then
    if 1 / 2 ≤ z.im then northWest
    else if z.im ≤ -1 / 2 then southWest
    else west
  else if 1 / 2 ≤ z.im then north
  else if z.im ≤ -1 / 2 then south
  else east

/-- The three exact norm bands used by the CCL controller. -/
def Band (z : Gaussian) : Prop := 1 ≤ normSq z ∧ normSq z ≤ 2
def Entry (z : Gaussian) : Prop := 1 ≤ normSq z ∧ normSq z < 2
def Loop (z : Gaussian) : Prop := 1 < normSq z ∧ normSq z ≤ 2

instance bandDecidable (z : Gaussian) : Decidable (Band z) := by
  unfold Band
  infer_instance

instance entryDecidable (z : Gaussian) : Decidable (Entry z) := by
  unfold Entry
  infer_instance

instance loopDecidable (z : Gaussian) : Decidable (Loop z) := by
  unfold Loop
  infer_instance

private theorem norm_lt_one_of_central (z : Gaussian)
    (xLower : -1 / 2 < z.re) (xUpper : z.re < 1 / 2)
    (yLower : -1 / 2 < z.im) (yUpper : z.im < 1 / 2) :
    normSq z < 1 := by
  have xLeftPositive : 0 < z.re + 1 / 2 := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      xLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < z.re + 1 / 2 := shifted
  have yLeftPositive : 0 < z.im + 1 / 2 := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      yLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < z.im + 1 / 2 := shifted
  have xRightPositive : 0 < 1 / 2 - z.re :=
    RFAP.ConstructiveFraction.sub_pos_direct xUpper
  have yRightPositive : 0 < 1 / 2 - z.im :=
    RFAP.ConstructiveFraction.sub_pos_direct yUpper
  have xSquare : z.re ^ 2 < (1 / 2 : Coordinate) ^ 2 := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      0 < (z.re + 1 / 2) * (1 / 2 - z.re) :=
        RFAP.ConstructiveFraction.mul_pos_direct xLeftPositive xRightPositive
      _ = (1 / 2 : Coordinate) ^ 2 - z.re ^ 2 := by ring1
  have ySquare : z.im ^ 2 < (1 / 2 : Coordinate) ^ 2 := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      0 < (z.im + 1 / 2) * (1 / 2 - z.im) :=
        RFAP.ConstructiveFraction.mul_pos_direct yLeftPositive yRightPositive
      _ = (1 / 2 : Coordinate) ^ 2 - z.im ^ 2 := by ring1
  calc
    normSq z = z.re ^ 2 + z.im ^ 2 := rfl
    _ < (1 / 2 : Coordinate) ^ 2 + (1 / 2 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.add_lt_add_direct xSquare ySquare
    _ = 1 / 2 := by decide
    _ < 1 := by decide

/-- Lemma 6.1: the deterministic row holds whenever the norm is at least one. -/
theorem select_spec (z : Gaussian) (normLower : 1 ≤ normSq z) :
    Holds (select z) z := by
  unfold select
  by_cases xHigh : 1 / 2 ≤ z.re
  · rw [if_pos xHigh]
    by_cases yHigh : 1 / 2 ≤ z.im
    · rw [if_pos yHigh]
      exact ⟨xHigh, yHigh⟩
    · rw [if_neg yHigh]
      by_cases yLow : z.im ≤ -1 / 2
      · rw [if_pos yLow]
        exact ⟨xHigh, yLow⟩
      · rw [if_neg yLow]
        exact ⟨xHigh, lt_of_not_ge yLow, lt_of_not_ge yHigh⟩
  · rw [if_neg xHigh]
    by_cases xLow : z.re ≤ -1 / 2
    · rw [if_pos xLow]
      by_cases yHigh : 1 / 2 ≤ z.im
      · rw [if_pos yHigh]
        exact ⟨xLow, yHigh⟩
      · rw [if_neg yHigh]
        by_cases yLow : z.im ≤ -1 / 2
        · rw [if_pos yLow]
          exact ⟨xLow, yLow⟩
        · rw [if_neg yLow]
          exact ⟨xLow, lt_of_not_ge yLow, lt_of_not_ge yHigh⟩
    · rw [if_neg xLow]
      by_cases yHigh : 1 / 2 ≤ z.im
      · rw [if_pos yHigh]
        exact ⟨lt_of_not_ge xLow, lt_of_not_ge xHigh, yHigh⟩
      · rw [if_neg yHigh]
        by_cases yLow : z.im ≤ -1 / 2
        · rw [if_pos yLow]
          exact ⟨lt_of_not_ge xLow, lt_of_not_ge xHigh, yLow⟩
        · rw [if_neg yLow]
          have normUpper := norm_lt_one_of_central z
            (lt_of_not_ge xLow) (lt_of_not_ge xHigh)
            (lt_of_not_ge yLow) (lt_of_not_ge yHigh)
          exact ((not_lt_of_ge normLower) normUpper).elim

/-- The weak/strict boundary convention makes every satisfied sector row
the row returned by the deterministic selector. -/
theorem select_eq_of_holds {sector : Sector} {z : Gaussian}
    (holds : sector.Holds z) : select z = sector := by
  have halfNegLtHalf : (-1 / 2 : Coordinate) < 1 / 2 := by decide
  cases sector with
  | east =>
      rcases holds with ⟨xHigh, yAbove, yBelow⟩
      rw [select, if_pos xHigh, if_neg (not_le_of_gt yBelow),
        if_neg (not_le_of_gt yAbove)]
  | northEast =>
      rcases holds with ⟨xHigh, yHigh⟩
      rw [select, if_pos xHigh, if_pos yHigh]
  | north =>
      rcases holds with ⟨xAbove, xBelow, yHigh⟩
      rw [select, if_neg (not_le_of_gt xBelow),
        if_neg (not_le_of_gt xAbove), if_pos yHigh]
  | northWest =>
      rcases holds with ⟨xLow, yHigh⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      rw [select, if_neg xNotHigh, if_pos xLow, if_pos yHigh]
  | west =>
      rcases holds with ⟨xLow, yAbove, yBelow⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      rw [select, if_neg xNotHigh, if_pos xLow,
        if_neg (not_le_of_gt yBelow), if_neg (not_le_of_gt yAbove)]
  | southWest =>
      rcases holds with ⟨xLow, yLow⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_neg xNotHigh, if_pos xLow, if_neg yNotHigh,
        if_pos yLow]
  | south =>
      rcases holds with ⟨xAbove, xBelow, yLow⟩
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_neg (not_le_of_gt xBelow),
        if_neg (not_le_of_gt xAbove), if_neg yNotHigh, if_pos yLow]
  | southEast =>
      rcases holds with ⟨xHigh, yLow⟩
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_pos xHigh, if_neg yNotHigh, if_pos yLow]

/-- Two satisfied rows at one displayed point are identical. -/
theorem holds_unique {left right : Sector} {z : Gaussian}
    (leftHolds : left.Holds z) (rightHolds : right.Holds z) :
    left = right :=
  (select_eq_of_holds leftHolds).symm.trans
    (select_eq_of_holds rightHolds)

private theorem axial_contraction (x y : Coordinate)
    (xLower : 1 / 2 ≤ x) (yLower : -1 / 2 < y) (yUpper : y < 1 / 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 2) :
    (x - 1) ^ 2 + y ^ 2 < 1 / 2 := by
  have halfPositive : (0 : Coordinate) < 1 / 2 := by decide
  have xNonnegative : 0 ≤ x := halfPositive.le.trans xLower
  have xUpper : x < 3 / 2 := by
    by_cases upper : x < 3 / 2
    · exact upper
    · have threeHalvesLe : (3 / 2 : Coordinate) ≤ x := le_of_not_gt upper
      have squareLower : (3 / 2 : Coordinate) ^ 2 ≤ x ^ 2 := by
        rw [pow_two, pow_two]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct threeHalvesLe
          threeHalvesLe (by decide) xNonnegative
      have impossible : (9 / 4 : Coordinate) ≤ 2 := by
        calc
          (9 / 4 : Coordinate) = (3 / 2 : Coordinate) ^ 2 := by decide
          _ ≤ x ^ 2 := squareLower
          _ ≤ x ^ 2 + y ^ 2 :=
            le_add_of_nonneg_right
              (RFAP.ConstructiveFraction.sq_nonneg_direct y)
          _ ≤ 2 := normUpper
      exact ((by decide : ¬ ((9 / 4 : Coordinate) ≤ 2)) impossible).elim
  have leftNonnegative : 0 ≤ x - 1 / 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct xLower
  have rightNonnegative : 0 ≤ 3 / 2 - x :=
    RFAP.ConstructiveFraction.sub_nonneg_direct xUpper.le
  have yLeftPositive : 0 < y + 1 / 2 := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      yLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < y + 1 / 2 := shifted
  have yRightPositive : 0 < 1 / 2 - y :=
    RFAP.ConstructiveFraction.sub_pos_direct yUpper
  have firstNonnegative :
      0 ≤ (x - 1 / 2) * (3 / 2 - x) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct leftNonnegative rightNonnegative
  have secondPositive : 0 < (y + 1 / 2) * (1 / 2 - y) :=
    RFAP.ConstructiveFraction.mul_pos_direct yLeftPositive yRightPositive
  have differencePositive :
      0 < 1 / 2 - ((x - 1) ^ 2 + y ^ 2) := by
    calc
      0 < (x - 1 / 2) * (3 / 2 - x) +
          (y + 1 / 2) * (1 / 2 - y) :=
        add_pos_of_nonneg_of_pos firstNonnegative secondPositive
      _ = 1 / 2 - ((x - 1) ^ 2 + y ^ 2) +
          (2 * (1 / 2 : Coordinate) - 1) * (x - 1) := by
        rw [show (3 / 2 : Coordinate) = 1 + 1 / 2 by decide]
        ring1
      _ = 1 / 2 - ((x - 1) ^ 2 + y ^ 2) := by
        rw [show (2 : Coordinate) * (1 / 2) - 1 = 0 by decide]
        ring1
  exact RFAP.ConstructiveFraction.lt_of_sub_pos_direct differencePositive

private theorem diagonal_contraction (x y : Coordinate)
    (xLower : 1 / 2 ≤ x) (yLower : 1 / 2 ≤ y)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 2) :
    (x - 1) ^ 2 + (y - 1) ^ 2 < 1 / 2 := by
  let a := x - 1 / 2
  let b := y - 1 / 2
  let p := a + b
  let q := a ^ 2 + b ^ 2
  have aNonnegative : 0 ≤ a :=
    RFAP.ConstructiveFraction.sub_nonneg_direct xLower
  have bNonnegative : 0 ≤ b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct yLower
  have pNonnegative : 0 ≤ p := add_nonneg aNonnegative bNonnegative
  have normIdentity : x ^ 2 + y ^ 2 = p + q + 1 / 2 := by
    have linearZero : (1 : Coordinate) - 2 * (1 / 2) = 0 := by decide
    have constantZero :
        (2 : Coordinate) * (1 / 2) ^ 2 - 1 / 2 = 0 := by decide
    calc
      x ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 +
          ((1 : Coordinate) - 2 * (1 / 2)) * (x + y) +
          (2 * (1 / 2 : Coordinate) ^ 2 - 1 / 2) := by
        rw [linearZero, constantZero]
        ring1
      _ = p + q + 1 / 2 := by
        dsimp only [a, b, p, q]
        ring1
  have lowerPQ : (1 / 2 : Coordinate) ≤ p + q := by
    apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
      (c := (1 / 2 : Coordinate))
    calc
      (1 / 2 : Coordinate) + 1 / 2 = 1 := by decide
      _ ≤ x ^ 2 + y ^ 2 := normLower
      _ = (p + q) + 1 / 2 := normIdentity
  have upperPQ : p + q ≤ (3 / 2 : Coordinate) := by
    apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
      (c := (1 / 2 : Coordinate))
    calc
      (p + q) + 1 / 2 = x ^ 2 + y ^ 2 := normIdentity.symm
      _ ≤ 2 := normUpper
      _ = (3 / 2 : Coordinate) + 1 / 2 := by decide
  have qLeSquareP : q ≤ p ^ 2 := by
    have twiceProductNonnegative : 0 ≤ 2 * (a * b) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct aNonnegative bNonnegative)
    calc
      q = q + 0 := by ring1
      _ ≤ q + 2 * (a * b) := add_le_add le_rfl twiceProductNonnegative
      _ = p ^ 2 := by
        dsimp only [p, q]
        ring1
  have pPositive : 0 < p := by
    by_cases pZero : p = 0
    · have aZero : a = 0 := by
        apply le_antisymm
        · calc
            a ≤ a + b := le_add_of_nonneg_right bNonnegative
            _ = 0 := pZero
        · exact aNonnegative
      have bZero : b = 0 := by
        apply le_antisymm
        · calc
            b ≤ a + b := le_add_of_nonneg_left aNonnegative
            _ = 0 := pZero
        · exact bNonnegative
      have impossible : (1 / 2 : Coordinate) ≤ 0 := by
        calc
          (1 / 2 : Coordinate) ≤ p + q := lowerPQ
          _ = 0 := by
            rw [pZero]
            dsimp only [q]
            rw [aZero, bZero]
            ring1
      exact ((by decide : ¬ ((1 / 2 : Coordinate) ≤ 0)) impossible).elim
    · exact lt_of_le_of_ne pNonnegative (Ne.symm pZero)
  have qLtP : q < p := by
    by_cases qLess : q < p
    · exact qLess
    · have pLeQ : p ≤ q := le_of_not_gt qLess
      have oneLeP : (1 : Coordinate) ≤ p := by
        by_cases pLessOne : p < 1
        · have oneMinusPositive : 0 < 1 - p :=
            RFAP.ConstructiveFraction.sub_pos_direct pLessOne
          have productPositive : 0 < p * (1 - p) :=
            RFAP.ConstructiveFraction.mul_pos_direct pPositive oneMinusPositive
          have squareLt : p ^ 2 < p := by
            apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
            calc
              0 < p * (1 - p) := productPositive
              _ = p - p ^ 2 := by ring1
          have qLessP : q < p := qLeSquareP.trans_lt squareLt
          exact (not_lt_of_ge pLeQ qLessP).elim
        · exact le_of_not_gt pLessOne
      have twoLeTwoP : (2 : Coordinate) ≤ 2 * p :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (a := (1 : Coordinate)) (b := p) (c := 2)
          oneLeP (by decide)
      have twoPLePQ : 2 * p ≤ p + q := by
        calc
          2 * p = p + p := by ring1
          _ ≤ p + q := add_le_add le_rfl pLeQ
      have impossible : (2 : Coordinate) ≤ 3 / 2 :=
        twoLeTwoP.trans (twoPLePQ.trans upperPQ)
      exact ((by decide : ¬ ((2 : Coordinate) ≤ 3 / 2)) impossible).elim
  apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
  calc
    0 < p - q := RFAP.ConstructiveFraction.sub_pos_direct qLtP
    _ = 1 / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2) +
        (2 * (1 / 2 : Coordinate) - 1) * (x + y) +
        (2 - 3 * (1 / 2 : Coordinate) - 2 * (1 / 2 : Coordinate) ^ 2) := by
      dsimp only [a, b, p, q]
      ring1
    _ = 1 / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2) := by
      rw [show (2 : Coordinate) * (1 / 2) - 1 = 0 by decide,
        show (2 : Coordinate) - 3 * (1 / 2) - 2 * (1 / 2) ^ 2 = 0 by decide]
      ring1

/-- Lemma 6.2: every selected row contracts the whole closed norm band. -/
theorem contraction {z : Gaussian} (band : Band z) (sector : Sector)
    (holds : Holds sector z) : normSq (z - rep sector) < 1 / 2 := by
  rcases band with ⟨normLower, normUpper⟩
  cases sector with
  | east =>
      rcases holds with ⟨xLower, yLower, yUpper⟩
      have contracted :=
        axial_contraction z.re z.im xLower yLower yUpper normUpper
      change (z.re - 1) ^ 2 + (z.im - 0) ^ 2 < 1 / 2
      calc
        (z.re - 1) ^ 2 + (z.im - 0) ^ 2 =
            (z.re - 1) ^ 2 + z.im ^ 2 := by ring1
        _ < 1 / 2 := contracted
  | northEast =>
      rcases holds with ⟨xLower, yLower⟩
      exact diagonal_contraction z.re z.im xLower yLower normLower normUpper
  | north =>
      rcases holds with ⟨xLower, xUpper, yLower⟩
      have rotatedUpper : z.im ^ 2 + (-z.re) ^ 2 ≤ 2 := by
        calc
          z.im ^ 2 + (-z.re) ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction z.im (-z.re) yLower
        (RFAP.ConstructiveFraction.neg_lt_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct xLower)
        rotatedUpper
      change (z.re - 0) ^ 2 + (z.im - 1) ^ 2 < 1 / 2
      calc
        (z.re - 0) ^ 2 + (z.im - 1) ^ 2 =
            (z.im - 1) ^ 2 + (-z.re) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | northWest =>
      rcases holds with ⟨xUpper, yLower⟩
      have rotatedLower : 1 ≤ z.im ^ 2 + (-z.re) ^ 2 := by
        calc
          1 ≤ normSq z := normLower
          _ = z.im ^ 2 + (-z.re) ^ 2 := by
            dsimp only [normSq]
            ring1
      have rotatedUpper : z.im ^ 2 + (-z.re) ^ 2 ≤ 2 := by
        calc
          z.im ^ 2 + (-z.re) ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction z.im (-z.re) yLower
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
        rotatedLower rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - 1) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - 1) ^ 2 =
            (z.im - 1) ^ 2 + (-z.re - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | west =>
      rcases holds with ⟨xUpper, yLower, yUpper⟩
      have rotatedUpper : (-z.re) ^ 2 + (-z.im) ^ 2 ≤ 2 := by
        calc
          (-z.re) ^ 2 + (-z.im) ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction (-z.re) (-z.im)
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct yUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct yLower)
        rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - 0) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - 0) ^ 2 =
            (-z.re - 1) ^ 2 + (-z.im) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | southWest =>
      rcases holds with ⟨xUpper, yUpper⟩
      have rotatedLower : 1 ≤ (-z.re) ^ 2 + (-z.im) ^ 2 := by
        calc
          1 ≤ normSq z := normLower
          _ = (-z.re) ^ 2 + (-z.im) ^ 2 := by
            dsimp only [normSq]
            ring1
      have rotatedUpper : (-z.re) ^ 2 + (-z.im) ^ 2 ≤ 2 := by
        calc
          (-z.re) ^ 2 + (-z.im) ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction (-z.re) (-z.im)
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper)
        rotatedLower rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - -1) ^ 2 =
            (-z.re - 1) ^ 2 + (-z.im - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | south =>
      rcases holds with ⟨xLower, xUpper, yUpper⟩
      have rotatedUpper : (-z.im) ^ 2 + z.re ^ 2 ≤ 2 := by
        calc
          (-z.im) ^ 2 + z.re ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction (-z.im) z.re
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper)
        xLower xUpper rotatedUpper
      change (z.re - 0) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - 0) ^ 2 + (z.im - -1) ^ 2 =
            (-z.im - 1) ^ 2 + z.re ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | southEast =>
      rcases holds with ⟨xLower, yUpper⟩
      have rotatedLower : 1 ≤ (-z.im) ^ 2 + z.re ^ 2 := by
        calc
          1 ≤ normSq z := normLower
          _ = (-z.im) ^ 2 + z.re ^ 2 := by
            dsimp only [normSq]
            ring1
      have rotatedUpper : (-z.im) ^ 2 + z.re ^ 2 ≤ 2 := by
        calc
          (-z.im) ^ 2 + z.re ^ 2 = normSq z := by
            dsimp only [normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction (-z.im) z.re
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper) xLower
        rotatedLower rotatedUpper
      change (z.re - 1) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - 1) ^ 2 + (z.im - -1) ^ 2 =
            (-z.im - 1) ^ 2 + (z.re - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated

/-- Contraction for the deterministic selector. -/
theorem select_contraction {z : Gaussian} (band : Band z) :
    normSq (z - rep (select z)) < 1 / 2 :=
  contraction band (select z) (select_spec z band.1)

end Sector

end CCL.Sectors
