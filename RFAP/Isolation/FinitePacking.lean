import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.TrackSeparation

/-!
# Choice-free finite packing of winding-one tracks

A finite rational grid assigns every sufficiently refined track to one
explicit cell.  Equal assignments contradict local Taylor uniqueness.  The
final pigeonhole bound is proved by direct recursion on `Fin`, avoiding the
choice-dependent generic finite-cardinality theorem.
-/

namespace RFAP.FinitePacking

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.AffineWinding
open RFAP.TrackSeparation

/-- Positive mesh side whose enlarged-cell diagonal is strictly below the
local uniqueness threshold. -/
def meshSide (threshold : Coordinate) : Coordinate :=
  min 1 ((1 / 16 : Coordinate) * threshold)

theorem meshSide_pos {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) : 0 < meshSide threshold := by
  exact lt_min
    (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) thresholdPositive)

theorem eight_meshSide_sq_lt {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    8 * meshSide threshold ^ 2 < threshold := by
  let side := meshSide threshold
  have sidePositive : 0 < side := meshSide_pos thresholdPositive
  have sideLeOne : side ≤ 1 := min_le_left _ _
  have sideLeScale : side ≤ (1 / 16 : Coordinate) * threshold :=
    min_le_right _ _
  have squareLeSide : side ^ 2 ≤ side := by
    rw [pow_two]
    calc
      side * side ≤ 1 * side :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          sideLeOne sidePositive.le
      _ = side := by ring1
  have eightNonnegative : (0 : Coordinate) ≤ 8 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 8) (by decide)).le
  have inverseIdentity : (8 : Coordinate) * (1 / 16) = 1 / 2 := by decide
  have halfLtOne : (1 / 2 : Coordinate) < 1 := by decide
  calc
    8 * side ^ 2 ≤ 8 * side :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLeSide
        eightNonnegative
    _ ≤ 8 * ((1 / 16 : Coordinate) * threshold) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sideLeScale
        eightNonnegative
    _ = (1 / 2 : Coordinate) * threshold := by
      rw [show 8 * ((1 / 16 : Coordinate) * threshold) =
          (8 * (1 / 16 : Coordinate)) * threshold by ring1,
        inverseIdentity]
    _ < 1 * threshold :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct halfLtOne
        thresholdPositive
    _ = threshold := by ring1

def horizontalIntervals (ambient : Box) (side : Coordinate) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (ambient.widthX / side)

def verticalIntervals (ambient : Box) (side : Coordinate) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (ambient.widthY / side)

theorem widthX_le_intervals_mul
    (ambient : Box) {side : Coordinate} (sidePositive : 0 < side) :
    ambient.widthX ≤ (horizontalIntervals ambient side : Nat) * side := by
  have quotientNonnegative : 0 ≤ ambient.widthX / side :=
    RFAP.ConstructiveFraction.mul_nonneg_direct ambient.widthX_nonneg
      (RFAP.ConstructiveFraction.inv_pos_direct sidePositive).le
  have ceiling := RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
    quotientNonnegative
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    ceiling sidePositive.le
  calc
    ambient.widthX = (ambient.widthX / side) * side :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne ambient.widthX side
        (ne_of_gt sidePositive)).symm
    _ ≤ (horizontalIntervals ambient side : Nat) * side := scaled

theorem widthY_le_intervals_mul
    (ambient : Box) {side : Coordinate} (sidePositive : 0 < side) :
    ambient.widthY ≤ (verticalIntervals ambient side : Nat) * side := by
  have quotientNonnegative : 0 ≤ ambient.widthY / side :=
    RFAP.ConstructiveFraction.mul_nonneg_direct ambient.widthY_nonneg
      (RFAP.ConstructiveFraction.inv_pos_direct sidePositive).le
  have ceiling := RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
    quotientNonnegative
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    ceiling sidePositive.le
  calc
    ambient.widthY = (ambient.widthY / side) * side :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne ambient.widthY side
        (ne_of_gt sidePositive)).symm
    _ ≤ (verticalIntervals ambient side : Nat) * side := scaled

/-- Bounded linear scan for the first grid interval whose upper endpoint
reaches the supplied coordinate. -/
def coordinateIndex (lower side value : Coordinate) :
    (intervals : Nat) → Fin (intervals + 1)
  | 0 => 0
  | intervals + 1 =>
      if value ≤ lower + side then 0
      else (coordinateIndex (lower + side) side value intervals).succ

theorem coordinateIndex_mem
    {lower side value : Coordinate} (sidePositive : 0 < side) :
    ∀ (intervals : Nat), lower ≤ value →
      value ≤ lower + (intervals : Nat) * side →
      lower + ((coordinateIndex lower side value intervals).val : Nat) * side ≤
          value ∧
        value ≤ lower +
          (((coordinateIndex lower side value intervals).val : Nat) + 1) *
            side
  | 0, lowerBound, upperBound => by
      have valueEq : value = lower := by
        apply le_antisymm
        · simpa only [Nat.cast_zero, zero_mul, add_zero] using upperBound
        · exact lowerBound
      subst value
      constructor
      · simp [coordinateIndex]
      · simp only [coordinateIndex, Fin.val_zero, Nat.cast_zero, zero_add,
          one_mul]
        exact le_add_of_nonneg_right sidePositive.le
  | intervals + 1, lowerBound, upperBound => by
      by_cases first : value ≤ lower + side
      · constructor
        · simpa only [coordinateIndex, if_pos first, Fin.val_zero,
            Nat.cast_zero, zero_mul, add_zero] using lowerBound
        · simpa only [coordinateIndex, if_pos first, Fin.val_zero,
            Nat.cast_zero, zero_add, Nat.cast_one, one_mul] using first
      · have nextLower : lower + side ≤ value := (lt_of_not_ge first).le
        have nextUpper : value ≤
            (lower + side) + (intervals : Nat) * side := by
          calc
            value ≤ lower + ((intervals + 1 : Nat) : Coordinate) * side :=
              upperBound
            _ = (lower + side) + (intervals : Nat) * side := by
              push_cast
              ring1
        have next := coordinateIndex_mem sidePositive intervals nextLower
          nextUpper
        constructor
        · calc
            lower +
                ((coordinateIndex lower side value (intervals + 1)).val : Nat) *
                  side =
              (lower + side) +
                ((coordinateIndex (lower + side) side value intervals).val :
                  Nat) * side := by
                rw [coordinateIndex, if_neg first]
                simp only [Fin.val_succ]
                push_cast
                ring1
            _ ≤ value := next.1
        · calc
            value ≤ (lower + side) +
                (((coordinateIndex (lower + side) side value intervals).val :
                  Nat) + 1) * side := next.2
            _ = lower +
                (((coordinateIndex lower side value (intervals + 1)).val :
                  Nat) + 1) * side := by
                rw [coordinateIndex, if_neg first]
                simp only [Fin.val_succ]
                push_cast
                ring1

/-- Grid cell enlarged by one mesh side toward increasing coordinates.  This
orientation matches the fixed lower-left anchor of every constructive box. -/
def enlargedCell
    (ambient : Box) (side : Coordinate) (sideNonnegative : 0 ≤ side)
    (i : Fin (horizontalIntervals ambient side + 1))
    (j : Fin (verticalIntervals ambient side + 1)) : Box where
  xLower := ambient.xLower + (i.val : Nat) * side
  xUpper := ambient.xLower + ((i.val : Nat) + 1) * side + side
  yLower := ambient.yLower + (j.val : Nat) * side
  yUpper := ambient.yLower + ((j.val : Nat) + 1) * side + side
  x_valid := by
    calc
      ambient.xLower + (i.val : Nat) * side ≤
          ambient.xLower + ((i.val : Nat) + 1) * side := by
        apply add_le_add_right
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        · exact RFAP.ConstructiveFraction.natCast_le_direct
            (m := i.val) (n := i.val + 1) (Nat.le_add_right i.val 1)
        · exact sideNonnegative
      _ ≤ ambient.xLower + ((i.val : Nat) + 1) * side + side :=
        le_add_of_nonneg_right sideNonnegative
  y_valid := by
    calc
      ambient.yLower + (j.val : Nat) * side ≤
          ambient.yLower + ((j.val : Nat) + 1) * side := by
        apply add_le_add_right
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        · exact RFAP.ConstructiveFraction.natCast_le_direct
            (m := j.val) (n := j.val + 1) (Nat.le_add_right j.val 1)
        · exact sideNonnegative
      _ ≤ ambient.yLower + ((j.val : Nat) + 1) * side + side :=
        le_add_of_nonneg_right sideNonnegative

theorem enlargedCell_diagonalSq
    (ambient : Box) (side : Coordinate) (sideNonnegative : 0 ≤ side)
    (i : Fin (horizontalIntervals ambient side + 1))
    (j : Fin (verticalIntervals ambient side + 1)) :
    (enlargedCell ambient side sideNonnegative i j).diagonalSq =
      8 * side ^ 2 := by
  dsimp only [enlargedCell, RFAP.Boxes.Box.diagonalSq]
  ring1

theorem widths_le_of_diagonal
    {box : Box} {side : Coordinate} (sideNonnegative : 0 ≤ side)
    (diagonal : box.diagonalSq ≤ side ^ 2) :
    box.widthX ≤ side ∧ box.widthY ≤ side := by
  let dimensions : Gaussian := ⟨box.widthX, box.widthY⟩
  have dimensionsNorm : RFAP.ConstructiveGaussian.Gaussian.normSq dimensions =
      box.diagonalSq := rfl
  have bounds := coordinate_bounds_of_normSq_le
    (z := dimensions) sideNonnegative (by
      rw [dimensionsNorm]
      exact diagonal)
  exact ⟨bounds.2.1, bounds.2.2.2⟩

theorem box_refines_anchor_enlargedCell
    {ambient box : Box} {side : Coordinate} (sidePositive : 0 < side)
    (refines : box.Refines ambient)
    (diagonal : box.diagonalSq ≤ side ^ 2) :
    let i := coordinateIndex ambient.xLower side box.anchor.re
      (horizontalIntervals ambient side)
    let j := coordinateIndex ambient.yLower side box.anchor.im
      (verticalIntervals ambient side)
    box.Refines (enlargedCell ambient side sidePositive.le i j) := by
  let horizontal := horizontalIntervals ambient side
  let vertical := verticalIntervals ambient side
  let i := coordinateIndex ambient.xLower side box.anchor.re horizontal
  let j := coordinateIndex ambient.yLower side box.anchor.im vertical
  have anchorAmbient : ambient.Contains box.anchor :=
    refines.contains box.contains_anchor
  have horizontalCover : box.anchor.re ≤
      ambient.xLower + (horizontal : Nat) * side := by
    calc
      box.anchor.re ≤ ambient.xUpper := anchorAmbient.2.1
      _ = ambient.xLower + ambient.widthX := by
        dsimp only [RFAP.Boxes.Box.widthX]
        ring1
      _ ≤ ambient.xLower + (horizontal : Nat) * side :=
        add_le_add_right (widthX_le_intervals_mul ambient sidePositive)
          ambient.xLower
  have verticalCover : box.anchor.im ≤
      ambient.yLower + (vertical : Nat) * side := by
    calc
      box.anchor.im ≤ ambient.yUpper := anchorAmbient.2.2.2
      _ = ambient.yLower + ambient.widthY := by
        dsimp only [RFAP.Boxes.Box.widthY]
        ring1
      _ ≤ ambient.yLower + (vertical : Nat) * side :=
        add_le_add_right (widthY_le_intervals_mul ambient sidePositive)
          ambient.yLower
  have horizontalMembership := coordinateIndex_mem sidePositive horizontal
    anchorAmbient.1 horizontalCover
  have verticalMembership := coordinateIndex_mem sidePositive vertical
    anchorAmbient.2.2.1 verticalCover
  have widths := widths_le_of_diagonal sidePositive.le diagonal
  constructor
  · exact horizontalMembership.1
  constructor
  · calc
      box.xUpper = box.xLower + box.widthX := by
        dsimp only [RFAP.Boxes.Box.widthX]
        ring1
      _ ≤ (ambient.xLower + ((i.val : Nat) + 1) * side) + side :=
        add_le_add horizontalMembership.2 widths.1
  constructor
  · exact verticalMembership.1
  · calc
      box.yUpper = box.yLower + box.widthY := by
        dsimp only [RFAP.Boxes.Box.widthY]
        ring1
      _ ≤ (ambient.yLower + ((j.val : Nat) + 1) * side) + side :=
        add_le_add verticalMembership.2 widths.2

/-! ## Direct finite pigeonhole lemma -/

private def removeFinIndex {m : Nat} (removed value : Fin (m + 1))
    (different : value ≠ removed) : Fin m :=
  if lower : value.val < removed.val then
    ⟨value.val, lower.trans_le (Nat.le_of_lt_succ removed.isLt)⟩
  else
    ⟨value.val - 1, by
      have greater : removed.val < value.val := by
        have unequal : value.val ≠ removed.val := fun equal =>
          different (Fin.ext equal)
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt lower) (Ne.symm unequal)
      exact (Nat.sub_lt (Nat.zero_lt_of_lt greater) (by decide)).trans_le
        (Nat.le_of_lt_succ value.isLt)⟩

private theorem removeFinIndex_injective {m : Nat}
    (removed : Fin (m + 1)) :
    ∀ {x y : Fin (m + 1)} (xDifferent : x ≠ removed)
      (yDifferent : y ≠ removed),
      removeFinIndex removed x xDifferent =
        removeFinIndex removed y yDifferent → x = y := by
  intro x y xDifferent yDifferent equal
  unfold removeFinIndex at equal
  split at equal <;> split at equal
  · have values := congrArg Fin.val equal
    change x.val = y.val at values
    exact Fin.ext values
  · rename_i xLower yNotLower
    have yGreater : removed.val < y.val := by
      have unequal : y.val ≠ removed.val := fun values =>
        yDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt yNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val = y.val - 1 at values
    have removedLeYPredecessor : removed.val ≤ y.val - 1 :=
      Nat.le_sub_of_add_le (Nat.succ_le_of_lt yGreater)
    rw [← values] at removedLeYPredecessor
    exact False.elim ((Nat.not_le_of_gt xLower) removedLeYPredecessor)
  · rename_i xNotLower yLower
    have xGreater : removed.val < x.val := by
      have unequal : x.val ≠ removed.val := fun values =>
        xDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt xNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val - 1 = y.val at values
    have removedLeXPredecessor : removed.val ≤ x.val - 1 :=
      Nat.le_sub_of_add_le (Nat.succ_le_of_lt xGreater)
    rw [values] at removedLeXPredecessor
    exact False.elim ((Nat.not_le_of_gt yLower) removedLeXPredecessor)
  · rename_i xNotLower yNotLower
    have xGreater : removed.val < x.val := by
      have unequal : x.val ≠ removed.val := fun values =>
        xDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt xNotLower) (Ne.symm unequal)
    have yGreater : removed.val < y.val := by
      have unequal : y.val ≠ removed.val := fun values =>
        yDifferent (Fin.ext values)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt yNotLower) (Ne.symm unequal)
    have values := congrArg Fin.val equal
    change x.val - 1 = y.val - 1 at values
    have xPredecessor : x.val - 1 + 1 = x.val :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt xGreater))
    have yPredecessor : y.val - 1 + 1 = y.val :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt yGreater))
    apply Fin.ext
    calc
      x.val = x.val - 1 + 1 := xPredecessor.symm
      _ = y.val - 1 + 1 := congrArg (fun value => value + 1) values
      _ = y.val := yPredecessor

theorem fin_card_le_of_injective_direct : ∀ {n m : Nat},
    (f : Fin n → Fin m) → Function.Injective f → n ≤ m
  | 0, _, _, _ => Nat.zero_le _
  | _ + 1, 0, f, _ => Fin.elim0 (f 0)
  | n + 1, m + 1, f, injective => by
      let removed := f 0
      let reduced : Fin n → Fin m := fun i =>
        removeFinIndex removed (f i.succ) (by
          intro equal
          exact Fin.succ_ne_zero i (injective equal))
      have reducedInjective : Function.Injective reduced := by
        intro i j equal
        have images : f i.succ = f j.succ := by
          apply removeFinIndex_injective <;> assumption
        have successors : i.succ = j.succ := injective images
        have values := congrArg (fun z : Fin (n + 1) => z.val) successors
        change i.val + 1 = j.val + 1 at values
        exact Fin.ext (Nat.add_right_cancel values)
      exact Nat.succ_le_succ
        (fin_card_le_of_injective_direct reduced reducedInjective)

private theorem pairCode_injective {m n : Nat} : Function.Injective
    (fun pair : Fin m × Fin n => pair.1.val * n + pair.2.val) := by
  intro a b equal
  have nPositive : 0 < n := (Nat.zero_le a.2.val).trans_lt a.2.isLt
  have codeDiv : ∀ (i : Nat) (j : Fin n),
      (i * n + j.val) / n = i := by
    intro i j
    rw [Nat.mul_comm i n, Nat.add_comm,
      Nat.add_mul_div_left _ _ nPositive, Nat.div_eq_of_lt j.isLt,
      Nat.zero_add]
  have codeMod : ∀ (i : Nat) (j : Fin n),
      (i * n + j.val) % n = j.val := by
    intro i j
    rw [Nat.mul_comm i n, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt j.isLt]
  have first := congrArg (fun value => value / n) equal
  have second := congrArg (fun value => value % n) equal
  have firstValues : a.1.val = b.1.val := by
    simpa only [codeDiv] using first
  have secondValues : a.2.val = b.2.val := by
    simpa only [codeMod] using second
  apply Prod.ext
  · exact Fin.ext firstValues
  · exact Fin.ext secondValues

def packingBound
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) : Nat :=
  let side := meshSide (uniquenessDiagonalThreshold squarefree ambient)
  (horizontalIntervals ambient side + 1) *
    (verticalIntervals ambient side + 1)

/-- Every finite pairwise-separated family of constructive winding-one tracks
has the displayed explicit finite grid bound. -/
theorem finite_family_card_le_packingBound
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : SquarefreeCertificate p) {count : Nat}
    (tracks : Fin count → WindingOneTrack p ambient)
    (states : (i : Fin count) → WindingOneState p ambient)
    (pairwiseSeparated : ∀ i j, i ≠ j →
      (states i).box.Separated (states j).box) :
    count ≤ packingBound squarefree ambient := by
  let threshold := uniquenessDiagonalThreshold squarefree ambient
  let side := meshSide threshold
  let horizontal := horizontalIntervals ambient side
  let vertical := verticalIntervals ambient side
  have thresholdPositive := uniquenessDiagonalThreshold_pos squarefree ambient
  have sidePositive : 0 < side := meshSide_pos thresholdPositive
  let refined : (i : Fin count) → WindingOneState p ambient := fun i =>
    (tracks i).refine (states i) side sidePositive
  have refinedDiagonal (i : Fin count) :
      (refined i).box.diagonalSq ≤ side ^ 2 :=
    (tracks i).accurate (states i) side sidePositive
  let cell : Fin count → Fin (horizontal + 1) × Fin (vertical + 1) :=
    fun i =>
      (coordinateIndex ambient.xLower side (refined i).box.anchor.re horizontal,
       coordinateIndex ambient.yLower side (refined i).box.anchor.im vertical)
  have refinedCell (i : Fin count) :
      (refined i).box.Refines
        (enlargedCell ambient side sidePositive.le
          (cell i).1 (cell i).2) := by
    exact box_refines_anchor_enlargedCell sidePositive
      (refined i).refinesAmbient (refinedDiagonal i)
  have cellInjective : Function.Injective cell := by
    intro i j equal
    by_cases same : i = j
    · exact same
    · have separated := pairwiseSeparated i j same
      have refinedSeparated := separated.of_refines
        ((tracks i).nested (states i) side sidePositive)
        ((tracks j).nested (states j) side sidePositive)
      have first : (cell i).1 = (cell j).1 := congrArg Prod.fst equal
      have second : (cell i).2 = (cell j).2 := congrArg Prod.snd equal
      let common := enlargedCell ambient side sidePositive.le
        (cell i).1 (cell i).2
      have leftCommon : (refined i).box.Refines common := refinedCell i
      have rightCommon : (refined j).box.Refines common := by
        have raw := refinedCell j
        rw [← first, ← second] at raw
        exact raw
      have commonSmall : common.diagonalSq < threshold := by
        rw [enlargedCell_diagonalSq]
        exact eight_meshSide_sq_lt thresholdPositive
      exact (separated_tracks_not_supported_in_small_common_box
        degreePositive squarefree (tracks i) (tracks j) (refined i)
        (refined j) refinedSeparated common leftCommon rightCommon commonSmall).elim
  let code : Fin count → Fin ((horizontal + 1) * (vertical + 1)) := fun i =>
    ⟨(cell i).1.val * (vertical + 1) + (cell i).2.val, by
      have firstStep : (cell i).1.val * (vertical + 1) + (cell i).2.val <
          ((cell i).1.val + 1) * (vertical + 1) := by
        calc
          (cell i).1.val * (vertical + 1) + (cell i).2.val <
              (cell i).1.val * (vertical + 1) + (vertical + 1) :=
            Nat.add_lt_add_left (cell i).2.isLt _
          _ = ((cell i).1.val + 1) * (vertical + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
      have secondStep : ((cell i).1.val + 1) * (vertical + 1) ≤
          (horizontal + 1) * (vertical + 1) :=
        Nat.mul_le_mul_right (vertical + 1) (cell i).1.isLt
      exact firstStep.trans_le secondStep⟩
  have codeInjective : Function.Injective code := by
    intro i j equal
    apply cellInjective
    apply pairCode_injective
    exact Fin.ext_iff.mp equal
  simpa only [packingBound, threshold, side, horizontal, vertical] using
    fin_card_le_of_injective_direct code codeInjective

end RFAP.FinitePacking
