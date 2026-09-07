import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian

/-!
# Rational boxes over constructive coordinates

These boxes contain only four constructive rational endpoints and finite order
certificates.  The norm bound uses endpoint squares directly, avoiding an
absolute-value compatibility layer.
-/

namespace RFAP.Boxes

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- An axis-aligned box with ordered constructive-rational endpoints. -/
structure Box where
  xLower : Coordinate
  xUpper : Coordinate
  yLower : Coordinate
  yUpper : Coordinate
  x_valid : xLower ≤ xUpper
  y_valid : yLower ≤ yUpper

namespace Box

def Proper (B : Box) : Prop :=
  B.xLower < B.xUpper ∧ B.yLower < B.yUpper

def widthX (B : Box) : Coordinate := B.xUpper - B.xLower
def widthY (B : Box) : Coordinate := B.yUpper - B.yLower

theorem widthX_nonneg (B : Box) : 0 ≤ B.widthX :=
  sub_nonneg.mpr B.x_valid

theorem widthY_nonneg (B : Box) : 0 ≤ B.widthY :=
  sub_nonneg.mpr B.y_valid

def Contains (B : Box) (z : Gaussian) : Prop :=
  B.xLower ≤ z.re ∧ z.re ≤ B.xUpper ∧
    B.yLower ≤ z.im ∧ z.im ≤ B.yUpper

instance containsDecidable (B : Box) (z : Gaussian) :
    Decidable (B.Contains z) := by
  unfold Contains
  infer_instance

def StrictContains (B : Box) (z : Gaussian) : Prop :=
  B.xLower < z.re ∧ z.re < B.xUpper ∧
    B.yLower < z.im ∧ z.im < B.yUpper

theorem StrictContains.contains {B : Box} {z : Gaussian}
    (strict : B.StrictContains z) : B.Contains z :=
  ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le, strict.2.2.2.le⟩

def Refines (inner outer : Box) : Prop :=
  outer.xLower ≤ inner.xLower ∧ inner.xUpper ≤ outer.xUpper ∧
    outer.yLower ≤ inner.yLower ∧ inner.yUpper ≤ outer.yUpper

/-- Strict coordinatewise containment of one constructive box in another. -/
structure StrictInterior (inner outer : Box) : Prop where
  left : outer.xLower < inner.xLower
  right : inner.xUpper < outer.xUpper
  bottom : outer.yLower < inner.yLower
  top : inner.yUpper < outer.yUpper

instance strictInteriorDecidable (inner outer : Box) :
    Decidable (inner.StrictInterior outer) := by
  by_cases left : outer.xLower < inner.xLower
  · by_cases right : inner.xUpper < outer.xUpper
    · by_cases bottom : outer.yLower < inner.yLower
      · by_cases top : inner.yUpper < outer.yUpper
        · exact isTrue ⟨left, right, bottom, top⟩
        · exact isFalse fun strict => top strict.top
      · exact isFalse fun strict => bottom strict.bottom
    · exact isFalse fun strict => right strict.right
  · exact isFalse fun strict => left strict.left

theorem StrictInterior.refines {inner outer : Box}
    (strict : inner.StrictInterior outer) : inner.Refines outer :=
  ⟨strict.left.le, strict.right.le, strict.bottom.le, strict.top.le⟩

/-- Refining a box that is already strictly interior preserves all four
strict outer inequalities. -/
theorem StrictInterior.of_refines {inner middle outer : Box}
    (strict : middle.StrictInterior outer)
    (refines : inner.Refines middle) : inner.StrictInterior outer :=
  ⟨strict.left.trans_le refines.1,
    refines.2.1.trans_lt strict.right,
    strict.bottom.trans_le refines.2.2.1,
    refines.2.2.2.trans_lt strict.top⟩

/-- A strict subbox remains strict after enlarging its outer box. -/
theorem StrictInterior.trans_refines {inner middle outer : Box}
    (strict : inner.StrictInterior middle)
    (refines : middle.Refines outer) : inner.StrictInterior outer :=
  ⟨refines.1.trans_lt strict.left,
    strict.right.trans_le refines.2.1,
    refines.2.2.1.trans_lt strict.bottom,
    strict.top.trans_le refines.2.2.2⟩

/-- Positive coordinate separation of two closed boxes. -/
def Separated (left right : Box) : Prop :=
  left.xUpper < right.xLower ∨ right.xUpper < left.xLower ∨
    left.yUpper < right.yLower ∨ right.yUpper < left.yLower

instance separatedDecidable (left right : Box) :
    Decidable (left.Separated right) := by
  unfold Separated
  infer_instance

/-- A fixed rational point in the intersection of two boxes whenever none of
the four strict separation comparisons succeeds. -/
def overlapPoint (left right : Box) : Gaussian :=
  ⟨max left.xLower right.xLower, max left.yLower right.yLower⟩

/-- Failure of positive box separation constructively exhibits a displayed
rational point contained in both closed boxes. -/
theorem contains_overlapPoint_of_not_separated
    {left right : Box} (notSeparated : ¬left.Separated right) :
    left.Contains (overlapPoint left right) ∧
      right.Contains (overlapPoint left right) := by
  have rightLowerLeLeftUpper : right.xLower ≤ left.xUpper :=
    le_of_not_gt (fun separated => notSeparated (Or.inl separated))
  have leftLowerLeRightUpper : left.xLower ≤ right.xUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inl separated)))
  have rightBottomLeLeftTop : right.yLower ≤ left.yUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inr (Or.inl separated))))
  have leftBottomLeRightTop : left.yLower ≤ right.yUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inr (Or.inr separated))))
  exact
    ⟨⟨le_max_left _ _,
        max_le left.x_valid rightLowerLeLeftUpper,
        le_max_left _ _,
        max_le left.y_valid rightBottomLeLeftTop⟩,
      ⟨le_max_right _ _,
        max_le leftLowerLeRightUpper right.x_valid,
        le_max_right _ _,
        max_le leftBottomLeRightTop right.y_valid⟩⟩

/-- Closed boxes whose interiors are disjoint.  Unlike `Separated`, this
permits the boxes to share an edge; strict refinements of the two boxes are
then genuinely separated. -/
def InteriorSeparated (left right : Box) : Prop :=
  left.xUpper ≤ right.xLower ∨ right.xUpper ≤ left.xLower ∨
    left.yUpper ≤ right.yLower ∨ right.yUpper ≤ left.yLower

theorem interiorSeparated_symm {left right : Box}
    (separated : left.InteriorSeparated right) :
    right.InteriorSeparated left := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inr (Or.inl leftOf)
  · exact Or.inl rightOf
  · exact Or.inr (Or.inr (Or.inr below))
  · exact Or.inr (Or.inr (Or.inl above))

/-- Strictly interior subboxes of interior-disjoint boxes have a positive
coordinate gap. -/
theorem InteriorSeparated.strict_refinements
    {left right leftSmall rightSmall : Box}
    (separated : left.InteriorSeparated right)
    (leftStrict : leftSmall.StrictInterior left)
    (rightStrict : rightSmall.StrictInterior right) :
    leftSmall.Separated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl ((leftStrict.right.trans_le leftOf).trans rightStrict.left)
  · exact Or.inr (Or.inl
      ((rightStrict.right.trans_le rightOf).trans leftStrict.left))
  · exact Or.inr (Or.inr (Or.inl
      ((leftStrict.top.trans_le below).trans rightStrict.bottom)))
  · exact Or.inr (Or.inr (Or.inr
      ((rightStrict.top.trans_le above).trans leftStrict.bottom)))

theorem InteriorSeparated.of_refines
    {left right leftSmall rightSmall : Box}
    (separated : left.InteriorSeparated right)
    (leftRefines : leftSmall.Refines left)
    (rightRefines : rightSmall.Refines right) :
    leftSmall.InteriorSeparated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl (leftRefines.2.1.trans
      (leftOf.trans rightRefines.1))
  · exact Or.inr (Or.inl (rightRefines.2.1.trans
      (rightOf.trans leftRefines.1)))
  · exact Or.inr (Or.inr (Or.inl (leftRefines.2.2.2.trans
      (below.trans rightRefines.2.2.1))))
  · exact Or.inr (Or.inr (Or.inr (rightRefines.2.2.2.trans
      (above.trans leftRefines.2.2.1))))

theorem separated_symm {left right : Box}
    (separated : left.Separated right) : right.Separated left := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inr (Or.inl leftOf)
  · exact Or.inl rightOf
  · exact Or.inr (Or.inr (Or.inr below))
  · exact Or.inr (Or.inr (Or.inl above))

theorem Separated.of_refines
    {left right leftSmall rightSmall : Box}
    (separated : left.Separated right)
    (leftRefines : leftSmall.Refines left)
    (rightRefines : rightSmall.Refines right) :
    leftSmall.Separated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl (leftRefines.2.1.trans_lt
      (leftOf.trans_le rightRefines.1))
  · exact Or.inr (Or.inl (rightRefines.2.1.trans_lt
      (rightOf.trans_le leftRefines.1)))
  · exact Or.inr (Or.inr (Or.inl (leftRefines.2.2.2.trans_lt
      (below.trans_le rightRefines.2.2.1))))
  · exact Or.inr (Or.inr (Or.inr (rightRefines.2.2.2.trans_lt
      (above.trans_le leftRefines.2.2.1))))

/-- Explicit points carried by positively separated boxes cannot coincide. -/
theorem Separated.points_ne {left right : Box} {leftPoint rightPoint : Gaussian}
    (separated : left.Separated right)
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint) : leftPoint ≠ rightPoint := by
  intro equal
  have realEqual := congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
  have imagEqual := congrArg RFAP.ConstructiveGaussian.Gaussian.im equal
  rcases separated with leftOf | rightOf | below | above
  · have impossible : leftPoint.re < rightPoint.re :=
      leftInside.2.1.trans_lt (leftOf.trans_le rightInside.1)
    rw [realEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : rightPoint.re < leftPoint.re :=
      rightInside.2.1.trans_lt (rightOf.trans_le leftInside.1)
    rw [realEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : leftPoint.im < rightPoint.im :=
      leftInside.2.2.2.trans_lt (below.trans_le rightInside.2.2.1)
    rw [imagEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : rightPoint.im < leftPoint.im :=
      rightInside.2.2.2.trans_lt (above.trans_le leftInside.2.2.1)
    rw [imagEqual] at impossible
    exact (lt_irrefl _ impossible).elim

/-- Displayed positive coordinate gap of two separated boxes, together with
its uniform squared-distance consequence. -/
structure SeparationCertificate (left right : Box) where
  gap : Coordinate
  positive : 0 < gap
  lower : ∀ {leftPoint rightPoint : Gaussian},
    left.Contains leftPoint → right.Contains rightPoint →
      gap ^ 2 ≤ normSq (leftPoint - rightPoint)

private theorem forwardRealGapLower
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {leftPoint rightPoint : Gaussian}
    (gapLe : gap ≤ rightPoint.re - leftPoint.re) :
    gap ^ 2 ≤ normSq (leftPoint - rightPoint) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative gapLe 2
  calc
    gap ^ 2 ≤ (rightPoint.re - leftPoint.re) ^ 2 := squares
    _ = (leftPoint.re - rightPoint.re) ^ 2 := by ring1
    _ = (leftPoint.re - rightPoint.re) ^ 2 + 0 := by ring1
    _ ≤ normSq (leftPoint - rightPoint) :=
      add_le_add (le_refl _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (leftPoint.im - rightPoint.im))

private theorem forwardImaginaryGapLower
    {gap : Coordinate} (gapNonnegative : 0 ≤ gap)
    {leftPoint rightPoint : Gaussian}
    (gapLe : gap ≤ rightPoint.im - leftPoint.im) :
    gap ^ 2 ≤ normSq (leftPoint - rightPoint) := by
  have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
    gapNonnegative gapLe 2
  calc
    gap ^ 2 ≤ (rightPoint.im - leftPoint.im) ^ 2 := squares
    _ = (leftPoint.im - rightPoint.im) ^ 2 := by ring1
    _ = 0 + (leftPoint.im - rightPoint.im) ^ 2 := by ring1
    _ ≤ normSq (leftPoint - rightPoint) :=
      add_le_add
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (leftPoint.re - rightPoint.re))
        (le_refl _)

/-- Execute the four finite coordinate comparisons and return the first
positive separation gap, when one exists. -/
def separationCertificate? (left right : Box) :
    Option (SeparationCertificate left right) := by
  if leftOf : left.xUpper < right.xLower then
    let gap := right.xLower - left.xUpper
    exact some
      { gap := gap
        positive := RFAP.ConstructiveFraction.sub_pos_direct leftOf
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ rightPoint.re - leftPoint.re :=
            RFAP.ConstructiveFraction.sub_le_sub_direct rightInside.1 leftInside.2.1
          exact forwardRealGapLower
            (RFAP.ConstructiveFraction.sub_pos_direct leftOf).le gapLe }
  else if rightOf : right.xUpper < left.xLower then
    let gap := left.xLower - right.xUpper
    exact some
      { gap := gap
        positive := RFAP.ConstructiveFraction.sub_pos_direct rightOf
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ leftPoint.re - rightPoint.re :=
            RFAP.ConstructiveFraction.sub_le_sub_direct leftInside.1 rightInside.2.1
          have reverse := forwardRealGapLower
            (RFAP.ConstructiveFraction.sub_pos_direct rightOf).le
            (leftPoint := rightPoint) (rightPoint := leftPoint) gapLe
          calc
            gap ^ 2 ≤ normSq (rightPoint - leftPoint) := reverse
            _ = normSq (leftPoint - rightPoint) := by
              simp only [normSq, sub_re, sub_im]
              ring1 }
  else if below : left.yUpper < right.yLower then
    let gap := right.yLower - left.yUpper
    exact some
      { gap := gap
        positive := RFAP.ConstructiveFraction.sub_pos_direct below
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ rightPoint.im - leftPoint.im :=
            RFAP.ConstructiveFraction.sub_le_sub_direct rightInside.2.2.1 leftInside.2.2.2
          exact forwardImaginaryGapLower
            (RFAP.ConstructiveFraction.sub_pos_direct below).le gapLe }
  else if above : right.yUpper < left.yLower then
    let gap := left.yLower - right.yUpper
    exact some
      { gap := gap
        positive := RFAP.ConstructiveFraction.sub_pos_direct above
        lower := by
          intro leftPoint rightPoint leftInside rightInside
          have gapLe : gap ≤ leftPoint.im - rightPoint.im :=
            RFAP.ConstructiveFraction.sub_le_sub_direct leftInside.2.2.1 rightInside.2.2.2
          have reverse := forwardImaginaryGapLower
            (RFAP.ConstructiveFraction.sub_pos_direct above).le
            (leftPoint := rightPoint) (rightPoint := leftPoint) gapLe
          calc
            gap ^ 2 ≤ normSq (rightPoint - leftPoint) := reverse
            _ = normSq (leftPoint - rightPoint) := by
              simp only [normSq, sub_re, sub_im]
              ring1 }
  else
    exact none

theorem separationCertificate?_ne_none
    {left right : Box} (separated : left.Separated right) :
    separationCertificate? left right ≠ none := by
  rcases separated with leftOf | rightOf | below | above
  · simp [separationCertificate?, leftOf]
  · by_cases leftOf : left.xUpper < right.xLower
    · simp [separationCertificate?, leftOf]
    · simp [separationCertificate?, leftOf, rightOf]
  · by_cases leftOf : left.xUpper < right.xLower
    · simp [separationCertificate?, leftOf]
    · by_cases rightOf : right.xUpper < left.xLower
      · simp [separationCertificate?, leftOf, rightOf]
      · simp [separationCertificate?, leftOf, rightOf, below]
  · by_cases leftOf : left.xUpper < right.xLower
    · simp [separationCertificate?, leftOf]
    · by_cases rightOf : right.xUpper < left.xLower
      · simp [separationCertificate?, leftOf, rightOf]
      · by_cases below : left.yUpper < right.yLower
        · simp [separationCertificate?, leftOf, rightOf, below]
        · simp [separationCertificate?, leftOf, rightOf, below, above]

/-- Total executable separation certificate once the finite disjunction has
been proved.  The proof is used only to eliminate the impossible `none`
branch; the returned gap itself is computed by `separationCertificate?`. -/
def separationCertificate
    {left right : Box} (separated : left.Separated right) :
    SeparationCertificate left right :=
  match found : separationCertificate? left right with
  | some certificate => certificate
  | none => False.elim (separationCertificate?_ne_none separated found)

theorem refines_refl (B : Box) : B.Refines B :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem Refines.trans {A B C : Box} (hAB : A.Refines B) (hBC : B.Refines C) :
    A.Refines C := by
  rcases hAB with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  rcases hBC with ⟨hxLower', hxUpper', hyLower', hyUpper'⟩
  exact ⟨hxLower'.trans hxLower, hxUpper.trans hxUpper',
    hyLower'.trans hyLower, hyUpper.trans hyUpper'⟩

theorem Refines.contains {inner outer : Box} {z : Gaussian}
    (refines : inner.Refines outer) (inside : inner.Contains z) :
    outer.Contains z := by
  rcases refines with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  rcases inside with ⟨hzxLower, hzxUpper, hzyLower, hzyUpper⟩
  exact ⟨hxLower.trans hzxLower, hzxUpper.trans hxUpper,
    hyLower.trans hzyLower, hzyUpper.trans hyUpper⟩

def diagonalSq (B : Box) : Coordinate :=
  (B.xUpper - B.xLower) ^ 2 + (B.yUpper - B.yLower) ^ 2

theorem diagonalSq_nonneg (B : Box) : 0 ≤ B.diagonalSq := by
  exact add_nonneg
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)

theorem widthX_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) : inner.widthX ≤ outer.widthX :=
  RFAP.ConstructiveFraction.sub_le_sub_direct refines.2.1 refines.1

theorem widthY_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) : inner.widthY ≤ outer.widthY :=
  RFAP.ConstructiveFraction.sub_le_sub_direct refines.2.2.2 refines.2.2.1

/-- Shrinking a rational box cannot increase its squared diagonal. -/
theorem diagonalSq_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) :
    inner.diagonalSq ≤ outer.diagonalSq := by
  have xWidth := widthX_le_of_refines refines
  have yWidth := widthY_le_of_refines refines
  have xSquare : inner.widthX ^ 2 ≤ outer.widthX ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct xWidth xWidth
      inner.widthX_nonneg outer.widthX_nonneg
  have ySquare : inner.widthY ^ 2 ≤ outer.widthY ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct yWidth yWidth
      inner.widthY_nonneg outer.widthY_nonneg
  exact add_le_add xSquare ySquare

/-- A fixed executable rational sample of a box. -/
def anchor (B : Box) : Gaussian := ⟨B.xLower, B.yLower⟩

theorem contains_anchor (B : Box) : B.Contains B.anchor :=
  ⟨le_rfl, B.x_valid, le_rfl, B.y_valid⟩

/-- A displayed nonzero rational point of every proper box.  The lower-left
anchor is used unless it is zero, in which case strict width makes the
upper-right corner nonzero. -/
structure NonzeroSample (B : Box) where
  point : Gaussian
  inside : B.Contains point
  nonzero : point ≠ 0

/-- Compute a nonzero sample without selecting from a collection of points. -/
def nonzeroSample (B : Box) (proper : B.Proper) : NonzeroSample B := by
  if anchorZero : B.anchor = 0 then
    let upperRight : Gaussian := ⟨B.xUpper, B.yUpper⟩
    have upperRightInside : B.Contains upperRight :=
      ⟨B.x_valid, le_rfl, B.y_valid, le_rfl⟩
    have upperRightNonzero : upperRight ≠ 0 := by
      intro upperRightZero
      have lowerRealZero := congrArg
        RFAP.ConstructiveGaussian.Gaussian.re anchorZero
      have upperRealZero := congrArg
        RFAP.ConstructiveGaussian.Gaussian.re upperRightZero
      dsimp only [anchor, upperRight,
        RFAP.ConstructiveGaussian.Gaussian.re]
        at lowerRealZero upperRealZero
      simp only [zero_re] at lowerRealZero upperRealZero
      dsimp only [Proper] at proper
      rw [lowerRealZero, upperRealZero] at proper
      exact (lt_irrefl (0 : Coordinate) proper.1).elim
    exact ⟨upperRight, upperRightInside, upperRightNonzero⟩
  else
    exact ⟨B.anchor, B.contains_anchor, anchorZero⟩

/-- Every point of a box is within its squared diagonal of the fixed anchor. -/
theorem normSq_sub_anchor_le {B : Box} {z : Gaussian}
    (inside : B.Contains z) : normSq (z - B.anchor) ≤ B.diagonalSq := by
  have xNonnegative : 0 ≤ z.re - B.xLower := sub_nonneg.mpr inside.1
  have yNonnegative : 0 ≤ z.im - B.yLower := sub_nonneg.mpr inside.2.2.1
  have xBound : z.re - B.xLower ≤ B.xUpper - B.xLower :=
    RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.1 B.xLower
  have yBound : z.im - B.yLower ≤ B.yUpper - B.yLower :=
    RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.2.2 B.yLower
  have xSquare : (z.re - B.xLower) ^ 2 ≤
      (B.xUpper - B.xLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct xBound xBound
      xNonnegative B.widthX_nonneg
  have ySquare : (z.im - B.yLower) ^ 2 ≤
      (B.yUpper - B.yLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct yBound yBound
      yNonnegative B.widthY_nonneg
  exact add_le_add xSquare ySquare

/-- Largest of the four squared endpoint coordinates. -/
def coordinateSqBound (B : Box) : Coordinate :=
  max (max (B.xLower ^ 2) (B.xUpper ^ 2))
    (max (B.yLower ^ 2) (B.yUpper ^ 2))

theorem coordinateSqBound_nonneg (B : Box) : 0 ≤ B.coordinateSqBound := by
  exact (RFAP.ConstructiveFraction.sq_nonneg_direct B.xLower).trans
    ((le_max_left _ _).trans (le_max_left _ _))

/-- Coarse squared Gaussian norm bound for every member of the box. -/
def normSqBound (B : Box) : Coordinate := 2 * B.coordinateSqBound

theorem normSqBound_nonneg (B : Box) : 0 ≤ B.normSqBound :=
  calc
    0 = 0 + 0 := by ring1
    _ ≤ B.coordinateSqBound + B.coordinateSqBound :=
      add_le_add B.coordinateSqBound_nonneg B.coordinateSqBound_nonneg
    _ = B.normSqBound := by
      dsimp only [normSqBound]
      ring1

/-- A value in a closed constructive interval has square bounded by the
larger endpoint square. -/
theorem sq_le_endpoint_max {lower value upper : Coordinate}
    (hlower : lower ≤ value) (hupper : value ≤ upper) :
    value ^ 2 ≤ max (lower ^ 2) (upper ^ 2) := by
  by_cases hvalue : 0 ≤ value
  · have hupperNonnegative : 0 ≤ upper := hvalue.trans hupper
    have hfirst : value * value ≤ upper * value :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct hupper hvalue
    have hsecond : value * upper ≤ upper * upper :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        hupper hupperNonnegative
    have hsquare : value ^ 2 ≤ upper ^ 2 := by
      rw [pow_two, pow_two]
      exact hfirst.trans (by
        rw [RFAP.ConstructiveFraction.mul_comm upper value]
        exact hsecond)
    exact hsquare.trans (le_max_right _ _)
  · have hvalueNonpositive : value ≤ 0 := le_of_not_ge hvalue
    have hlowerNonpositive : lower ≤ 0 := hlower.trans hvalueNonpositive
    have hneg : -value ≤ -lower := RFAP.ConstructiveFraction.neg_le_neg_direct hlower
    have hnegValueNonnegative : 0 ≤ -value := neg_nonneg.mpr hvalueNonpositive
    have hnegLowerNonnegative : 0 ≤ -lower := neg_nonneg.mpr hlowerNonpositive
    have hfirst : (-value) * (-value) ≤ (-lower) * (-value) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        hneg hnegValueNonnegative
    have hsecond : (-value) * (-lower) ≤ (-lower) * (-lower) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        hneg hnegLowerNonnegative
    have hsquare : value ^ 2 ≤ lower ^ 2 := by
      rw [pow_two, pow_two]
      calc
        value * value = (-value) * (-value) := by ring1
        _ ≤ (-lower) * (-value) := hfirst
        _ = (-value) * (-lower) := RFAP.ConstructiveFraction.mul_comm _ _
        _ ≤ (-lower) * (-lower) := hsecond
        _ = lower * lower := by ring1
    exact hsquare.trans (le_max_left _ _)

/-- Any two points of a box are at squared distance at most its squared
diagonal. -/
theorem normSq_sub_le_diagonalSq {B : Box} {u v : Gaussian}
    (uInside : B.Contains u) (vInside : B.Contains v) :
    normSq (u - v) ≤ B.diagonalSq := by
  have xLower : -B.widthX ≤ u.re - v.re := by
    calc
      -B.widthX = B.xLower - B.xUpper := by
        dsimp only [widthX]
        ring1
      _ ≤ u.re - v.re := RFAP.ConstructiveFraction.sub_le_sub_direct uInside.1 vInside.2.1
  have xUpper : u.re - v.re ≤ B.widthX := by
    exact RFAP.ConstructiveFraction.sub_le_sub_direct uInside.2.1 vInside.1
  have yLower : -B.widthY ≤ u.im - v.im := by
    calc
      -B.widthY = B.yLower - B.yUpper := by
        dsimp only [widthY]
        ring1
      _ ≤ u.im - v.im := RFAP.ConstructiveFraction.sub_le_sub_direct uInside.2.2.1 vInside.2.2.2
  have yUpper : u.im - v.im ≤ B.widthY := by
    exact RFAP.ConstructiveFraction.sub_le_sub_direct uInside.2.2.2 vInside.2.2.1
  have xSquare := sq_le_endpoint_max xLower xUpper
  have ySquare := sq_le_endpoint_max yLower yUpper
  have negXSquare : (-B.widthX) ^ 2 = B.widthX ^ 2 := by ring1
  have negYSquare : (-B.widthY) ^ 2 = B.widthY ^ 2 := by ring1
  rw [negXSquare, max_self] at xSquare
  rw [negYSquare, max_self] at ySquare
  exact add_le_add xSquare ySquare

theorem normSq_le_normSqBound {B : Box} {z : Gaussian}
    (inside : B.Contains z) : normSq z ≤ B.normSqBound := by
  rcases inside with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  have hre : z.re ^ 2 ≤ B.coordinateSqBound :=
    (sq_le_endpoint_max hxLower hxUpper).trans (le_max_left _ _)
  have him : z.im ^ 2 ≤ B.coordinateSqBound :=
    (sq_le_endpoint_max hyLower hyUpper).trans (le_max_right _ _)
  calc
    normSq z = z.re ^ 2 + z.im ^ 2 := rfl
    _ ≤ B.coordinateSqBound + B.coordinateSqBound := add_le_add hre him
    _ = B.normSqBound := by
      dsimp only [normSqBound]
      ring1

def symmetric (radius : Coordinate) (nonnegative : 0 ≤ radius) : Box where
  xLower := -radius
  xUpper := radius
  yLower := -radius
  yUpper := radius
  x_valid := (neg_nonpos.mpr nonnegative).trans nonnegative
  y_valid := (neg_nonpos.mpr nonnegative).trans nonnegative

/-- Left child produced by a certified vertical cut. -/
def verticalLeft (B : Box) (cut : Coordinate)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := B.xLower
  xUpper := cut
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.1
  y_valid := B.y_valid

/-- Right child produced by a certified vertical cut. -/
def verticalRight (B : Box) (cut : Coordinate)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := cut
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.2
  y_valid := B.y_valid

theorem verticalLeft_refines (B : Box) (cut : Coordinate)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalLeft cut inside).Refines B :=
  ⟨le_rfl, inside.2, le_rfl, le_rfl⟩

theorem verticalRight_refines (B : Box) (cut : Coordinate)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalRight cut inside).Refines B :=
  ⟨inside.1, le_rfl, le_rfl, le_rfl⟩

/-- Lower child produced by a certified horizontal cut. -/
def horizontalLower (B : Box) (cut : Coordinate)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := cut
  x_valid := B.x_valid
  y_valid := inside.1

/-- Upper child produced by a certified horizontal cut. -/
def horizontalUpper (B : Box) (cut : Coordinate)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := cut
  yUpper := B.yUpper
  x_valid := B.x_valid
  y_valid := inside.2

theorem horizontalLower_refines (B : Box) (cut : Coordinate)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalLower cut inside).Refines B :=
  ⟨le_rfl, le_rfl, le_rfl, inside.2⟩

theorem horizontalUpper_refines (B : Box) (cut : Coordinate)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalUpper cut inside).Refines B :=
  ⟨le_rfl, le_rfl, inside.1, le_rfl⟩

end Box

end RFAP.Boxes
