import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Cover
import RFAP.Geometry.Boxes

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace RFAP.FiniteMeasure

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box

/-- Exact rational area of a displayed RFAP box. -/
def boxContent (box : Box) : Coordinate :=
  box.widthX * box.widthY

theorem boxContent_nonneg (box : Box) : 0 ≤ boxContent box :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    box.widthX_nonneg box.widthY_nonneg

/-- Every proper displayed rational box has strictly positive exact area. -/
theorem boxContent_pos_of_proper {box : Box} (proper : box.Proper) :
    0 < boxContent box := by
  unfold boxContent RFAP.Boxes.Box.widthX RFAP.Boxes.Box.widthY
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.sub_pos_direct proper.1)
    (RFAP.ConstructiveFraction.sub_pos_direct proper.2)

/-- RFAP rational boxes as an instance of the generic finite-cover
calculus. -/
def boxCoverScheme : _root_.FiniteMeasure.CoverScheme Gaussian Box where
  covers box point := box.Contains point
  weight := boxContent
  weight_nonnegative := boxContent_nonneg

/-- Rational box refinement cannot increase exact box content. -/
theorem boxContent_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) :
    boxContent inner ≤ boxContent outer :=
  RFAP.ConstructiveFraction.mul_le_mul_direct
    (RFAP.Boxes.Box.widthX_le_of_refines refines)
    (RFAP.Boxes.Box.widthY_le_of_refines refines)
    inner.widthY_nonneg outer.widthX_nonneg

/-- Box area is at most half its displayed squared diagonal. -/
theorem boxContent_le_half_diagonalSq (box : Box) :
    boxContent box ≤ box.diagonalSq / 2 := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    boxContent box * 2 = 2 * (box.widthX * box.widthY) := by
      dsimp only [boxContent]
      ring1
    _ ≤ 2 * (box.widthX * box.widthY) +
          (box.widthX - box.widthY) ^ 2 :=
      le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (box.widthX - box.widthY))
    _ = box.diagonalSq := by
      dsimp only [RFAP.Boxes.Box.diagonalSq, RFAP.Boxes.Box.widthX,
        RFAP.Boxes.Box.widthY]
      ring1

theorem half_diagonalSq_le_diagonalSq (box : Box) :
    box.diagonalSq / 2 ≤ box.diagonalSq := by
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    box.diagonalSq ≤ box.diagonalSq + box.diagonalSq :=
      le_add_of_nonneg_right box.diagonalSq_nonneg
    _ = box.diagonalSq * 2 := by ring1

theorem boxContent_le_diagonalSq (box : Box) :
    boxContent box ≤ box.diagonalSq :=
  (boxContent_le_half_diagonalSq box).trans
    (half_diagonalSq_le_diagonalSq box)

/-- A squared-diagonal request is also a strict area request. -/
theorem boxContent_lt_of_diagonalSq_lt {box : Box} {target : Coordinate}
    (small : box.diagonalSq < target) : boxContent box < target :=
  (boxContent_le_diagonalSq box).trans_lt small

/-- Zero-to-area rational enclosure attached to one displayed box. -/
def boxContentBound (box : Box) : _root_.FiniteMeasure.Bound where
  lower := 0
  upper := boxContent box
  valid := boxContent_nonneg box

theorem boxContentBound_width (box : Box) :
    (boxContentBound box).width = boxContent box := by
  dsimp only [boxContentBound, _root_.FiniteMeasure.Bound.width]
  ring1

theorem boxContentBound_refines {inner outer : Box}
    (refines : inner.Refines outer) :
    _root_.FiniteMeasure.Bound.Refines
      (boxContentBound inner) (boxContentBound outer) :=
  ⟨le_rfl, boxContent_le_of_refines refines⟩

/-- Exact finite additivity across a displayed vertical cut. -/
theorem vertical_content_add (box : Box) (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper) :
    boxContent (box.verticalLeft cut inside) +
      boxContent (box.verticalRight cut inside) = boxContent box := by
  dsimp only [boxContent, RFAP.Boxes.Box.widthX,
    RFAP.Boxes.Box.widthY, RFAP.Boxes.Box.verticalLeft,
    RFAP.Boxes.Box.verticalRight]
  ring1

/-- Exact finite additivity across a displayed horizontal cut. -/
theorem horizontal_content_add (box : Box) (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper) :
    boxContent (box.horizontalLower cut inside) +
      boxContent (box.horizontalUpper cut inside) = boxContent box := by
  dsimp only [boxContent, RFAP.Boxes.Box.widthX,
    RFAP.Boxes.Box.widthY, RFAP.Boxes.Box.horizontalLower,
    RFAP.Boxes.Box.horizontalUpper]
  ring1

/-- A finite displayed rational box cover. -/
structure BoxCover where
  boxes : List Box

namespace BoxCover

/-- Exact sum of the areas of a finite displayed cover. -/
def content (cover : BoxCover) : Coordinate :=
  (cover.boxes.map boxContent).sum

theorem content_nonneg (cover : BoxCover) : 0 ≤ cover.content := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil => exact le_rfl
  | cons box remaining inductionHypothesis =>
      change 0 ≤ boxContent box + (remaining.map boxContent).sum
      exact add_nonneg (boxContent_nonneg box) inductionHypothesis

/-- Forget the box-specific field name while retaining exactly the same
displayed generic cover certificate. -/
def toFiniteCover (cover : BoxCover) :
    _root_.FiniteMeasure.FiniteCover boxCoverScheme :=
  ⟨cover.boxes⟩

theorem toFiniteCover_content (cover : BoxCover) :
    cover.toFiniteCover.content = cover.content := rfl

/-- Pairwise concatenation is the finite union operation on covers. -/
def append (left right : BoxCover) : BoxCover :=
  ⟨left.boxes ++ right.boxes⟩

theorem content_append (left right : BoxCover) :
    (left.append right).content = left.content + right.content := by
  simp only [content, append, List.map_append, List.sum_append]

/-- A cover contains every displayed rational point satisfying a predicate. -/
def Covers (cover : BoxCover) (predicate : Gaussian → Prop) : Prop :=
  ∀ point, predicate point →
    ∃ box, box ∈ cover.boxes ∧ box.Contains point

theorem append_covers_or {left right : BoxCover}
    {first second : Gaussian → Prop}
    (leftCovers : left.Covers first) (rightCovers : right.Covers second) :
    (left.append right).Covers (fun point => first point ∨ second point) := by
  intro point member
  rcases member with firstMember | secondMember
  · rcases leftCovers point firstMember with ⟨box, boxMember, inside⟩
    exact ⟨box, List.mem_append_left _ boxMember, inside⟩
  · rcases rightCovers point secondMember with ⟨box, boxMember, inside⟩
    exact ⟨box, List.mem_append_right _ boxMember, inside⟩

theorem toFiniteCover_covers {cover : BoxCover}
    {predicate : Gaussian → Prop} (covers : cover.Covers predicate) :
    cover.toFiniteCover.Covers predicate :=
  covers

end BoxCover

/-- Effective rational nullity: every positive rational budget produces one
finite covering certificate below that budget. -/
structure EffectiveNull (predicate : Gaussian → Prop) where
  request : (epsilon : Coordinate) → 0 < epsilon → BoxCover
  covers : ∀ epsilon positive, (request epsilon positive).Covers predicate
  small : ∀ epsilon positive, (request epsilon positive).content < epsilon

namespace EffectiveNull

/-- Every RFAP box-null protocol is an instance of generic finite effective
nullity with exactly the same requests and costs. -/
def toGeneric {predicate : Gaussian → Prop}
    (null : EffectiveNull predicate) :
    _root_.FiniteMeasure.EffectiveNull boxCoverScheme predicate where
  request epsilon positive :=
    (null.request epsilon positive).toFiniteCover
  covers epsilon positive :=
    BoxCover.toFiniteCover_covers (null.covers epsilon positive)
  small epsilon positive := by
    rw [BoxCover.toFiniteCover_content]
    exact null.small epsilon positive

/-- The empty rational predicate is effectively null. -/
def empty : EffectiveNull (fun _ => False) where
  request _ _ := ⟨[]⟩
  covers epsilon positive := by
    intro point impossible
    exact impossible.elim
  small epsilon positive := by
    simpa only [BoxCover.content, List.map_nil, List.sum_nil] using positive

/-- Restrict an effectively null predicate by an explicit pointwise
implication. -/
def mono {smaller larger : Gaussian → Prop}
    (large : EffectiveNull larger)
    (subset : ∀ point, smaller point → larger point) :
    EffectiveNull smaller where
  request := large.request
  covers epsilon positive := by
    intro point member
    exact large.covers epsilon positive point (subset point member)
  small := large.small

/-- Finite union of two effectively null predicates, using an explicit
half-budget allocation. -/
def or {first second : Gaussian → Prop}
    (left : EffectiveNull first) (right : EffectiveNull second) :
    EffectiveNull (fun point => first point ∨ second point) where
  request epsilon positive :=
    let half := epsilon / 2
    let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
      (by decide : (0 : Coordinate) < 2)
    (left.request half halfPositive).append
      (right.request half halfPositive)
  covers epsilon positive := by
    exact BoxCover.append_covers_or
      (left.covers (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
      (right.covers (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
  small epsilon positive := by
    rw [BoxCover.content_append]
    have halfPositive : (0 : Coordinate) < epsilon / 2 :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    have leftSmall := left.small (epsilon / 2) halfPositive
    have rightSmall := right.small (epsilon / 2) halfPositive
    calc
      (left.request (epsilon / 2) halfPositive).content +
          (right.request (epsilon / 2) halfPositive).content <
          epsilon / 2 + epsilon / 2 :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftSmall rightSmall
      _ = epsilon := by
        calc
          epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
          _ = epsilon :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
              (by decide)

end EffectiveNull

/-! ## Displayed finite null families -/

/-- One predicate packaged with its effective finite-cover protocol. -/
structure NullPredicate where
  predicate : Gaussian → Prop
  effective : EffectiveNull predicate

namespace NullPredicate

/-- Pointwise union of a displayed finite null family. -/
def union : List NullPredicate → Gaussian → Prop
  | [], _ => False
  | member :: remaining, point =>
      member.predicate point ∨ union remaining point

/-- Every displayed finite family of effectively null predicates is
effectively null.  The recursive construction allocates half of each current
budget to the head and half to the remaining finite family. -/
def finiteUnion : (family : List NullPredicate) → EffectiveNull (union family)
  | [] => EffectiveNull.empty
  | member :: remaining =>
      member.effective.or (finiteUnion remaining)

end NullPredicate

/-- Degenerate rational box containing exactly the displayed rational point. -/
def pointBox (point : Gaussian) : Box where
  xLower := point.re
  xUpper := point.re
  yLower := point.im
  yUpper := point.im
  x_valid := le_rfl
  y_valid := le_rfl

theorem pointBox_contains (point : Gaussian) :
    (pointBox point).Contains point :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

@[simp] theorem pointBox_content (point : Gaussian) :
    boxContent (pointBox point) = 0 := by
  dsimp only [boxContent, pointBox, RFAP.Boxes.Box.widthX,
    RFAP.Boxes.Box.widthY]
  ring1

/-- A displayed rational singleton is effectively null with an exact
zero-content certificate. -/
def singletonNull (point : Gaussian) :
    EffectiveNull (fun candidate => candidate = point) where
  request _ _ := ⟨[pointBox point]⟩
  covers epsilon positive := by
    intro candidate equal
    subst candidate
    exact ⟨pointBox point, List.mem_cons_self, pointBox_contains point⟩
  small epsilon positive := by
    simpa only [BoxCover.content, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, pointBox_content, add_zero] using positive

/-- Every displayed finite list of rational points is effectively null. -/
def finitePointsNull : (points : List Gaussian) →
    EffectiveNull (fun candidate => candidate ∈ points)
  | [] => EffectiveNull.mono EffectiveNull.empty
      (fun _ member => (List.not_mem_nil member).elim)
  | point :: remaining =>
      EffectiveNull.mono
        ((singletonNull point).or (finitePointsNull remaining))
        (by
          intro candidate member
          simpa only [List.mem_cons] using member)

/-- A predicate holds except on an effectively null rational exception
protocol. -/
def HoldsExceptNull (predicate : Gaussian → Prop) : Type :=
  EffectiveNull (fun point => ¬predicate point)

/-- Operational equality away from an effectively null rational exception. -/
def EqualExceptNull {β : Type} (left right : Gaussian → β) : Type :=
  EffectiveNull (fun point => left point ≠ right point)

def equalExceptNull_refl {β : Type} (value : Gaussian → β) :
    EqualExceptNull value value :=
  EffectiveNull.mono EffectiveNull.empty
    (fun _ notEqual => (notEqual rfl).elim)

def equalExceptNull_symm {β : Type} {left right : Gaussian → β}
    (equal : EqualExceptNull left right) : EqualExceptNull right left :=
  EffectiveNull.mono equal (fun _ notEqual equalReverse =>
    notEqual equalReverse.symm)

/-- Transitivity uses only the finite decidable equality of displayed
codomain values and a finite union of the two exception protocols. -/
def equalExceptNull_trans {β : Type} [DecidableEq β]
    {first second third : Gaussian → β}
    (firstSecond : EqualExceptNull first second)
    (secondThird : EqualExceptNull second third) :
    EqualExceptNull first third := by
  apply EffectiveNull.mono (firstSecond.or secondThird)
  intro point firstThird
  by_cases firstSecondEqual : first point = second point
  · exact Or.inr (fun secondThirdEqual =>
      firstThird (firstSecondEqual.trans secondThirdEqual))
  · exact Or.inl firstSecondEqual

end RFAP.FiniteMeasure
