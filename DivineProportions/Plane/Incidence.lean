import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ExplicitField
import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Algebra.FieldEleven

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace DivineProportions

variable {K : Type*}

/-- A Cartesian point is an ordered pair of field elements. -/
@[ext]
structure Point (K : Type*) where
  x : K
  y : K
deriving DecidableEq

/-- A line is a displayed coefficient triple with a nonzero direction pair.
The proof field prevents the invalid triple `⟨0 : 0 : c⟩`. -/
structure Line (K : Type*) [Zero K] where
  a : K
  b : K
  c : K
  direction_nonzero : a ≠ 0 ∨ b ≠ 0

namespace Line

variable [CommRing K]

/-- Equality of two displayed ordered proportions, expressed without a
quotient or a selected scaling coefficient. -/
def Equivalent (left right : Line K) : Prop :=
  left.a * right.b = right.a * left.b ∧
  left.a * right.c = right.a * left.c ∧
  left.b * right.c = right.b * left.c

theorem equivalent_refl (line : Line K) : line.Equivalent line := by
  exact ⟨rfl, rfl, rfl⟩

theorem equivalent_symm {left right : Line K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨first, second, third⟩
  exact ⟨first.symm, second.symm, third.symm⟩

/-- A point lies on a line when it satisfies the displayed linear equation. -/
def Contains (line : Line K) (point : Point K) : Prop :=
  line.a * point.x + line.b * point.y + line.c = 0

/-- Two lines are parallel when their direction determinant vanishes. -/
def Parallel (left right : Line K) : Prop :=
  left.a * right.b - right.a * left.b = 0

/-- Two lines are perpendicular when their direction dot product vanishes. -/
def Perpendicular (left right : Line K) : Prop :=
  left.a * right.a + left.b * right.b = 0

/-- A line is null when its direction quadrance vanishes. -/
def IsNull (line : Line K) : Prop := line.a ^ 2 + line.b ^ 2 = 0

theorem parallel_refl (line : Line K) : line.Parallel line := by
  unfold Parallel
  ring1

theorem parallel_symm {left right : Line K} (parallel : left.Parallel right) :
    right.Parallel left := by
  unfold Parallel at parallel ⊢
  calc
    right.a * left.b - left.a * right.b =
        -(left.a * right.b - right.a * left.b) := by ring1
    _ = 0 := by rw [parallel]; exact neg_zero

theorem perpendicular_symm {left right : Line K}
    (perpendicular : left.Perpendicular right) : right.Perpendicular left := by
  unfold Perpendicular at perpendicular ⊢
  calc
    right.a * left.a + right.b * left.b =
        left.a * right.a + left.b * right.b := by ring1
    _ = 0 := perpendicular

end Line

section Incidence

variable [RFAP.ExplicitField K]

private theorem eq_zero_of_nonzero_mul_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor * factor⁻¹) * value := by rw [factorCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

private theorem eq_of_left_mul_eq_left_mul
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply sub_eq_zero.mp
  apply eq_zero_of_nonzero_mul_left factorNonzero
  calc
    factor * (left - right) = factor * left - factor * right := by ring1
    _ = 0 := by rw [productsEqual]; ring1

/-- Equivalent coefficient triples are parallel. -/
theorem line_parallel_of_equivalent {first second : Line K}
    (equivalent : first.Equivalent second) : first.Parallel second := by
  unfold Line.Equivalent at equivalent
  unfold Line.Parallel
  rw [equivalent.1]
  ring1

/-- Equivalent displayed lines differ by one explicit coefficient scale.
The scale is selected from a displayed nonzero direction coordinate, with no
quotient or choice of a projective representative. -/
theorem line_coefficient_scale_of_equivalent (source target : Line K)
    (equivalent : source.Equivalent target) :
    ∃ scale : K,
      target.a = scale * source.a ∧
      target.b = scale * source.b ∧
      target.c = scale * source.c := by
  rcases source.direction_nonzero with sourceANonzero | sourceBNonzero
  · let scale := target.a / source.a
    have inverseCancel : source.a⁻¹ * source.a = (1 : K) := by
      calc
        source.a⁻¹ * source.a = source.a * source.a⁻¹ := by ring1
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel source.a sourceANonzero
    refine ⟨scale, ?_, ?_, ?_⟩
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.a = target.a * 1 := by ring1
        _ = target.a * (source.a⁻¹ * source.a) := by rw [inverseCancel]
        _ = (target.a * source.a⁻¹) * source.a := by ring1
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.b = 1 * target.b := by ring1
        _ = (source.a⁻¹ * source.a) * target.b := by rw [inverseCancel]
        _ = source.a⁻¹ * (source.a * target.b) := by ring1
        _ = source.a⁻¹ * (target.a * source.b) := by rw [equivalent.1]
        _ = (target.a * source.a⁻¹) * source.b := by ring1
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.c = 1 * target.c := by ring1
        _ = (source.a⁻¹ * source.a) * target.c := by rw [inverseCancel]
        _ = source.a⁻¹ * (source.a * target.c) := by ring1
        _ = source.a⁻¹ * (target.a * source.c) := by rw [equivalent.2.1]
        _ = (target.a * source.a⁻¹) * source.c := by ring1
  · let scale := target.b / source.b
    have inverseCancel : source.b⁻¹ * source.b = (1 : K) := by
      calc
        source.b⁻¹ * source.b = source.b * source.b⁻¹ := by ring1
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel source.b sourceBNonzero
    refine ⟨scale, ?_, ?_, ?_⟩
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.a = target.a * 1 := by ring1
        _ = target.a * (source.b * source.b⁻¹) := by
          rw [RFAP.ExplicitField.mul_inv_cancel source.b sourceBNonzero]
        _ = source.b⁻¹ * (target.a * source.b) := by ring1
        _ = source.b⁻¹ * (source.a * target.b) := by rw [equivalent.1]
        _ = (target.b * source.b⁻¹) * source.a := by ring1
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.b = target.b * 1 := by ring1
        _ = target.b * (source.b⁻¹ * source.b) := by rw [inverseCancel]
        _ = (target.b * source.b⁻¹) * source.b := by ring1
    · unfold scale
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        target.c = 1 * target.c := by ring1
        _ = (source.b⁻¹ * source.b) * target.c := by rw [inverseCancel]
        _ = source.b⁻¹ * (source.b * target.c) := by ring1
        _ = source.b⁻¹ * (target.b * source.c) := by rw [equivalent.2.2]
        _ = (target.b * source.b⁻¹) * source.c := by ring1

/-- Transitivity of quotient-free line equality. -/
theorem line_equivalent_trans {first second third : Line K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases line_coefficient_scale_of_equivalent first second firstSecond with
    ⟨firstScale, secondA, secondB, secondC⟩
  rcases line_coefficient_scale_of_equivalent second third secondThird with
    ⟨secondScale, thirdA, thirdB, thirdC⟩
  unfold Line.Equivalent
  rw [thirdA, thirdB, thirdC, secondA, secondB, secondC]
  constructor
  · ring1
  constructor <;> ring1

/-- Parallelism is transitive for displayed lines. -/
theorem line_parallel_trans {first second third : Line K}
    (firstSecond : first.Parallel second)
    (secondThird : second.Parallel third) : first.Parallel third := by
  unfold Line.Parallel at firstSecond secondThird ⊢
  rcases second.direction_nonzero with secondANonzero | secondBNonzero
  · apply eq_zero_of_nonzero_mul_left secondANonzero
    calc
      second.a * (first.a * third.b - third.a * first.b) =
          first.a *
              (second.a * third.b - third.a * second.b) +
            third.a *
              (first.a * second.b - second.a * first.b) := by ring1
      _ = 0 := by rw [firstSecond, secondThird]; ring1
  · apply eq_zero_of_nonzero_mul_left secondBNonzero
    calc
      second.b * (first.a * third.b - third.a * first.b) =
          third.b *
              (first.a * second.b - second.a * first.b) +
            first.b *
              (second.a * third.b - third.a * second.b) := by ring1
      _ = 0 := by rw [firstSecond, secondThird]; ring1

/-- Parallel direction pairs differ by an explicitly constructed nonzero
scale.  Constants are intentionally absent because parallelism depends only
on the two direction coefficients. -/
theorem direction_scale_of_parallel [DecidableEq K]
    (source target : Line K)
    (parallel : source.Parallel target) :
    ∃ scale : K, scale ≠ 0 ∧
      target.a = scale * source.a ∧ target.b = scale * source.b := by
  unfold Line.Parallel at parallel
  rcases source.direction_nonzero with sourceANonzero | sourceBNonzero
  · have targetANonzero : target.a ≠ 0 := by
      intro targetAZero
      have targetBZero : target.b = 0 := by
        have productZero : source.a * target.b = 0 := by
          calc
            source.a * target.b = target.a * source.b :=
              sub_eq_zero.mp parallel
            _ = 0 := by rw [targetAZero]; ring1
        by_cases zero : target.b = 0
        · exact zero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero sourceANonzero zero) productZero)
      rcases target.direction_nonzero with targetANonzero | targetBNonzero
      · exact targetANonzero targetAZero
      · exact targetBNonzero targetBZero
    let scale := target.a / source.a
    have scaleNonzero : scale ≠ 0 := by
      unfold scale
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact RFAP.ExplicitField.mul_ne_zero targetANonzero
        (RFAP.ExplicitField.inv_ne_zero sourceANonzero)
    refine ⟨scale, scaleNonzero, ?_, ?_⟩
    · exact (RFAP.ExplicitField.div_mul_cancel target.a sourceANonzero).symm
    · apply eq_of_left_mul_eq_left_mul sourceANonzero
      calc
        source.a * target.b = target.a * source.b :=
          sub_eq_zero.mp parallel
        _ = source.a * (scale * source.b) := by
          unfold scale
          rw [RFAP.ExplicitField.div_eq_mul_inv]
          have cancel := RFAP.ExplicitField.mul_inv_cancel source.a
            sourceANonzero
          calc
            target.a * source.b =
                source.a * source.a⁻¹ * (target.a * source.b) := by
              rw [cancel, one_mul]
            _ = source.a * (target.a * source.a⁻¹ * source.b) := by ring1
  · have targetBNonzero : target.b ≠ 0 := by
      intro targetBZero
      have targetAZero : target.a = 0 := by
        have productZero : target.a * source.b = 0 := by
          calc
            target.a * source.b = source.a * target.b :=
              (sub_eq_zero.mp parallel).symm
            _ = 0 := by rw [targetBZero]; ring1
        by_cases zero : target.a = 0
        · exact zero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero zero sourceBNonzero) productZero)
      rcases target.direction_nonzero with targetANonzero | targetBNonzero
      · exact targetANonzero targetAZero
      · exact targetBNonzero targetBZero
    let scale := target.b / source.b
    have scaleNonzero : scale ≠ 0 := by
      unfold scale
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact RFAP.ExplicitField.mul_ne_zero targetBNonzero
        (RFAP.ExplicitField.inv_ne_zero sourceBNonzero)
    refine ⟨scale, scaleNonzero, ?_, ?_⟩
    · apply eq_of_left_mul_eq_left_mul sourceBNonzero
      calc
        source.b * target.a = target.b * source.a := by
          calc
            source.b * target.a = target.a * source.b := by ring1
            _ = source.a * target.b := (sub_eq_zero.mp parallel).symm
            _ = target.b * source.a := by ring1
        _ = source.b * (scale * source.a) := by
          unfold scale
          rw [RFAP.ExplicitField.div_eq_mul_inv]
          have cancel := RFAP.ExplicitField.mul_inv_cancel source.b
            sourceBNonzero
          calc
            target.b * source.a =
                source.b * source.b⁻¹ * (target.b * source.a) := by
              rw [cancel, one_mul]
            _ = source.b * (target.b * source.b⁻¹ * source.a) := by ring1
    · exact (RFAP.ExplicitField.div_mul_cancel target.b sourceBNonzero).symm

/-- Equivalent displayed line representatives contain exactly the same
points. -/
theorem line_contains_of_equivalent {first second : Line K}
    (equivalent : first.Equivalent second) (point : Point K)
    (contains : first.Contains point) : second.Contains point := by
  unfold Line.Equivalent at equivalent
  unfold Line.Contains at contains ⊢
  rcases first.direction_nonzero with firstANonzero | firstBNonzero
  · apply eq_zero_of_nonzero_mul_left firstANonzero
    calc
      first.a *
          (second.a * point.x + second.b * point.y + second.c) =
        first.a * second.a * point.x +
          (first.a * second.b) * point.y + first.a * second.c := by ring1
      _ = second.a * first.a * point.x +
          (second.a * first.b) * point.y + second.a * first.c := by
            rw [equivalent.1, equivalent.2.1]
            ring1
      _ =
        second.a *
          (first.a * point.x + first.b * point.y + first.c) := by ring1
      _ = 0 := by rw [contains]; ring1
  · apply eq_zero_of_nonzero_mul_left firstBNonzero
    have directionSwap : first.b * second.a = second.b * first.a := by
      calc
        first.b * second.a = second.a * first.b := by ring1
        _ = first.a * second.b := equivalent.1.symm
        _ = second.b * first.a := by ring1
    calc
      first.b *
          (second.a * point.x + second.b * point.y + second.c) =
        (first.b * second.a) * point.x +
          first.b * second.b * point.y + first.b * second.c := by ring1
      _ = (second.b * first.a) * point.x +
          second.b * first.b * point.y + second.b * first.c := by
            rw [directionSwap, equivalent.2.2]
            ring1
      _ =
        second.b *
          (first.a * point.x + first.b * point.y + first.c) := by ring1
      _ = 0 := by rw [contains]; ring1

/-- The signed determinant used by the Collinear points theorem. -/
def pointDeterminant (first second third : Point K) : K :=
  first.x * second.y - first.x * third.y +
    second.x * third.y - third.x * second.y +
    third.x * first.y - second.x * first.y

/-- Three points are collinear when one displayed line contains all three. -/
def Collinear (first second third : Point K) : Prop :=
  ∃ line : Line K,
    line.Contains first ∧ line.Contains second ∧ line.Contains third

private theorem sub_ne_zero_of_ne {a b : K} (different : a ≠ b) : a - b ≠ 0 := by
  intro differenceZero
  apply different
  calc
    a = (a - b) + b := by ring1
    _ = 0 + b := by rw [differenceZero]
    _ = b := zero_add b

/-- The explicit coefficient triple through two distinct points. -/
def lineThrough [DecidableEq K] (first second : Point K)
    (distinct : first ≠ second) : Line K where
  a := first.y - second.y
  b := second.x - first.x
  c := first.x * second.y - second.x * first.y
  direction_nonzero := by
    by_cases sameY : first.y = second.y
    · right
      apply sub_ne_zero_of_ne
      intro sameX
      apply distinct
      apply Point.ext
      · exact sameX.symm
      · exact sameY
    · exact Or.inl (sub_ne_zero_of_ne sameY)

@[simp] theorem lineThrough_a [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).a = first.y - second.y := rfl

@[simp] theorem lineThrough_b [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).b = second.x - first.x := rfl

@[simp] theorem lineThrough_c [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).c =
      first.x * second.y - second.x * first.y := rfl

/-- Theorem 2, existence half: the displayed line contains the first point. -/
theorem lineThrough_contains_first [DecidableEq K] (first second : Point K)
    (distinct : first ≠ second) :
    (lineThrough first second distinct).Contains first := by
  unfold Line.Contains lineThrough
  ring1

/-- Theorem 2, existence half: the displayed line contains the second point. -/
theorem lineThrough_contains_second [DecidableEq K] (first second : Point K)
    (distinct : first ≠ second) :
    (lineThrough first second distinct).Contains second := by
  unfold Line.Contains lineThrough
  ring1

/-- Theorem 2 (Line through two points), uniqueness up to equality of ordered
proportions.  No representative is chosen by quotient or choice. -/
theorem lineThrough_unique [DecidableEq K] (first second : Point K)
    (distinct : first ≠ second) (other : Line K)
    (containsFirst : other.Contains first)
    (containsSecond : other.Contains second) :
    (lineThrough first second distinct).Equivalent other := by
  unfold Line.Contains at containsFirst containsSecond
  unfold Line.Equivalent
  constructor
  · calc
      (first.y - second.y) * other.b =
          ((other.a * first.x + other.b * first.y + other.c) -
            (other.a * second.x + other.b * second.y + other.c)) +
            other.a * (second.x - first.x) := by ring1
      _ = other.a * (second.x - first.x) := by
        rw [containsFirst, containsSecond]
        ring1
  constructor
  · calc
      (first.y - second.y) * other.c =
          first.y * (other.a * second.x + other.b * second.y + other.c) -
            second.y * (other.a * first.x + other.b * first.y + other.c) +
            other.a * (first.x * second.y - second.x * first.y) := by ring1
      _ = other.a * (first.x * second.y - second.x * first.y) := by
        rw [containsFirst, containsSecond]
        ring1
  · calc
      (second.x - first.x) * other.c =
          second.x * (other.a * first.x + other.b * first.y + other.c) -
            first.x * (other.a * second.x + other.b * second.y + other.c) +
            other.b * (first.x * second.y - second.x * first.y) := by ring1
      _ = other.b * (first.x * second.y - second.x * first.y) := by
        rw [containsFirst, containsSecond]
        ring1

theorem pointDeterminant_eq_zero_of_collinear
    [DecidableEq K]
    {first second third : Point K}
    (collinear : Collinear first second third) :
    pointDeterminant first second third = 0 := by
  rcases collinear with ⟨line, containsFirst, containsSecond, containsThird⟩
  unfold Line.Contains at containsFirst containsSecond containsThird
  have timesA : line.a * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      line.a *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
          (line.a * first.x + line.b * first.y + line.c) *
              (second.y - third.y) +
            (line.a * second.x + line.b * second.y + line.c) *
              (third.y - first.y) +
            (line.a * third.x + line.b * third.y + line.c) *
              (first.y - second.y) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1
  have timesB : line.b * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      line.b *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
          (line.a * first.x + line.b * first.y + line.c) *
              (third.x - second.x) +
            (line.a * second.x + line.b * second.y + line.c) *
              (first.x - third.x) +
            (line.a * third.x + line.b * third.y + line.c) *
              (second.x - first.x) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1
  rcases line.direction_nonzero with aNonzero | bNonzero
  · by_cases determinantZero : pointDeterminant first second third = 0
    · exact determinantZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero aNonzero determinantZero) timesA)
  · by_cases determinantZero : pointDeterminant first second third = 0
    · exact determinantZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero bNonzero determinantZero) timesB)

private theorem collinear_of_pointDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (determinantZero : pointDeterminant first second third = 0) :
    Collinear first second third := by
  by_cases firstSecondDistinct : first ≠ second
  · refine ⟨lineThrough first second firstSecondDistinct,
      lineThrough_contains_first first second firstSecondDistinct,
      lineThrough_contains_second first second firstSecondDistinct, ?_⟩
    unfold Line.Contains lineThrough
    unfold pointDeterminant at determinantZero
    calc
      (first.y - second.y) * third.x + (second.x - first.x) * third.y +
          (first.x * second.y - second.x * first.y) =
          first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y := by ring1
      _ = 0 := determinantZero
  · have firstSecondEqual : first = second := by
      by_cases equal : first = second
      · exact equal
      · exact False.elim (firstSecondDistinct equal)
    by_cases firstThirdDistinct : first ≠ third
    · refine ⟨lineThrough first third firstThirdDistinct,
        lineThrough_contains_first first third firstThirdDistinct, ?_,
        lineThrough_contains_second first third firstThirdDistinct⟩
      rw [← firstSecondEqual]
      exact lineThrough_contains_first first third firstThirdDistinct
    · have firstThirdEqual : first = third := by
        by_cases equal : first = third
        · exact equal
        · exact False.elim (firstThirdDistinct equal)
      let line : Line K :=
        { a := 1
          b := 0
          c := -first.x
          direction_nonzero := Or.inl one_ne_zero }
      refine ⟨line, ?_, ?_, ?_⟩
      · unfold line Line.Contains
        ring1
      · rw [← firstSecondEqual]
        unfold line Line.Contains
        ring1
      · rw [← firstThirdEqual]
        unfold line Line.Contains
        ring1

/-- Theorem 3 (Collinear points): the existential incidence definition is
equivalent to the six-term determinant formula in the source. -/
theorem collinear_iff_pointDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K] (first second third : Point K) :
    Collinear first second third ↔ pointDeterminant first second third = 0 := by
  exact ⟨pointDeterminant_eq_zero_of_collinear,
    collinear_of_pointDeterminant_eq_zero⟩

/-- The determinant of three displayed line coefficient rows. -/
def lineDeterminant (first second third : Line K) : K :=
  first.a * second.b * third.c - first.a * third.b * second.c +
    second.a * third.b * first.c - third.a * second.b * first.c +
    third.a * first.b * second.c - second.a * first.b * third.c

/-- Theorem 4 (Concurrent lines): three lines containing one displayed point
have zero coefficient determinant. -/
theorem lineDeterminant_eq_zero_of_concurrent
    (first second third : Line K) (point : Point K)
    (containsFirst : first.Contains point)
    (containsSecond : second.Contains point)
    (containsThird : third.Contains point) :
    lineDeterminant first second third = 0 := by
  unfold Line.Contains at containsFirst containsSecond containsThird
  unfold lineDeterminant
  calc
    first.a * second.b * third.c - first.a * third.b * second.c +
        second.a * third.b * first.c - third.a * second.b * first.c +
        third.a * first.b * second.c - second.a * first.b * third.c =
      (first.a * point.x + first.b * point.y + first.c) *
          (second.a * third.b - third.a * second.b) -
        (second.a * point.x + second.b * point.y + second.c) *
          (first.a * third.b - third.a * first.b) +
        (third.a * point.x + third.b * point.y + third.c) *
          (first.a * second.b - second.a * first.b) := by ring1
    _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1

/-- The explicit intersection point of two nonparallel lines. -/
def lineIntersection (first second : Line K)
    (_nonparallel : ¬ first.Parallel second) : Point K :=
  { x := (first.b * second.c - second.b * first.c) /
      (first.a * second.b - second.a * first.b)
    y := (first.c * second.a - second.c * first.a) /
      (first.a * second.b - second.a * first.b) }

private theorem nonparallel_denominator_ne_zero
    {first second : Line K} (nonparallel : ¬ first.Parallel second) :
    first.a * second.b - second.a * first.b ≠ 0 := by
  exact nonparallel

/-- Theorem 5, first incidence equation. -/
theorem lineIntersection_on_first (first second : Line K)
    (nonparallel : ¬ first.Parallel second) :
    first.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Line.Contains lineIntersection
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change first.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
      first.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
      first.c = 0
  calc
    first.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
        first.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
        first.c = -first.c * (denominator * denominator⁻¹) + first.c := by
      unfold denominator
      ring1
    _ = 0 := by rw [denominatorCancel]; ring1

/-- Theorem 5, second incidence equation. -/
theorem lineIntersection_on_second (first second : Line K)
    (nonparallel : ¬ first.Parallel second) :
    second.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Line.Contains lineIntersection
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change second.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
      second.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
      second.c = 0
  calc
    second.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
        second.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
        second.c = -second.c * (denominator * denominator⁻¹) + second.c := by
      unfold denominator
      ring1
    _ = 0 := by rw [denominatorCancel]; ring1

/-- If three displayed lines have zero coefficient determinant, the third
line contains the explicit intersection of two nonparallel ones. -/
theorem lineIntersection_on_third_of_determinant_eq_zero
    (first second third : Line K)
    (nonparallel : ¬ first.Parallel second)
    (determinantZero : lineDeterminant first second third = 0) :
    third.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 := nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Line.Contains lineIntersection
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    third.a * ((first.b * second.c - second.b * first.c) *
        denominator⁻¹) +
      third.b * ((first.c * second.a - second.c * first.a) *
        denominator⁻¹) + third.c = 0
  calc
    third.a * ((first.b * second.c - second.b * first.c) *
          denominator⁻¹) +
        third.b * ((first.c * second.a - second.c * first.a) *
          denominator⁻¹) + third.c =
      lineDeterminant first second third * denominator⁻¹ +
        third.c * (1 - denominator * denominator⁻¹) := by
          unfold lineDeterminant denominator
          ring1
    _ = 0 := by rw [determinantZero, denominatorCancel]; ring1

/-- Theorem 5 (Point on two lines), uniqueness of the displayed intersection. -/
theorem lineIntersection_unique (first second : Line K)
    (nonparallel : ¬ first.Parallel second) (point : Point K)
    (onFirst : first.Contains point) (onSecond : second.Contains point) :
    point = lineIntersection first second nonparallel := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Line.Contains at onFirst onSecond
  apply Point.ext
  · have clearedX :
        denominator * point.x = first.b * second.c - second.b * first.c := by
      unfold denominator
      calc
        (first.a * second.b - second.a * first.b) * point.x =
            second.b * (first.a * point.x + first.b * point.y + first.c) -
              first.b * (second.a * point.x + second.b * point.y + second.c) +
              (first.b * second.c - second.b * first.c) := by ring1
        _ = first.b * second.c - second.b * first.c := by
          rw [onFirst, onSecond]
          ring1
    unfold lineIntersection
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [← clearedX]
    calc
      point.x = point.x * 1 := by rw [mul_one]
      _ = point.x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = denominator * point.x * denominator⁻¹ := by ring1
  · have clearedY :
        denominator * point.y = first.c * second.a - second.c * first.a := by
      unfold denominator
      calc
        (first.a * second.b - second.a * first.b) * point.y =
            first.a * (second.a * point.x + second.b * point.y + second.c) -
              second.a * (first.a * point.x + first.b * point.y + first.c) +
              (first.c * second.a - second.c * first.a) := by ring1
        _ = first.c * second.a - second.c * first.a := by
          rw [onFirst, onSecond]
          ring1
    unfold lineIntersection
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [← clearedY]
    calc
      point.y = point.y * 1 := by rw [mul_one]
      _ = point.y * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = denominator * point.y * denominator⁻¹ := by ring1

/-- The line through a point with the same displayed direction coefficients. -/
def parallelThrough (point : Point K) (line : Line K) : Line K where
  a := line.a
  b := line.b
  c := -(line.a * point.x) - line.b * point.y
  direction_nonzero := line.direction_nonzero

/-- Theorem 6: the constructed parallel contains the requested point. -/
theorem parallelThrough_contains (point : Point K) (line : Line K) :
    (parallelThrough point line).Contains point := by
  unfold parallelThrough Line.Contains
  ring1

/-- Theorem 6: the constructed line is parallel to the source line. -/
theorem parallelThrough_parallel (point : Point K) (line : Line K) :
    (parallelThrough point line).Parallel line := by
  unfold parallelThrough Line.Parallel
  ring1

/-- Theorem 6 (Parallel to a line), uniqueness after choosing the source line's
displayed direction representative. -/
theorem parallelThrough_unique (point : Point K) (line other : Line K)
    (sameA : other.a = line.a) (sameB : other.b = line.b)
    (contains : other.Contains point) :
    other.c = (parallelThrough point line).c := by
  unfold Line.Contains at contains
  unfold parallelThrough
  rw [sameA, sameB] at contains
  calc
    other.c = (line.a * point.x + line.b * point.y + other.c) -
        (line.a * point.x + line.b * point.y) := by ring1
    _ = -(line.a * point.x) - line.b * point.y := by rw [contains]; ring1

/-- The altitude through a point to a displayed line. -/
def altitudeThrough (point : Point K) (line : Line K) : Line K where
  a := -line.b
  b := line.a
  c := line.b * point.x - line.a * point.y
  direction_nonzero := by
    rcases line.direction_nonzero with aNonzero | bNonzero
    · exact Or.inr aNonzero
    · left
      intro negativeZero
      apply bNonzero
      calc
        line.b = -(-line.b) := by ring1
        _ = -0 := by rw [negativeZero]
        _ = 0 := neg_zero

/-- Theorem 7: the altitude contains its source point. -/
theorem altitudeThrough_contains (point : Point K) (line : Line K) :
    (altitudeThrough point line).Contains point := by
  unfold altitudeThrough Line.Contains
  ring1

/-- Theorem 7: the altitude is perpendicular to the source line. -/
theorem altitudeThrough_perpendicular (point : Point K) (line : Line K) :
    (altitudeThrough point line).Perpendicular line := by
  unfold altitudeThrough Line.Perpendicular
  ring1

/-- Theorem 7 (Altitude to a line), uniqueness after choosing the displayed
perpendicular direction representative. -/
theorem altitudeThrough_unique (point : Point K) (line other : Line K)
    (sameA : other.a = -line.b) (sameB : other.b = line.a)
    (contains : other.Contains point) :
    other.c = (altitudeThrough point line).c := by
  unfold Line.Contains at contains
  unfold altitudeThrough
  rw [sameA, sameB] at contains
  calc
    other.c = (-line.b * point.x + line.a * point.y + other.c) -
        (-line.b * point.x + line.a * point.y) := by ring1
    _ = line.b * point.x - line.a * point.y := by rw [contains]; ring1

/-- Example 3.1, first displayed rational/decimal point. -/
def example_3_1_first (K : Type*) [OfNat K 2] [OfNat K 3] : Point K := ⟨2, 3⟩

/-- Example 3.1, second displayed rational/decimal point. -/
def example_3_1_second (K : Type*) [OfNat K 2] [OfNat K 5] : Point K := ⟨5, 2⟩

/-- Example 3.3: the displayed line equation contains both displayed points. -/
theorem example_3_3 (K : Type*) [CommRing K] :
    (1 : K) * 2 + 3 * 3 - 11 = 0 ∧
      (1 : K) * 5 + 3 * 2 - 11 = 0 := by
  constructor <;> ring1

/-- Example 3.4, isolated as a characteristic-eleven calculation so it can be
instantiated by any executable finite field of that characteristic. -/
theorem example_3_4 (K : Type*) [CommRing K] (characteristicEleven : (11 : K) = 0) :
    (10 : K) * 3 + 5 * 7 + 1 = 0 ∧
      (10 : K) * 6 + 5 * 1 + 1 = 0 := by
  constructor
  · calc
      (10 : K) * 3 + 5 * 7 + 1 = 6 * 11 := by ring1
      _ = 0 := by rw [characteristicEleven]; ring1
  · calc
      (10 : K) * 6 + 5 * 1 + 1 = 6 * 11 := by ring1
      _ = 0 := by rw [characteristicEleven]; ring1

/-- Example 3.4 evaluated in the concrete eleven-element field. -/
theorem example_3_4_fieldEleven :
    (10 : FieldEleven.Element) * 3 + 5 * 7 + 1 = 0 ∧
      (10 : FieldEleven.Element) * 6 + 5 * 1 + 1 = 0 :=
  example_3_4 FieldEleven.Element FieldEleven.eleven_eq_zero

/-- Exercise 3.1: a zero line determinant need not mean affine concurrency.
These are three distinct parallel coefficient triples; already the first two
cannot contain one common point. -/
theorem exercise_3_1_counterexample [Nontrivial K] (point : Point K) :
    ¬ ((1 : K) * point.x + 0 * point.y + 0 = 0 ∧
      (1 : K) * point.x + 0 * point.y - 1 = 0) := by
  rintro ⟨firstEquation, secondEquation⟩
  have zeroEqualsOne : (0 : K) = 1 := by
    calc
      0 = ((1 : K) * point.x + 0 * point.y + 0) -
          ((1 : K) * point.x + 0 * point.y - 1) := by
        rw [firstEquation, secondEquation]
        ring1
      _ = 1 := by ring1
  exact zero_ne_one zeroEqualsOne

/-- Two parallel displayed lines through one point represent the same ordered
proportion.  This is the quotient-free uniqueness principle used by later
vertex and conic constructions. -/
theorem line_equivalent_of_parallel_and_common_point
    (first second : Line K) (point : Point K)
    (parallel : first.Parallel second)
    (firstContains : first.Contains point)
    (secondContains : second.Contains point) :
    first.Equivalent second := by
  unfold Line.Parallel at parallel
  have directionCross : first.a * second.b = second.a * first.b := by
    calc
      first.a * second.b =
          (first.a * second.b - second.a * first.b) +
            second.a * first.b := by ring1
      _ = second.a * first.b := by rw [parallel]; ring1
  unfold Line.Contains at firstContains secondContains
  have firstConstant :
      first.c = -(first.a * point.x + first.b * point.y) := by
    calc
      first.c =
          (first.a * point.x + first.b * point.y + first.c) -
            (first.a * point.x + first.b * point.y) := by ring1
      _ = -(first.a * point.x + first.b * point.y) := by
        rw [firstContains]
        ring1
  have secondConstant :
      second.c = -(second.a * point.x + second.b * point.y) := by
    calc
      second.c =
          (second.a * point.x + second.b * point.y + second.c) -
            (second.a * point.x + second.b * point.y) := by ring1
      _ = -(second.a * point.x + second.b * point.y) := by
        rw [secondContains]
        ring1
  unfold Line.Equivalent
  refine ⟨directionCross, ?_, ?_⟩
  · rw [firstConstant, secondConstant]
    calc
      first.a * -(second.a * point.x + second.b * point.y) =
          -(first.a * second.a * point.x) -
            (first.a * second.b) * point.y := by ring1
      _ = -(second.a * first.a * point.x) -
            (second.a * first.b) * point.y := by
        rw [directionCross]
        ring1
      _ = second.a * -(first.a * point.x + first.b * point.y) := by
        ring1
  · rw [firstConstant, secondConstant]
    calc
      first.b * -(second.a * point.x + second.b * point.y) =
          -(second.a * first.b * point.x) -
            (first.b * second.b) * point.y := by ring1
      _ = -(first.a * second.b * point.x) -
            (second.b * first.b) * point.y := by
        rw [← directionCross]
        ring1
      _ = second.b * -(first.a * point.x + first.b * point.y) := by
        ring1

end Incidence

end DivineProportions
