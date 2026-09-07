import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Triangles.Right

/-!
# Divine Proportions, Chapter 10: the median triangle

All three midpoint sides are retained as displayed lines.  Their distinctness,
parallelism, and non-nullity are proved explicitly, so the final similarity
statement is a finite triple of spread equalities over any explicit field of
characteristic different from two.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Equality of midpoints with a common second endpoint cancels when two is
nonzero.  This is the finite substitute for invoking injectivity of an affine
homothety. -/
theorem midpoint_cancel_common
    (first second common : Point K) (twoNonzero : (2 : K) ≠ 0)
    (equalMidpoints : midpoint first common = midpoint second common) :
    first = second := by
  have equalX := congrArg Point.x equalMidpoints
  have equalY := congrArg Point.y equalMidpoints
  change (first.x + common.x) / 2 = (second.x + common.x) / 2 at equalX
  change (first.y + common.y) / 2 = (second.y + common.y) / 2 at equalY
  apply Point.ext
  · calc
      first.x = ((first.x + common.x) / 2) * 2 - common.x := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
      _ = ((second.x + common.x) / 2) * 2 - common.x := by rw [equalX]
      _ = second.x := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
  · calc
      first.y = ((first.y + common.y) / 2) * 2 - common.y := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1
      _ = ((second.y + common.y) / 2) * 2 - common.y := by rw [equalY]
      _ = second.y := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
        ring1

/-- Distinct points give distinct midpoints when they share the other
endpoint. -/
theorem midpoint_pair_distinct
    (first second common : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    midpoint first common ≠ midpoint second common := by
  intro equalMidpoints
  exact distinct
    (midpoint_cancel_common first second common twoNonzero equalMidpoints)

theorem midpoint_symm (first second : Point K) :
    midpoint first second = midpoint second first := by
  apply Point.ext
  · change (first.x + second.x) / 2 = (second.x + first.x) / 2
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  · change (first.y + second.y) / 2 = (second.y + first.y) / 2
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1

/-- The common-first-endpoint form of `midpoint_pair_distinct`. -/
theorem midpoint_pair_distinct_left
    (common first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    midpoint common first ≠ midpoint common second := by
  intro equalMidpoints
  apply distinct
  apply midpoint_cancel_common first second common twoNonzero
  calc
    midpoint first common = midpoint common first := midpoint_symm first common
    _ = midpoint common second := equalMidpoints
    _ = midpoint second common := midpoint_symm common second

/-- The segment joining two midpoints with a common endpoint has one quarter
of the quadrance of the segment joining the other endpoints. -/
theorem midpoint_segment_quadrance
    (first second common : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint first common) (midpoint second common) =
      quadrance first second / 4 := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    quadrance (midpoint first common) (midpoint second common) * 4 =
        quadrance first second := by
      unfold quadrance midpoint
      change
        ((((second.x + common.x) / 2) -
              ((first.x + common.x) / 2)) ^ 2 +
            (((second.y + common.y) / 2) -
              ((first.y + common.y) / 2)) ^ 2) * 4 =
          (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      rw [fourAsProduct]
      calc
        ((((second.x + common.x) * (2 : K)⁻¹) -
                ((first.x + common.x) * (2 : K)⁻¹)) ^ 2 +
              (((second.y + common.y) * (2 : K)⁻¹) -
                ((first.y + common.y) * (2 : K)⁻¹)) ^ 2) * (2 * 2) =
            ((second.x - first.x) ^ 2 +
              (second.y - first.y) ^ 2) *
                (2 * (2 : K)⁻¹) ^ 2 := by ring1
        _ = (second.x - first.x) ^ 2 +
            (second.y - first.y) ^ 2 := by rw [twoCancel]; ring1
    _ = (quadrance first second / 4) * 4 :=
      (RFAP.ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- The common-first-endpoint form of `midpoint_segment_quadrance`. -/
theorem midpoint_segment_quadrance_left
    (common first second : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (midpoint common first) (midpoint common second) =
      quadrance first second / 4 := by
  calc
    quadrance (midpoint common first) (midpoint common second) =
        quadrance (midpoint first common) (midpoint second common) := by
      rw [midpoint_symm common first, midpoint_symm common second]
    _ = quadrance first second / 4 :=
      midpoint_segment_quadrance first second common twoNonzero

/-- The midpoint segment is parallel to the segment between the other two
endpoints.  This is the half-way instance of Thales' theorem. -/
theorem midpoint_segment_parallel [DecidableEq K]
    (first second common : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (lineThrough (midpoint first common) (midpoint second common)
        (midpoint_pair_distinct first second common distinct twoNonzero)).Parallel
      (lineThrough first second distinct) := by
  unfold Line.Parallel lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- The common-first-endpoint form of `midpoint_segment_parallel`. -/
theorem midpoint_segment_parallel_left [DecidableEq K]
    (common first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (lineThrough (midpoint common first) (midpoint common second)
        (midpoint_pair_distinct_left common first second distinct
          twoNonzero)).Parallel
      (lineThrough first second distinct) := by
  unfold Line.Parallel lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- The midpoint of the side opposite the first vertex. -/
def medianPoint₁ (_first second third : Point K) : Point K :=
  midpoint second third

/-- The midpoint of the side opposite the second vertex. -/
def medianPoint₂ (first _second third : Point K) : Point K :=
  midpoint first third

/-- The midpoint of the side opposite the third vertex. -/
def medianPoint₃ (first second _third : Point K) : Point K :=
  midpoint first second

theorem medianPoint₁_ne_medianPoint₂
    (first second third : Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    medianPoint₁ first second third ≠ medianPoint₂ first second third := by
  unfold medianPoint₁ medianPoint₂
  exact midpoint_pair_distinct second first third firstSecondDistinct.symm
    twoNonzero

theorem medianPoint₂_ne_medianPoint₃
    (first second third : Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    medianPoint₂ first second third ≠ medianPoint₃ first second third := by
  unfold medianPoint₂ medianPoint₃
  exact midpoint_pair_distinct_left first third second
    secondThirdDistinct.symm twoNonzero

theorem medianPoint₁_ne_medianPoint₃
    (first second third : Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    medianPoint₁ first second third ≠ medianPoint₃ first second third := by
  unfold medianPoint₁ medianPoint₃
  intro equalMidpoints
  apply firstThirdDistinct.symm
  apply midpoint_cancel_common third first second twoNonzero
  calc
    midpoint third second = midpoint second third := midpoint_symm third second
    _ = midpoint first second := equalMidpoints

/-- The median-triangle side corresponding to `A₁A₂`. -/
def medianSide₁₂ [DecidableEq K]
    (first second third : Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) : Line K :=
  lineThrough (medianPoint₁ first second third)
    (medianPoint₂ first second third)
    (medianPoint₁_ne_medianPoint₂ first second third firstSecondDistinct
      twoNonzero)

/-- The median-triangle side corresponding to `A₂A₃`. -/
def medianSide₂₃ [DecidableEq K]
    (first second third : Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) : Line K :=
  lineThrough (medianPoint₂ first second third)
    (medianPoint₃ first second third)
    (medianPoint₂_ne_medianPoint₃ first second third secondThirdDistinct
      twoNonzero)

/-- The median-triangle side corresponding to `A₁A₃`. -/
def medianSide₁₃ [DecidableEq K]
    (first second third : Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) : Line K :=
  lineThrough (medianPoint₁ first second third)
    (medianPoint₃ first second third)
    (medianPoint₁_ne_medianPoint₃ first second third firstThirdDistinct
      twoNonzero)

theorem median_side₁₂_quadrance
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (medianPoint₁ first second third)
        (medianPoint₂ first second third) =
      quadrance first second / 4 := by
  unfold medianPoint₁ medianPoint₂
  calc
    quadrance (midpoint second third) (midpoint first third) =
        quadrance second first / 4 :=
      midpoint_segment_quadrance second first third twoNonzero
    _ = quadrance first second / 4 := by rw [quadrance_symm second first]

theorem median_side₂₃_quadrance
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (medianPoint₂ first second third)
        (medianPoint₃ first second third) =
      quadrance second third / 4 := by
  unfold medianPoint₂ medianPoint₃
  calc
    quadrance (midpoint first third) (midpoint first second) =
        quadrance third second / 4 :=
      midpoint_segment_quadrance_left first third second twoNonzero
    _ = quadrance second third / 4 := by rw [quadrance_symm third second]

theorem median_side₁₃_quadrance
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance (medianPoint₁ first second third)
        (medianPoint₃ first second third) =
      quadrance first third / 4 := by
  unfold medianPoint₁ medianPoint₃
  calc
    quadrance (midpoint second third) (midpoint first second) =
        quadrance (midpoint third second) (midpoint first second) := by
      rw [midpoint_symm second third]
    _ = quadrance third first / 4 :=
      midpoint_segment_quadrance third first second twoNonzero
    _ = quadrance first third / 4 := by rw [quadrance_symm third first]

theorem median_side₁₂_parallel [DecidableEq K]
    (first second third : Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₁₂ first second third firstSecondDistinct twoNonzero).Parallel
      (lineThrough first second firstSecondDistinct) := by
  unfold medianSide₁₂ medianPoint₁ medianPoint₂
  unfold Line.Parallel lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem median_side₂₃_parallel [DecidableEq K]
    (first second third : Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₂₃ first second third secondThirdDistinct twoNonzero).Parallel
      (lineThrough second third secondThirdDistinct) := by
  unfold medianSide₂₃ medianPoint₂ medianPoint₃
  unfold Line.Parallel lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem median_side₁₃_parallel [DecidableEq K]
    (first second third : Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₁₃ first second third firstThirdDistinct twoNonzero).Parallel
      (lineThrough first third firstThirdDistinct) := by
  unfold medianSide₁₃ medianPoint₁ medianPoint₃
  unfold Line.Parallel lineThrough midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 71 (Median triangle).  The first six fields are the three
quarter-quadrance and Thales parallelism conclusions.  The final existential
contains explicit non-null certificates for the median sides and the three
corresponding spread equalities, which is precisely the book's similarity
claim without an infinite or quotient-valued line construction. -/
theorem median_triangle [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (side₁₂NonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (side₁₃NonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (side₂₃NonNull :
      ¬ (lineThrough second third secondThirdDistinct).IsNull) :
    quadrance (medianPoint₁ first second third)
        (medianPoint₂ first second third) = quadrance first second / 4 ∧
      quadrance (medianPoint₂ first second third)
        (medianPoint₃ first second third) = quadrance second third / 4 ∧
      quadrance (medianPoint₁ first second third)
        (medianPoint₃ first second third) = quadrance first third / 4 ∧
      (medianSide₁₂ first second third firstSecondDistinct
          twoNonzero).Parallel
        (lineThrough first second firstSecondDistinct) ∧
      (medianSide₂₃ first second third secondThirdDistinct
          twoNonzero).Parallel
        (lineThrough second third secondThirdDistinct) ∧
      (medianSide₁₃ first second third firstThirdDistinct
          twoNonzero).Parallel
        (lineThrough first third firstThirdDistinct) ∧
      ∃ (medianSide₁₂NonNull :
            ¬ (medianSide₁₂ first second third firstSecondDistinct
              twoNonzero).IsNull)
          (medianSide₁₃NonNull :
            ¬ (medianSide₁₃ first second third firstThirdDistinct
              twoNonzero).IsNull)
          (medianSide₂₃NonNull :
            ¬ (medianSide₂₃ first second third secondThirdDistinct
              twoNonzero).IsNull),
        spread
            (medianSide₁₂ first second third firstSecondDistinct twoNonzero)
            (medianSide₁₃ first second third firstThirdDistinct twoNonzero)
            medianSide₁₂NonNull medianSide₁₃NonNull =
          spread (lineThrough first second firstSecondDistinct)
            (lineThrough first third firstThirdDistinct)
            side₁₂NonNull side₁₃NonNull ∧
        spread
            (medianSide₁₂ first second third firstSecondDistinct twoNonzero)
            (medianSide₂₃ first second third secondThirdDistinct twoNonzero)
            medianSide₁₂NonNull medianSide₂₃NonNull =
          spread (lineThrough first second firstSecondDistinct)
            (lineThrough second third secondThirdDistinct)
            side₁₂NonNull side₂₃NonNull ∧
        spread
            (medianSide₁₃ first second third firstThirdDistinct twoNonzero)
            (medianSide₂₃ first second third secondThirdDistinct twoNonzero)
            medianSide₁₃NonNull medianSide₂₃NonNull =
          spread (lineThrough first third firstThirdDistinct)
            (lineThrough second third secondThirdDistinct)
            side₁₃NonNull side₂₃NonNull := by
  have parallel₁₂ := median_side₁₂_parallel first second third
    firstSecondDistinct twoNonzero
  have parallel₁₃ := median_side₁₃_parallel first second third
    firstThirdDistinct twoNonzero
  have parallel₂₃ := median_side₂₃_parallel first second third
    secondThirdDistinct twoNonzero
  have medianSide₁₂NonNull := nonNull_of_parallel
    (lineThrough first second firstSecondDistinct)
    (medianSide₁₂ first second third firstSecondDistinct twoNonzero)
    side₁₂NonNull (Line.parallel_symm parallel₁₂)
  have medianSide₁₃NonNull := nonNull_of_parallel
    (lineThrough first third firstThirdDistinct)
    (medianSide₁₃ first second third firstThirdDistinct twoNonzero)
    side₁₃NonNull (Line.parallel_symm parallel₁₃)
  have medianSide₂₃NonNull := nonNull_of_parallel
    (lineThrough second third secondThirdDistinct)
    (medianSide₂₃ first second third secondThirdDistinct twoNonzero)
    side₂₃NonNull (Line.parallel_symm parallel₂₃)
  refine ⟨median_side₁₂_quadrance first second third twoNonzero,
    median_side₂₃_quadrance first second third twoNonzero,
    median_side₁₃_quadrance first second third twoNonzero,
    parallel₁₂, parallel₂₃, parallel₁₃,
    medianSide₁₂NonNull, medianSide₁₃NonNull, medianSide₂₃NonNull,
    ?_, ?_, ?_⟩
  · exact (spread_eq_of_parallel_pairs
      (lineThrough first second firstSecondDistinct)
      (lineThrough first third firstThirdDistinct)
      (medianSide₁₂ first second third firstSecondDistinct twoNonzero)
      (medianSide₁₃ first second third firstThirdDistinct twoNonzero)
      side₁₂NonNull side₁₃NonNull medianSide₁₂NonNull
      medianSide₁₃NonNull (Line.parallel_symm parallel₁₂)
      (Line.parallel_symm parallel₁₃)).symm
  · exact (spread_eq_of_parallel_pairs
      (lineThrough first second firstSecondDistinct)
      (lineThrough second third secondThirdDistinct)
      (medianSide₁₂ first second third firstSecondDistinct twoNonzero)
      (medianSide₂₃ first second third secondThirdDistinct twoNonzero)
      side₁₂NonNull side₂₃NonNull medianSide₁₂NonNull
      medianSide₂₃NonNull (Line.parallel_symm parallel₁₂)
      (Line.parallel_symm parallel₂₃)).symm
  · exact (spread_eq_of_parallel_pairs
      (lineThrough first third firstThirdDistinct)
      (lineThrough second third secondThirdDistinct)
      (medianSide₁₃ first second third firstThirdDistinct twoNonzero)
      (medianSide₂₃ first second third secondThirdDistinct twoNonzero)
      side₁₃NonNull side₂₃NonNull medianSide₁₃NonNull
      medianSide₂₃NonNull (Line.parallel_symm parallel₁₃)
      (Line.parallel_symm parallel₂₃)).symm

end DivineProportions
