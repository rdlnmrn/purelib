import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.SpreadPolynomial
import DivineProportions.Trigonometry.SpreadReflection
import DivineProportions.Trigonometry.Quadrea
import DivineProportions.Algebra.FieldEleven

/-!
# Divine Proportions, Theorem 95: regular stars of order three

The three-line star is finite data.  Its cyclic rule stores the three
reflection-lineation equations explicitly, and mutual nonparallelism replaces
any appeal to a global collection of lines.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A regular star of order three, spelling out the book's cyclic indexing. -/
structure RegularThreeStar (K : Type*) [RFAP.ExplicitField K] [DecidableEq K] where
  line₀ : Line K
  line₁ : Line K
  line₂ : Line K
  line₀NonNull : ¬ line₀.IsNull
  line₁NonNull : ¬ line₁.IsNull
  line₂NonNull : ¬ line₂.IsNull
  line₀Line₁Nonparallel : ¬ line₀.Parallel line₁
  line₁Line₂Nonparallel : ¬ line₁.Parallel line₂
  line₂Line₀Nonparallel : ¬ line₂.Parallel line₀
  reflectAround₀ :
    (reflectLine line₀ line₂ line₀NonNull).Equivalent line₁
  reflectAround₁ :
    (reflectLine line₁ line₀ line₁NonNull).Equivalent line₂
  reflectAround₂ :
    (reflectLine line₂ line₁ line₂NonNull).Equivalent line₀

namespace RegularThreeStar

variable [DecidableEq K]

/-- The first two adjacent spreads of a regular three-star are equal. -/
theorem spread₀₁_eq_spread₁₂ (star : RegularThreeStar K) :
    spread star.line₀ star.line₁ star.line₀NonNull star.line₁NonNull =
      spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull := by
  let reflected := reflectLine star.line₁ star.line₀ star.line₁NonNull
  let reflectedNonNull := reflectLine_nonNull star.line₁ star.line₀
    star.line₁NonNull star.line₀NonNull
  have reflectionSpread := spread_reflectLine_mirror
    star.line₁ star.line₀ star.line₁NonNull star.line₀NonNull
  have representativeSpread := spread_eq_of_parallel_pairs
    reflected star.line₁ star.line₂ star.line₁
    reflectedNonNull star.line₁NonNull star.line₂NonNull star.line₁NonNull
    (line_parallel_of_equivalent star.reflectAround₁)
    (Line.parallel_refl star.line₁)
  calc
    spread star.line₀ star.line₁ star.line₀NonNull star.line₁NonNull =
        spread reflected star.line₁ reflectedNonNull star.line₁NonNull :=
          reflectionSpread.symm
    _ = spread star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull :=
      representativeSpread
    _ = spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull :=
      spread_symm star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull

/-- The second and third adjacent spreads of a regular three-star are equal. -/
theorem spread₁₂_eq_spread₂₀ (star : RegularThreeStar K) :
    spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull =
      spread star.line₂ star.line₀ star.line₂NonNull star.line₀NonNull := by
  let reflected := reflectLine star.line₂ star.line₁ star.line₂NonNull
  let reflectedNonNull := reflectLine_nonNull star.line₂ star.line₁
    star.line₂NonNull star.line₁NonNull
  have reflectionSpread := spread_reflectLine_mirror
    star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull
  have representativeSpread := spread_eq_of_parallel_pairs
    reflected star.line₂ star.line₀ star.line₂
    reflectedNonNull star.line₂NonNull star.line₀NonNull star.line₂NonNull
    (line_parallel_of_equivalent star.reflectAround₂)
    (Line.parallel_refl star.line₂)
  calc
    spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull =
        spread reflected star.line₂ reflectedNonNull star.line₂NonNull :=
          reflectionSpread.symm
    _ = spread star.line₀ star.line₂ star.line₀NonNull star.line₂NonNull :=
      representativeSpread
    _ = spread star.line₂ star.line₀ star.line₂NonNull star.line₀NonNull :=
      spread_symm star.line₀ star.line₂ star.line₀NonNull star.line₂NonNull

end RegularThreeStar

/-- The first explicit line in the source's converse construction. -/
def orderThreeLine₀ [Nontrivial K] : Line K where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- The second explicit line `⟨r:1:0⟩`. -/
def orderThreeLine₁ [Nontrivial K] (root : K) : Line K where
  a := root
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- The third explicit line `⟨-r:1:0⟩`. -/
def orderThreeLine₂ [Nontrivial K] (root : K) : Line K where
  a := -root
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  rw [fourAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-- The source's three displayed lines form a regular star whenever
`3 = r²` with `r ≠ 0`. -/
def orderThreeStar [Nontrivial K] [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0) (threeSquare : (3 : K) = root ^ 2)
    (twoNonzero : (2 : K) ≠ 0) : RegularThreeStar K where
  line₀ := orderThreeLine₀
  line₁ := orderThreeLine₁ root
  line₂ := orderThreeLine₂ root
  line₀NonNull := by
    intro nullNorm
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  line₁NonNull := by
    intro nullNorm
    apply four_ne_zero twoNonzero
    calc
      (4 : K) = root ^ 2 + 1 ^ 2 := by rw [← threeSquare]; ring1
      _ = 0 := nullNorm
  line₂NonNull := by
    intro nullNorm
    apply four_ne_zero twoNonzero
    calc
      (4 : K) = root ^ 2 + 1 ^ 2 := by rw [← threeSquare]; ring1
      _ = (-root) ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  line₀Line₁Nonparallel := by
    intro parallel
    apply rootNonzero
    unfold Line.Parallel orderThreeLine₀ orderThreeLine₁ at parallel
    calc
      root = -(0 * 1 - root * 1) := by ring1
      _ = 0 := by rw [parallel]; ring1
  line₁Line₂Nonparallel := by
    intro parallel
    have productNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero rootNonzero
    apply productNonzero
    unfold Line.Parallel orderThreeLine₁ orderThreeLine₂ at parallel
    calc
      (2 : K) * root = root * 1 - (-root) * 1 := by ring1
      _ = 0 := parallel
  line₂Line₀Nonparallel := by
    intro parallel
    apply rootNonzero
    unfold Line.Parallel orderThreeLine₂ orderThreeLine₀ at parallel
    calc
      root = -((-root) * 1 - 0 * 1) := by ring1
      _ = 0 := by rw [parallel]; ring1
  reflectAround₀ := by
    unfold Line.Equivalent
    simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
      lineNorm, orderThreeLine₀, orderThreeLine₁, orderThreeLine₂]
    constructor
    · ring1
    constructor <;> ring1
  reflectAround₁ := by
    unfold Line.Equivalent
    simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
      lineNorm, orderThreeLine₀, orderThreeLine₁, orderThreeLine₂]
    constructor
    · rw [← threeSquare]
      ring1
    constructor <;> ring1
  reflectAround₂ := by
    unfold Line.Equivalent
    simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
      lineNorm, orderThreeLine₀, orderThreeLine₁, orderThreeLine₂]
    constructor
    · rw [show (-root) ^ 2 = (3 : K) by
        calc
          (-root) ^ 2 = root ^ 2 := by ring1
          _ = 3 := threeSquare.symm]
      ring1
    constructor <;> ring1

private theorem square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact False.elim (squareNonzero squareZero)

/-- Theorem 95 (Order three star): a regular three-star exists exactly when
`3` is a nonzero square.  Characteristic two is excluded explicitly because
the source construction then has null mirror lines. -/
theorem order_three_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (RegularThreeStar K) ↔ IsNonzeroSquare (3 : K) := by
  constructor
  · rintro ⟨star⟩
    let s := spread star.line₀ star.line₁
      star.line₀NonNull star.line₁NonNull
    have sNonzero : s ≠ 0 := by
      intro sZero
      apply star.line₀Line₁Nonparallel
      exact (spread_eq_zero_iff_parallel star.line₀ star.line₁
        star.line₀NonNull star.line₁NonNull).1 sZero
    have firstEquality := star.spread₀₁_eq_spread₁₂
    have secondEquality := star.spread₁₂_eq_spread₂₀
    have alternatives := three_equal_spreads
      star.line₀ star.line₁ star.line₂ star.line₀
      star.line₀NonNull star.line₁NonNull star.line₂NonNull star.line₀NonNull
      firstEquality secondEquality (by
        intro parallel
        apply star.line₂Line₀Nonparallel
        exact Line.parallel_symm parallel)
    have selfZero :
        spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull = 0 :=
      (spread_eq_zero_iff_parallel star.line₀ star.line₀
        star.line₀NonNull star.line₀NonNull).2
        (Line.parallel_refl star.line₀)
    change
      spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull = s ∨
        spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull =
          s * (3 - 4 * s) ^ 2 at alternatives
    rw [selfZero] at alternatives
    have factorSquareZero : (3 - 4 * s) ^ 2 = 0 := by
      rcases alternatives with zeroEqualsS | productZero
      · exact False.elim (sNonzero zeroEqualsS.symm)
      · by_cases squareZero : (3 - 4 * s) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero sNonzero squareZero)
              productZero.symm)
    have factorZero := square_eq_zero (3 - 4 * s) factorSquareZero
    have fourS : (4 : K) * s = 3 := by
      calc
        (4 : K) * s = 3 - (3 - 4 * s) := by ring1
        _ = 3 := by rw [factorZero]; ring1
    have fourNonzero := four_ne_zero twoNonzero
    have threeNonzero : (3 : K) ≠ 0 := by
      intro threeZero
      apply (RFAP.ExplicitField.mul_ne_zero fourNonzero sNonzero)
      calc
        (4 : K) * s = 3 := fourS
        _ = 0 := threeZero
    rcases spread_isSpreadNumber star.line₀ star.line₁
        star.line₀NonNull star.line₁NonNull with ⟨root, rootSquare⟩
    have fourComplement : (4 : K) * (1 - s) = 1 := by
      calc
        (4 : K) * (1 - s) = 4 - 4 * s := by ring1
        _ = 1 := by rw [fourS]; ring1
    have threeSquare : (3 : K) = (4 * root) ^ 2 := by
      calc
        (3 : K) = (4 * s) * (4 * (1 - s)) := by
          rw [fourS, fourComplement]
          ring1
        _ = 16 * (s * (1 - s)) := by ring1
        _ = 16 * root ^ 2 := by rw [rootSquare]
        _ = (4 * root) ^ 2 := by ring1
    have rootNonzero : (4 : K) * root ≠ 0 := by
      intro rootZero
      apply threeNonzero
      calc
        (3 : K) = (4 * root) ^ 2 := threeSquare
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨4 * root, rootNonzero, threeSquare⟩
  · rintro ⟨root, rootNonzero, threeSquare⟩
    exact ⟨orderThreeStar root rootNonzero threeSquare twoNonzero⟩

/-- Example 14.2: `5² = 3` in `F₁₁`, yielding the printed regular star with
line parameters `0`, `5`, and `6 = -5`. -/
theorem example_14_2_fieldEleven :
    Nonempty (RegularThreeStar FieldEleven.Element) := by
  apply (order_three_star (K := FieldEleven.Element) (by decide)).2
  exact ⟨5, by decide, by decide⟩

end DivineProportions
