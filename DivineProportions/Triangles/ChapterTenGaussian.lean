import DivineProportions.Trigonometry.TripleSpread
import mathlib.RFAP.ConstructiveGaussian

/-!
# Divine Proportions, Exercise 10.12

The source's complex calculation uses only exact Gaussian-rational arithmetic.
Each value here is therefore represented by a finite pair
`Rational × Rational`, equipped with the project-owned constructive field
operations; no completed complex object is introduced.
-/

namespace DivineProportions

namespace ExerciseTenTwelve

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

/-! Closed rational literals are kept in their finite numerator/denominator
representation while the certificates below are checked.  This prevents the
kernel from repeatedly reducing nested quotient decision procedures. -/

private def rationalLiteral (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) : Rational :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, Int.ofNat denominator,
      Int.natCast_pos.mpr denominatorPositive⟩

private theorem rationalLiteral_mul_denominator
    (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    rationalLiteral numerator denominator denominatorPositive * denominator =
      (numerator : Rational) := by
  exact RFAP.ConstructiveFraction.ofFraction_mul_den
    ⟨numerator, Int.ofNat denominator,
      Int.natCast_pos.mpr denominatorPositive⟩

private theorem rationalNatCastNonzero {value : Nat}
    (valuePositive : 0 < value) : (value : Rational) ≠ 0 := by
  intro castZero
  have castPositive : (0 : Rational) < (value : Rational) :=
    RFAP.ConstructiveFraction.natCast_pos_direct valuePositive
  rw [castZero] at castPositive
  exact (lt_irrefl 0) castPositive

private theorem rationalLiteral_eq_div
    (numerator : Int) (denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    rationalLiteral numerator denominator denominatorPositive =
      (numerator : Rational) / denominator := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (rationalNatCastNonzero denominatorPositive)
  calc
    rationalLiteral numerator denominator denominatorPositive * denominator =
        (numerator : Rational) :=
      rationalLiteral_mul_denominator numerator denominator
        denominatorPositive
    _ = ((numerator : Rational) / denominator) * denominator :=
      (RFAP.ExplicitField.div_mul_cancel _
        (rationalNatCastNonzero denominatorPositive)).symm

private theorem rationalLiteral_denominator_one (numerator : Int) :
    rationalLiteral numerator 1 (by decide) = (numerator : Rational) := by
  calc
    rationalLiteral numerator 1 (by decide) =
        rationalLiteral numerator 1 (by decide) * 1 :=
      (RFAP.ConstructiveFraction.mul_one_direct _).symm
    _ = (numerator : Rational) :=
      rationalLiteral_mul_denominator numerator 1 (by decide)

def q₃ : Gaussian :=
  ⟨rationalLiteral (-3) 1 (by decide), rationalLiteral 0 1 (by decide)⟩
def s₁ : Gaussian :=
  ⟨rationalLiteral 4 15 (by decide), rationalLiteral 2 15 (by decide)⟩
def s₂ : Gaussian :=
  ⟨rationalLiteral 1 24 (by decide), rationalLiteral 7 24 (by decide)⟩

/-- The two roots of the Triple-spread equation, retained internally so that
the two quadrance pairs can be recovered without selecting a square root. -/
def firstThirdSpread : Gaussian :=
  ⟨rationalLiteral (-1) 40 (by decide),
    rationalLiteral (-3) 40 (by decide)⟩

def secondThirdSpread : Gaussian :=
  ⟨rationalLiteral 271 360 (by decide),
    rationalLiteral 71 120 (by decide)⟩

def firstQ₁ : Gaussian :=
  ⟨rationalLiteral 8 1 (by decide), rationalLiteral (-8) 1 (by decide)⟩
def firstQ₂ : Gaussian :=
  ⟨rationalLiteral 11 1 (by decide), rationalLiteral 2 1 (by decide)⟩

def secondQ₁ : Gaussian :=
  ⟨rationalLiteral (-10872) 11881 (by decide),
    rationalLiteral 2232 11881 (by decide)⟩

def secondQ₂ : Gaussian :=
  ⟨rationalLiteral (-7929) 11881 (by decide),
    rationalLiteral (-7578) 11881 (by decide)⟩

/-- The false second pair printed in the source, retained for the executable
countercheck below. -/
def printedSecondQ₁ : Gaussian :=
  ⟨rationalLiteral 10872 11881 (by decide),
    rationalLiteral 2232 11881 (by decide)⟩

def printedSecondQ₂ : Gaussian :=
  ⟨rationalLiteral 7929 11881 (by decide),
    rationalLiteral (-7578) 11881 (by decide)⟩

/-- The three fixed inputs, in the source's ordinary fraction notation. -/
theorem input_values :
    q₃ = ⟨-3, 0⟩ ∧
      s₁ = ⟨(4 : Rational) / 15, (2 : Rational) / 15⟩ ∧
      s₂ = ⟨(1 : Rational) / 24, (7 : Rational) / 24⟩ := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · change rationalLiteral (-3) 1 (by decide) = (-3 : Rational)
      exact rationalLiteral_denominator_one (-3)
    · change rationalLiteral 0 1 (by decide) = (0 : Rational)
      exact rationalLiteral_denominator_one 0
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div 4 15 (by decide)
    · exact rationalLiteral_eq_div 2 15 (by decide)
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div 1 24 (by decide)
    · exact rationalLiteral_eq_div 7 24 (by decide)

/-- The two third-spread roots in ordinary fraction notation. -/
theorem third_spread_values :
    firstThirdSpread =
        ⟨(-1 : Rational) / 40, (-3 : Rational) / 40⟩ ∧
      secondThirdSpread =
        ⟨(271 : Rational) / 360, (71 : Rational) / 120⟩ := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div (-1) 40 (by decide)
    · exact rationalLiteral_eq_div (-3) 40 (by decide)
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div 271 360 (by decide)
    · exact rationalLiteral_eq_div 71 120 (by decide)

/-- The two corrected quadrance pairs in ordinary fraction notation. -/
theorem quadrance_values :
    (firstQ₁ = ⟨8, -8⟩ ∧ firstQ₂ = ⟨11, 2⟩) ∧
      (secondQ₁ =
          ⟨((-10872 : Int) : Rational) / 11881,
            (2232 : Rational) / 11881⟩ ∧
        secondQ₂ =
          ⟨((-7929 : Int) : Rational) / 11881,
            ((-7578 : Int) : Rational) / 11881⟩) := by
  constructor
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext
      · exact rationalLiteral_denominator_one 8
      · exact rationalLiteral_denominator_one (-8)
    · apply RFAP.ConstructiveGaussian.Gaussian.ext
      · exact rationalLiteral_denominator_one 11
      · exact rationalLiteral_denominator_one 2
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext
      · exact rationalLiteral_eq_div (-10872) 11881 (by decide)
      · exact rationalLiteral_eq_div 2232 11881 (by decide)
    · apply RFAP.ConstructiveGaussian.Gaussian.ext
      · exact rationalLiteral_eq_div (-7929) 11881 (by decide)
      · exact rationalLiteral_eq_div (-7578) 11881 (by decide)

/-- The source's uncorrected second pair, in ordinary fraction notation. -/
theorem printed_quadrance_values :
    printedSecondQ₁ =
        ⟨(10872 : Rational) / 11881, (2232 : Rational) / 11881⟩ ∧
      printedSecondQ₂ =
        ⟨(7929 : Rational) / 11881,
          ((-7578 : Int) : Rational) / 11881⟩ := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div 10872 11881 (by decide)
    · exact rationalLiteral_eq_div 2232 11881 (by decide)
  · apply RFAP.ConstructiveGaussian.Gaussian.ext
    · exact rationalLiteral_eq_div 7929 11881 (by decide)
    · exact rationalLiteral_eq_div (-7578) 11881 (by decide)

private theorem eq_of_mul_eq_mul_left
    {left right factor : Gaussian} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    factorNonzero
  calc
    left * factor = factor * left :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm left factor
    _ = factor * right := productsEqual
    _ = right * factor :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm factor right

private theorem root_sum :
    firstThirdSpread + secondThirdSpread =
      2 * (s₁ + s₂) - 4 * s₁ * s₂ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem root_product :
    (s₁ + s₂) ^ 2 - 2 * (s₁ ^ 2 + s₂ ^ 2) =
      -(firstThirdSpread * secondThirdSpread) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem firstThirdSpreadNonzero : firstThirdSpread ≠ 0 := by
  intro zero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
  exact (by decide : firstThirdSpread.re ≠ 0) realZero

private theorem secondThirdSpreadNonzero : secondThirdSpread ≠ 0 := by
  intro zero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
  exact (by decide : secondThirdSpread.re ≠ 0) realZero

private theorem first_solution_products :
    firstThirdSpread * firstQ₁ = s₁ * q₃ ∧
      firstThirdSpread * firstQ₂ = s₂ * q₃ := by
  constructor <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem second_solution_products :
    secondThirdSpread * secondQ₁ = s₁ * q₃ ∧
      secondThirdSpread * secondQ₂ = s₂ * q₃ := by
  constructor <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

private theorem factorization_identity
    {K : Type*} [RFAP.ExplicitField K]
    (firstSpread secondSpread firstRoot secondRoot thirdSpread : K)
    (rootSum :
      firstRoot + secondRoot =
        2 * (firstSpread + secondSpread) -
          4 * firstSpread * secondSpread)
    (rootProduct :
      (firstSpread + secondSpread) ^ 2 -
          2 * (firstSpread ^ 2 + secondSpread ^ 2) =
        -(firstRoot * secondRoot)) :
    tripleSpreadFunction firstSpread secondSpread thirdSpread =
      -((thirdSpread - firstRoot) * (thirdSpread - secondRoot)) := by
  calc
    tripleSpreadFunction firstSpread secondSpread thirdSpread =
        -thirdSpread ^ 2 +
          (2 * (firstSpread + secondSpread) -
            4 * firstSpread * secondSpread) * thirdSpread +
          ((firstSpread + secondSpread) ^ 2 -
            2 * (firstSpread ^ 2 + secondSpread ^ 2)) := by
      unfold tripleSpreadFunction
      ring1
    _ = -thirdSpread ^ 2 +
        (firstRoot + secondRoot) * thirdSpread -
          firstRoot * secondRoot := by
      rw [rootSum, rootProduct]
      ring1
    _ = -((thirdSpread - firstRoot) *
        (thirdSpread - secondRoot)) := by ring1

/-- The Triple-spread equation is exactly a quadratic with the two displayed
Gaussian-rational roots. -/
theorem triple_spread_factorization (thirdSpread : Gaussian) :
    SpreadTriple s₁ s₂ thirdSpread ↔
      (thirdSpread - firstThirdSpread) *
        (thirdSpread - secondThirdSpread) = 0 := by
  have identity :
      tripleSpreadFunction s₁ s₂ thirdSpread =
        -((thirdSpread - firstThirdSpread) *
          (thirdSpread - secondThirdSpread)) :=
    factorization_identity s₁ s₂ firstThirdSpread secondThirdSpread
      thirdSpread root_sum root_product
  constructor
  · intro spreadTriple
    unfold SpreadTriple at spreadTriple
    have negativeProductZero :
        -((thirdSpread - firstThirdSpread) *
          (thirdSpread - secondThirdSpread)) = 0 := by
      calc
        -((thirdSpread - firstThirdSpread) *
            (thirdSpread - secondThirdSpread)) =
          tripleSpreadFunction s₁ s₂ thirdSpread := identity.symm
        _ = 0 := spreadTriple
    exact neg_eq_zero.mp negativeProductZero
  · intro productZero
    unfold SpreadTriple
    calc
      tripleSpreadFunction s₁ s₂ thirdSpread =
          -((thirdSpread - firstThirdSpread) *
            (thirdSpread - secondThirdSpread)) := identity
      _ = 0 := by rw [productZero]; exact neg_zero

/-- The two possible third spreads, obtained by direct finite factor
elimination rather than a selected quadratic root. -/
theorem third_spread_alternatives (thirdSpread : Gaussian)
    (spreadTriple : SpreadTriple s₁ s₂ thirdSpread) :
    thirdSpread = firstThirdSpread ∨
      thirdSpread = secondThirdSpread := by
  have factored := (triple_spread_factorization thirdSpread).1 spreadTriple
  by_cases firstFactorZero : thirdSpread - firstThirdSpread = 0
  · exact Or.inl (sub_eq_zero.mp firstFactorZero)
  · have secondFactorZero : thirdSpread - secondThirdSpread = 0 := by
      by_cases zero : thirdSpread - secondThirdSpread = 0
      · exact zero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactorZero zero) factored)
    exact Or.inr (sub_eq_zero.mp secondFactorZero)

/-- Exercise 10.12.  The two premises are the denominator-free Spread-law
relations with the printed `Q₃`, `s₁`, and `s₂`.  They force exactly the first
quadrance pair in the source and the sign-corrected second pair. -/
theorem exercise_10_12
    (q₁ q₂ thirdSpread : Gaussian)
    (spreadTriple : SpreadTriple s₁ s₂ thirdSpread)
    (firstSpreadLaw : s₁ * q₃ = thirdSpread * q₁)
    (secondSpreadLaw : s₂ * q₃ = thirdSpread * q₂) :
    (q₁ = firstQ₁ ∧ q₂ = firstQ₂) ∨
      (q₁ = secondQ₁ ∧ q₂ = secondQ₂) := by
  rcases third_spread_alternatives thirdSpread spreadTriple with
    firstRoot | secondRoot
  · rw [firstRoot] at firstSpreadLaw secondSpreadLaw
    apply Or.inl
    constructor
    · apply eq_of_mul_eq_mul_left firstThirdSpreadNonzero
      calc
        firstThirdSpread * q₁ = s₁ * q₃ := firstSpreadLaw.symm
        _ = firstThirdSpread * firstQ₁ := first_solution_products.1.symm
    · apply eq_of_mul_eq_mul_left firstThirdSpreadNonzero
      calc
        firstThirdSpread * q₂ = s₂ * q₃ := secondSpreadLaw.symm
        _ = firstThirdSpread * firstQ₂ := first_solution_products.2.symm
  · rw [secondRoot] at firstSpreadLaw secondSpreadLaw
    apply Or.inr
    constructor
    · apply eq_of_mul_eq_mul_left secondThirdSpreadNonzero
      calc
        secondThirdSpread * q₁ = s₁ * q₃ := firstSpreadLaw.symm
        _ = secondThirdSpread * secondQ₁ :=
          second_solution_products.1.symm
    · apply eq_of_mul_eq_mul_left secondThirdSpreadNonzero
      calc
        secondThirdSpread * q₂ = s₂ * q₃ := secondSpreadLaw.symm
        _ = secondThirdSpread * secondQ₂ :=
          second_solution_products.2.symm

/-- Both corrected pairs really satisfy the Triple-spread and Spread-law data. -/
theorem displayed_solutions :
    (SpreadTriple s₁ s₂ firstThirdSpread ∧
      s₁ * q₃ = firstThirdSpread * firstQ₁ ∧
      s₂ * q₃ = firstThirdSpread * firstQ₂) ∧
    (SpreadTriple s₁ s₂ secondThirdSpread ∧
      s₁ * q₃ = secondThirdSpread * secondQ₁ ∧
      s₂ * q₃ = secondThirdSpread * secondQ₂) := by
  constructor
  · refine ⟨(triple_spread_factorization firstThirdSpread).2 ?_,
      first_solution_products.1.symm, first_solution_products.2.symm⟩
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  · refine ⟨(triple_spread_factorization secondThirdSpread).2 ?_,
      second_solution_products.1.symm, second_solution_products.2.symm⟩
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero]

/-- The source's second pair has both real-part signs wrong.  Already its
first displayed Spread-law cross-product fails. -/
theorem printed_second_pair_counterexample :
    ¬ (s₁ * q₃ = secondThirdSpread * printedSecondQ₁ ∧
      s₂ * q₃ = secondThirdSpread * printedSecondQ₂) := by
  rintro ⟨firstPrintedLaw, _⟩
  have realPartsEqual :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re firstPrintedLaw
  exact (by decide : (s₁ * q₃).re ≠
    (secondThirdSpread * printedSecondQ₁).re) realPartsEqual

end ExerciseTenTwelve

end DivineProportions
