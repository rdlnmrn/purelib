module

public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Remainder

namespace Purelib.Data.Nat.Divisibility

/-- Every natural number divides itself with the displayed unit factor. -/
public theorem refl (value : Nat) : value ∣ value := ⟨1, (Nat.mul_one value).symm⟩

/-- Every natural number divides zero with the displayed zero factor. -/
public theorem zero (value : Nat) : value ∣ 0 := ⟨0, (Nat.mul_zero value).symm⟩

/-- Two retained natural divisibility witnesses compose by multiplying factors.

The factor from the first witness precedes the factor from the second
witness. Their product certifies divisibility of the final displayed value. -/
public theorem trans {first middle last : Nat} (forward : first ∣ middle)
    (next : middle ∣ last) : first ∣ last := by
  obtain ⟨firstFactor, firstEquation⟩ := forward
  obtain ⟨nextFactor, nextEquation⟩ := next
  refine ⟨firstFactor * nextFactor, ?_⟩
  rw [nextEquation, firstEquation, Multiplication.mul_assoc]

/-- A common natural divisor divides the sum of the two displayed multiples. -/
public theorem add {divisor first second : Nat} (left : divisor ∣ first)
    (right : divisor ∣ second) : divisor ∣ first + second := by
  obtain ⟨leftFactor, leftEquation⟩ := left
  obtain ⟨rightFactor, rightEquation⟩ := right
  refine ⟨leftFactor + rightFactor, ?_⟩
  rw [leftEquation, rightEquation, Multiplication.left_distrib]

/-- A displayed divisor remains a divisor after multiplying on the right. -/
public theorem mul_right {divisor value : Nat} (retained : divisor ∣ value)
    (factor : Nat) : divisor ∣ value * factor := by
  obtain ⟨retainedFactor, retainedEquation⟩ := retained
  refine ⟨retainedFactor * factor, ?_⟩
  rw [retainedEquation, Multiplication.mul_assoc]

/-- A natural divisor does not exceed a positive displayed multiple.

The retained factor cannot be zero when the multiple is positive; its
successor form displays the divisor as a summand of that multiple. -/
public theorem le_of_dvd {divisor value : Nat} (positive : 0 < value)
    (retained : divisor ∣ value) : divisor ≤ value := by
  obtain ⟨factor, equation⟩ := retained
  cases factor with
  | zero =>
      have vanishes : value = 0 := equation.trans (Nat.mul_zero divisor)
      rw [vanishes] at positive
      exact (Nat.not_lt_zero _ positive).elim
  | succ factor =>
      rw [Nat.mul_succ] at equation
      calc
        divisor ≤ divisor * factor + divisor := Nat.le_add_left _ _
        _ = value := equation.symm

/-- Mutual natural divisibility identifies the two displayed values.

Zero multiples are handled by their retained witnesses. For two positive
values, each witness supplies one of the opposing natural bounds. -/
public theorem antisymm {first second : Nat} (forward : first ∣ second)
    (reverse : second ∣ first) : first = second := by
  cases first with
  | zero =>
      obtain ⟨factor, equation⟩ := forward
      exact (equation.trans (Nat.zero_mul factor)).symm
  | succ first =>
      cases second with
      | zero =>
          obtain ⟨factor, equation⟩ := reverse
          exact equation.trans (Nat.zero_mul factor)
      | succ second =>
          exact Nat.le_antisymm (le_of_dvd (Nat.zero_lt_succ _) forward)
            (le_of_dvd (Nat.zero_lt_succ _) reverse)

/-- A natural divisor of one is one. -/
public theorem eq_one_of_dvd_one {value : Nat} (retained : value ∣ 1) : value = 1 :=
  antisymm retained ⟨value, (Nat.one_mul value).symm⟩

/-- A common natural divisor divides the truncated difference.

Subtracting the retained factors gives a factor for the difference, including
the case where natural subtraction truncates it to zero. -/
public theorem sub {divisor first second : Nat} (left : divisor ∣ first)
    (right : divisor ∣ second) : divisor ∣ first - second := by
  obtain ⟨leftFactor, leftEquation⟩ := left
  obtain ⟨rightFactor, rightEquation⟩ := right
  refine ⟨leftFactor - rightFactor, ?_⟩
  rw [leftEquation, rightEquation, Multiplication.left_sub_distrib]

/-- Cancel a positive common right factor from a natural divisibility witness.

The original displayed multiplier is retained. Reassociation and ordinary
natural multiplication cancellation certify the resulting divisibility. -/
public theorem of_mul_dvd_mul_right {factor first second : Nat}
    (positive : 0 < factor) (retained : first * factor ∣ second * factor) :
    first ∣ second := by
  obtain ⟨multiplier, equation⟩ := retained
  rw [Multiplication.mul_assoc, Nat.mul_comm factor multiplier,
    ← Multiplication.mul_assoc] at equation
  exact ⟨multiplier, Nat.eq_of_mul_eq_mul_right positive equation⟩

/-- A displayed natural divisibility witness gives zero remainder.

The original multiplier identifies the dividend with a multiple of the
retained divisor. The original remainder procedure removes those same
copies and leaves its zero tail, including a zero divisor. -/
public theorem mod_eq_zero_of_dvd {divisor value : Nat}
    (retained : divisor ∣ value) : value % divisor = 0 := by
  obtain ⟨factor, equation⟩ := retained
  rw [equation]
  calc
    (divisor * factor) % divisor = (divisor * factor + 0) % divisor :=
      congrArg (· % divisor) (Nat.add_zero (divisor * factor)).symm
    _ = 0 % divisor := Remainder.mul_add_mod divisor factor 0
    _ = 0 := rfl

/-- Zero natural remainder supplies the original quotient as a divisibility witness.

The original quotient and divisor reconstruct the dividend in the retained
remainder equation. When that same remainder is zero, this gives the
required multiplicative witness without another search or factor selection. -/
public theorem of_mod_eq_zero {divisor value : Nat}
    (vanishes : value % divisor = 0) : divisor ∣ value := by
  refine ⟨value / divisor, ?_⟩
  have reconstruct := Division.mod_add_div value divisor
  rewrite [vanishes, Nat.zero_add] at reconstruct
  exact reconstruct.symm

/-- Decide natural divisibility by the original zero-remainder test.

The same quotient and remainder operations supply the two correctness
certificates. The decision procedure retains the original equality test
and transports its outcomes without proposition equality. -/
@[inline, expose, reducible] public def decidable (divisor value : Nat) :
    Decidable (divisor ∣ value) :=
  decidable_of_decidable_of_iff
    ⟨of_mod_eq_zero, mod_eq_zero_of_dvd⟩

/-- Every retained entry of a natural list divides its product.

The head uses the exact retained tail product as its factor. A tail
occurrence transports its original factor through the same head product;
no new enumeration or product calculation is introduced. -/
public theorem mem_dvd_prod {value : Nat} : ∀ {values : List Nat},
    value ∈ values → value ∣ values.prod
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      cases member with
      | head => exact ⟨tail.prod, rfl⟩
      | tail _ tailMember =>
          obtain ⟨factor, equation⟩ := mem_dvd_prod tailMember
          refine ⟨head * factor, ?_⟩
          change head * tail.prod = value * (head * factor)
          calc
            head * tail.prod = head * (value * factor) :=
              congrArg (head * ·) equation
            _ = (head * value) * factor := (Multiplication.mul_assoc _ _ _).symm
            _ = (value * head) * factor :=
              congrArg (· * factor) (Nat.mul_comm head value)
            _ = value * (head * factor) := Multiplication.mul_assoc _ _ _

end Purelib.Data.Nat.Divisibility
