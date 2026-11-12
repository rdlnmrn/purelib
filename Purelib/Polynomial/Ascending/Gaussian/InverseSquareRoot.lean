module

public import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Natural
public import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
public import Purelib.Polynomial.Ascending.Gaussian.Derivative
import Purelib.Algebra.NatCast
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Finite normalized inverse-square-root coefficients

The retained table starts with one. Each next coefficient solves the next
coefficient of `2 Q H′ + Q′ H = 0`, using the nonzero constant coefficient of
the original radicand. The table is finite and every extension retains its
complete original prefix. The certificates below concern these exact finite
recurrences; they do not assert an analytic expansion or a completed series.
-/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.InverseSquareRoot

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Natural (naturalGaussian naturalGaussian_ne_zero)
open Purelib.Data.Gaussian.Natural (naturalGaussian_eq_natCast)
open Purelib.Polynomial.Ascending.Gaussian.Coefficient (coefficient coefficientList)
open Purelib.Algebra
open Purelib.Algebra.FiniteSum

/-- The previously determined terms in the degree-`n-1` coefficient equation.

The finite index reads positive radicand degrees `j+1`; its jet index is
strictly below `n`, so no next coefficient is recomputed while producing it. -/
@[expose] def previous (radicand jet : CoefficientPolynomial) (degree : Nat) : Canonical :=
  sumFin fun index : Fin degree =>
    naturalGaussian (2 * degree - (index.val + 1)) * coefficient radicand (index.val + 1) *
      coefficient jet (degree - (index.val + 1))

/-- The cleared finite coefficient equation for the normalized inverse root.

For positive `n`, this is the coefficient at degree `n-1` of
`2 Q H′ + Q′ H`, with the unknown `h_n` isolated from the earlier entries. -/
@[expose] def residual (radicand jet : CoefficientPolynomial) (degree : Nat) : Canonical :=
  (naturalGaussian (2 * degree) * coefficient radicand 0) * coefficient jet degree +
    previous radicand jet degree

/-- Produce the next coefficient from the identical retained earlier table. -/
@[expose] def next (radicand jet : CoefficientPolynomial) (degree : Nat) : Canonical :=
  -previous radicand jet degree / (naturalGaussian (2 * degree) * coefficient radicand 0)

/-- Build the constant term and the requested number of positive coefficients.

Every successor appends one computed entry to the actual preceding table.
No earlier entry is obtained by invoking the builder again inside the sum. -/
@[expose] def coefficients (radicand : CoefficientPolynomial) : Nat → List Canonical
  | 0 => [1]
  | order + 1 =>
      let retained := coefficients radicand order
      retained ++ [next radicand ⟨retained⟩ (order + 1)]

/-- The complete table construction retains its original successor prefix literally. -/
theorem coefficients_succ (radicand : CoefficientPolynomial) (order : Nat) :
    coefficients radicand (order + 1) =
      coefficients radicand order ++ [next radicand ⟨coefficients radicand order⟩ (order + 1)] := rfl

private theorem read_append_before : ∀ (left right : List Canonical) (degree : Nat),
    degree < left.length → coefficientList (left ++ right) degree = coefficientList left degree
  | [], _, _, bound => (Nat.not_lt_zero _ bound).elim
  | _ :: _, _, 0, _ => rfl
  | _ :: tail, right, degree + 1, bound =>
      read_append_before tail right degree (Nat.lt_of_succ_lt_succ bound)

private theorem read_append_last : ∀ (retained : List Canonical) (value : Canonical),
    coefficientList (retained ++ [value]) retained.length = value
  | [], _ => rfl
  | _ :: tail, value => read_append_last tail value

/-- The finite cache contains exactly the constant and the requested positive entries. -/
theorem coefficients_length (radicand : CoefficientPolynomial) : ∀ order,
    (coefficients radicand order).length = order + 1
  | 0 => rfl
  | order + 1 => by
      rewrite [coefficients_succ, List.length_append, coefficients_length]
      rfl

/-- A successor cache reads every original bounded entry from the retained prefix. -/
theorem coefficient_succ_before (radicand : CoefficientPolynomial) (order degree : Nat)
    (bound : degree ≤ order) :
    coefficient ⟨coefficients radicand (order + 1)⟩ degree =
      coefficient ⟨coefficients radicand order⟩ degree := by
  apply read_append_before
  rewrite [coefficients_length]
  exact Nat.lt_succ_of_le bound

/-- The last cache entry is the next coefficient computed from its identical prefix. -/
theorem coefficient_succ_last (radicand : CoefficientPolynomial) (order : Nat) :
    coefficient ⟨coefficients radicand (order + 1)⟩ (order + 1) =
      next radicand ⟨coefficients radicand order⟩ (order + 1) := by
  change coefficientList (coefficients radicand order ++ [_]) (order + 1) = _
  rewrite [← coefficients_length radicand order]
  exact read_append_last _ _

/-- Increasing the requested order preserves every already retained coefficient. -/
theorem coefficient_prefix (radicand : CoefficientPolynomial) {earlier later degree : Nat}
    (order : earlier ≤ later) (bound : degree ≤ earlier) :
    coefficient ⟨coefficients radicand later⟩ degree =
      coefficient ⟨coefficients radicand earlier⟩ degree := by
  induction later with
  | zero =>
      have zero : earlier = 0 := Nat.eq_zero_of_le_zero order
      subst earlier
      rfl
  | succ later inductionHypothesis =>
      by_cases same : earlier = later + 1
      · subst earlier
        rfl
      · have preceding : earlier ≤ later := by omega
        exact (coefficient_succ_before radicand later degree (Nat.le_trans bound preceding)).trans
          (inductionHypothesis preceding)

/-- The normalized finite inverse-root table starts with the exact scalar one. -/
theorem coefficient_zero (radicand : CoefficientPolynomial) (order : Nat) :
    coefficient ⟨coefficients radicand order⟩ 0 = 1 :=
  coefficient_prefix radicand (Nat.zero_le order) (Nat.le_refl 0)

private theorem previous_congr (radicand left right : CoefficientPolynomial) (degree : Nat)
    (equal : ∀ index, index < degree → coefficient left index = coefficient right index) :
    previous radicand left degree = previous radicand right degree := by
  apply sumFin_congr
  intro index
  have earlier : degree - (index.val + 1) < degree := by omega
  rewrite [equal _ earlier]
  rfl

private theorem denominator_nonzero (radicand : CoefficientPolynomial)
    (nonzero : coefficient radicand 0 ≠ 0) {degree : Nat} (positive : 0 < degree) :
    naturalGaussian (2 * degree) * coefficient radicand 0 ≠ 0 :=
  ExplicitField.mul_ne_zero (naturalGaussian_ne_zero ⟨2 * degree, by omega⟩) nonzero

/-- Every positive coefficient through the requested order satisfies its cleared equation.

The proof follows the actual prefix extensions. The only divisions are by
positive natural weights times the original nonzero radicand constant. -/
theorem coefficients_residual (radicand : CoefficientPolynomial)
    (nonzero : coefficient radicand 0 ≠ 0) : ∀ (order degree : Nat),
    0 < degree → degree ≤ order → residual radicand ⟨coefficients radicand order⟩ degree = 0
  | 0, degree, positive, bound => by omega
  | order + 1, degree, positive, bound => by
      by_cases last : degree = order + 1
      · subst degree
        have same := previous_congr radicand ⟨coefficients radicand (order + 1)⟩
          ⟨coefficients radicand order⟩ (order + 1)
          (fun index bound => coefficient_succ_before radicand order index (Nat.le_of_lt_succ bound))
        unfold residual
        rewrite [coefficient_succ_last, same]
        unfold next
        have cancel := ExplicitField.div_mul_cancel
          (-previous radicand ⟨coefficients radicand order⟩ (order + 1))
          (denominator_nonzero radicand nonzero (by omega : 0 < order + 1))
        calc
          _ = (-previous radicand ⟨coefficients radicand order⟩ (order + 1) /
              (naturalGaussian (2 * (order + 1)) * coefficient radicand 0)) *
              (naturalGaussian (2 * (order + 1)) * coefficient radicand 0) +
              previous radicand ⟨coefficients radicand order⟩ (order + 1) := by ring1
          _ = 0 := by rewrite [cancel]; exact Canonical.neg_add_cancel _
      · have preceding : degree ≤ order := by omega
        unfold residual
        rewrite [coefficient_succ_before radicand order degree preceding,
          previous_congr radicand ⟨coefficients radicand (order + 1)⟩
            ⟨coefficients radicand order⟩ degree
            (fun index smaller => coefficient_succ_before radicand order index (by omega))]
        exact coefficients_residual radicand nonzero order degree positive preceding

/-- The exact finite normalized inverse-root coefficient contract.

The physical table length, constant entry and every required cleared equation
refer to the same supplied table and radicand, with the actual requested order. -/
@[expose] def Specification (radicand : CoefficientPolynomial) (order : Nat) (jet : CoefficientPolynomial) : Prop :=
  jet.coefficients.length = order + 1 ∧ coefficient jet 0 = 1 ∧
    ∀ degree, 0 < degree → degree ≤ order → residual radicand jet degree = 0

/-- The finite recurrence determines every required coefficient uniquely.

Both tables satisfy the same original radicand equations and start with one.
Each positive step cancels its proved nonzero original constant-weight factor. -/
theorem Specification.coefficient_eq {radicand left right : CoefficientPolynomial} {order : Nat}
    (leftSpecification : Specification radicand order left)
    (rightSpecification : Specification radicand order right)
    (nonzero : coefficient radicand 0 ≠ 0) (degree : Nat) (bound : degree ≤ order) :
    coefficient left degree = coefficient right degree := by
  have through : ∀ last, last ≤ order → ∀ index, index ≤ last →
      coefficient left index = coefficient right index := by
    intro last
    induction last with
    | zero =>
        intro _ index indexBound
        have zero : index = 0 := Nat.eq_zero_of_le_zero indexBound
        subst index
        exact leftSpecification.2.1.trans rightSpecification.2.1.symm
    | succ last inductionHypothesis =>
        intro lastBound index indexBound
        by_cases isLast : index = last + 1
        · subst index
          have preceding : last ≤ order := by omega
          have same := previous_congr radicand left right (last + 1)
            (fun index smaller => inductionHypothesis preceding index (Nat.le_of_lt_succ smaller))
          have leftEquation := leftSpecification.2.2 (last + 1) (by omega) lastBound
          have rightEquation := rightSpecification.2.2 (last + 1) (by omega) lastBound
          unfold residual at leftEquation rightEquation
          rewrite [same] at leftEquation
          apply ExplicitField.eq_of_mul_eq_mul_left
            (denominator_nonzero radicand nonzero (degree := last + 1) (by omega))
          have complete := leftEquation.trans rightEquation.symm
          calc
            _ = (naturalGaussian (2 * (last + 1)) * coefficient radicand 0 *
                coefficient left (last + 1) + previous radicand right (last + 1)) -
                previous radicand right (last + 1) := by ring1
            _ = (naturalGaussian (2 * (last + 1)) * coefficient radicand 0 *
                coefficient right (last + 1) + previous radicand right (last + 1)) -
                previous radicand right (last + 1) := congrArg
                  (fun value => value - previous radicand right (last + 1)) complete
            _ = _ := by ring1
        · exact inductionHypothesis (by omega) index (by omega)
  exact through degree bound degree (Nat.le_refl degree)

/-- The actual finite product whose low coefficients certify the normalized inverse square root. -/
@[expose] def product (radicand jet : CoefficientPolynomial) : CoefficientPolynomial :=
  Arithmetic.mul (Arithmetic.mul radicand jet) jet

/-- The finite differential equation before multiplication by its retained inverse-root table.

The original product rule identifies `(QH)′+QH′` with `Q′H+2QH′`.
Using the actual intermediate product keeps its derivative cache explicit. -/
@[expose] def equation (radicand jet : CoefficientPolynomial) : CoefficientPolynomial :=
  Arithmetic.add (Derivative.derivative (Arithmetic.mul radicand jet))
    (Arithmetic.mul radicand (Derivative.derivative jet))

/-- The finite equation's coefficient is exactly the builder's cleared recurrence.

The complementary degree weights combine in one bounded convolution. The
zero endpoint of the second derivative factor is inserted explicitly. -/
theorem equation_coefficient (radicand jet : CoefficientPolynomial) (degree : Nat) :
    coefficient (equation radicand jet) degree = residual radicand jet (degree + 1) := by
  unfold equation
  rewrite [Arithmetic.coefficient_add, Derivative.coefficient_derivative,
    Arithmetic.coefficient_mul, Arithmetic.coefficient_mul]
  have second : Prefix.prefixSum (degree + 1) (fun index =>
        coefficient radicand index * coefficient (Derivative.derivative jet) (degree - index)) =
      Prefix.prefixSum (degree + 2) (fun index =>
        coefficient radicand index * ((degree + 1 - index : Nat) : Canonical) *
          coefficient jet (degree + 1 - index)) := by
    rewrite [Prefix.prefixSum_succ_last (degree + 1) (fun index =>
      coefficient radicand index * ((degree + 1 - index : Nat) : Canonical) *
        coefficient jet (degree + 1 - index))]
    have endpoint : coefficient radicand (degree + 1) * ((degree + 1 - (degree + 1) : Nat) : Canonical) *
        coefficient jet (degree + 1 - (degree + 1)) = 0 := by
      rewrite [Nat.sub_self, Nat.cast_zero, Purelib.Data.Gaussian.Basic.mul_zero,
        Purelib.Data.Gaussian.Basic.zero_mul]
      rfl
    rewrite [endpoint, Purelib.Data.Gaussian.Basic.add_zero]
    apply Prefix.prefixSum_congr
    intro index bound
    rewrite [Derivative.coefficient_derivative,
      show degree - index + 1 = degree + 1 - index by omega]
    ring1
  rewrite [second, ← Prefix.prefixSum_mul_left, ← Prefix.prefixSum_add]
  have collected : Prefix.prefixSum (degree + 2) (fun index =>
        ((degree + 1 : Nat) : Canonical) * (coefficient radicand index *
          coefficient jet (degree + 1 - index)) +
        coefficient radicand index * ((degree + 1 - index : Nat) : Canonical) *
          coefficient jet (degree + 1 - index)) =
      Prefix.prefixSum (degree + 2) (fun index =>
        naturalGaussian (2 * (degree + 1) - index) * coefficient radicand index *
          coefficient jet (degree + 1 - index)) := by
    apply Prefix.prefixSum_congr
    intro index bound
    have weights : (degree + 1) + (degree + 1 - index) = 2 * (degree + 1) - index := by omega
    rewrite [naturalGaussian_eq_natCast]
    calc
      _ = (((degree + 1 : Nat) : Canonical) + ((degree + 1 - index : Nat) : Canonical)) *
          coefficient radicand index * coefficient jet (degree + 1 - index) := by ring1
      _ = _ := by rewrite [← NatCast.add, weights]; rfl
  rewrite [collected, Prefix.prefixSum_succ]
  unfold residual previous
  rewrite [Nat.sub_zero]
  apply congrArg ((naturalGaussian (2 * (degree + 1)) * coefficient radicand 0) *
    coefficient jet (degree + 1) + ·)
  exact (Prefix.sumFin_eq_prefixSum (degree + 1) _).symm

/-- Differentiate the same finite product as the equation times the actual cached table. -/
theorem product_derivative_coefficient (radicand jet : CoefficientPolynomial) (degree : Nat) :
    coefficient (Derivative.derivative (product radicand jet)) degree =
      coefficient (Arithmetic.mul (equation radicand jet) jet) degree := by
  unfold product equation
  rewrite [Derivative.coefficient_derivative_mul, Arithmetic.coefficient_mul_add_left]
  apply congrArg (coefficient
    (Arithmetic.mul (Derivative.derivative (Arithmetic.mul radicand jet)) jet) degree + ·)
  exact Arithmetic.coefficient_mul_swap_tail radicand jet (Derivative.derivative jet) degree

/-- The actual finite product `Q*H²` has the original constant and all other low coefficients zero.

Every positive product coefficient is multiplied by its explicit nonzero
natural degree in the original derivative. Its derivative convolution reads
only previously certified equation coefficients, so no truncated identity is assumed. -/
theorem Specification.product_coefficient {radicand jet : CoefficientPolynomial} {order : Nat}
    (specification : Specification radicand order jet) (degree : Nat) (bound : degree ≤ order) :
    coefficient (product radicand jet) degree = if degree = 0 then coefficient radicand 0 else 0 := by
  cases degree with
  | zero =>
      unfold product
      rewrite [Arithmetic.coefficient_mul, Prefix.prefixSum_succ, Prefix.prefixSum_zero,
        Arithmetic.coefficient_mul, Prefix.prefixSum_succ, Prefix.prefixSum_zero, Nat.sub_zero,
        specification.2.1]
      change (coefficient radicand 0 * 1 + 0) * 1 + 0 = coefficient radicand 0
      ring1
  | succ degree =>
      have derivativeZero : coefficient (Derivative.derivative (product radicand jet)) degree = 0 := by
        rewrite [product_derivative_coefficient, Arithmetic.coefficient_mul]
        exact (Prefix.prefixSum_congr (degree + 1) _ _ (fun index indexBound => by
          rewrite [equation_coefficient,
            specification.2.2 (index + 1) (by omega) (by omega), Purelib.Data.Gaussian.Basic.zero_mul]
          rfl)).trans (Prefix.prefixSum_zero_values (degree + 1))
      rewrite [Derivative.coefficient_derivative] at derivativeZero
      change coefficient (product radicand jet) (degree + 1) = 0
      have naturalNonzero : ((degree + 1 : Nat) : Canonical) ≠ 0 := by
        rewrite [← naturalGaussian_eq_natCast]
        exact naturalGaussian_ne_zero ⟨degree + 1, by omega⟩
      exact ExplicitField.eq_of_mul_eq_mul_left naturalNonzero
        (derivativeZero.trans (Purelib.Data.Gaussian.Basic.mul_zero _).symm)

/-- The actual finite product is the original constant modulo the first omitted degree.

Equality below `order+1` is derived from the same retained table's coefficient
equations. The caller supplies no truncated square-root identity. -/
theorem Specification.product_truncation {radicand jet : CoefficientPolynomial} {order : Nat}
    (specification : Specification radicand order jet) :
    Coefficient.EqualBelow (order + 1) (product radicand jet)
      (Basic.constant (coefficient radicand 0)) := by
  intro degree below
  rewrite [Coefficient.coefficient_constant]
  exact specification.product_coefficient degree (Nat.le_of_lt_succ below)

/-- The actual retained finite product evaluates to the radicand times the square of the supplied table. -/
theorem product_eval (radicand jet : CoefficientPolynomial) (input : Canonical) :
    Evaluation.eval (product radicand jet) input =
      Evaluation.eval radicand input * (Evaluation.eval jet input) ^ 2 := by
  unfold product
  rewrite [Evaluation.eval_mul, Evaluation.eval_mul, pow_two]
  ring1

/-- The exact inverse-root residual factors by its first omitted degree through its original finite tail.

The product is computed once from the supplied radicand and table. The
original coefficient equations prove that every discarded low entry is zero;
the output stores the literal higher-degree tail and its full evaluation
identity. No caller-supplied divisibility or completed series is used.
-/
theorem Specification.remainder_identity {radicand jet : CoefficientPolynomial} {order : Nat}
    (specification : Specification radicand order jet) (input : Canonical) :
    coefficient radicand 0 - Evaluation.eval radicand input * (Evaluation.eval jet input) ^ 2 =
      input ^ (order + 1) * Evaluation.eval (Arithmetic.divideByPower (order + 1)
        (Arithmetic.add (Basic.constant (coefficient radicand 0))
          (Arithmetic.scale (-1) (product radicand jet)))) input := by
  let retainedProduct := product radicand jet
  let residual := Arithmetic.add (Basic.constant (coefficient radicand 0))
    (Arithmetic.scale (-1) retainedProduct)
  let tail := Arithmetic.divideByPower (order + 1) residual
  have zero (index : Nat) (below : index < order + 1) : coefficient residual index = 0 := by
    change coefficient (Arithmetic.add (Basic.constant (coefficient radicand 0))
      (Arithmetic.scale (-1) (product radicand jet))) index = 0
    rewrite [Arithmetic.coefficient_add, Arithmetic.coefficient_scale,
      specification.product_coefficient index (Nat.le_of_lt_succ below), Coefficient.coefficient_constant]
    by_cases atZero : index = 0
    · rewrite [if_pos atZero]
      ring1
    · rewrite [if_neg atZero]
      ring1
  have factored := Evaluation.eval_eq_power_mul_divideByPower residual (order + 1) zero input
  calc
    _ = Evaluation.eval residual input := by
      change _ = Evaluation.eval (Arithmetic.add (Basic.constant (coefficient radicand 0))
        (Arithmetic.scale (-1) (product radicand jet))) input
      rewrite [Evaluation.eval_add, Evaluation.eval_scale, Evaluation.eval_constant, product_eval]
      ring1
    _ = _ := factored

/-- An original finite polynomial tail whose retained power gives the exact supplied inverse-root residual. -/
abbrev ResidualFactor (radicand : CoefficientPolynomial) (order : Nat) (jet : CoefficientPolynomial) :=
  { tail : CoefficientPolynomial // ∀ input : Canonical,
    coefficient radicand 0 - Evaluation.eval radicand input * (Evaluation.eval jet input) ^ 2 =
      input ^ (order + 1) * Evaluation.eval tail input }

/-- Retain the actual finite residual tail and its complete factorization certificate.

The supplied table and radicand determine the product once. Execution drops
only the certified zero prefix; the original identity theorem supplies the
same tail's specification without rebuilding an executable product.
-/
@[expose] def Specification.remainder {radicand jet : CoefficientPolynomial} {order : Nat}
    (specification : Specification radicand order jet) : ResidualFactor radicand order jet :=
  let retainedProduct := product radicand jet
  let residual := Arithmetic.add (Basic.constant (coefficient radicand 0))
    (Arithmetic.scale (-1) retainedProduct)
  ⟨Arithmetic.divideByPower (order + 1) residual, specification.remainder_identity⟩

/-- The certified residual factor is the actual dropped coefficient tail of the same finite product calculation. -/
theorem Specification.remainder_coefficients {radicand jet : CoefficientPolynomial} {order : Nat}
    (specification : Specification radicand order jet) :
    specification.remainder.val.coefficients =
      (Arithmetic.add (Basic.constant (coefficient radicand 0))
        (Arithmetic.scale (-1) (product radicand jet))).coefficients.drop (order + 1) := rfl

/-- Construct a certified finite coefficient table from a nonzero original constant.

The subtype retains the original ascending Gaussian polynomial; it introduces
no second polynomial or jet representation. -/
@[expose] def build (radicand : CoefficientPolynomial) (order : Nat)
    (nonzero : coefficient radicand 0 ≠ 0) :
    { jet : CoefficientPolynomial // Specification radicand order jet } :=
  ⟨⟨coefficients radicand order⟩, coefficients_length radicand order,
    coefficient_zero radicand order, coefficients_residual radicand nonzero order⟩

/-- The certified constructor retains precisely the computed finite table. -/
theorem build_coefficients (radicand : CoefficientPolynomial) (order : Nat)
    (nonzero : coefficient radicand 0 ≠ 0) :
    (build radicand order nonzero).val.coefficients = coefficients radicand order := rfl

end Purelib.Polynomial.Ascending.Gaussian.InverseSquareRoot
end
