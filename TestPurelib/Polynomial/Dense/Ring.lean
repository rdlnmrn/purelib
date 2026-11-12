module

import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Synthetic
import Purelib.Polynomial.Dense.Division.Synthetic.Map
import Purelib.Polynomial.Dense.Division.Synthetic.Factorization
import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Polynomial.Ascending.Integer.Basic

/-!
# Dense coefficient operations over rings with zero divisors

The retained quadratic pair at parameter zero has a nonzero nilpotent
generator. These clients exercise the original normalization, evaluation and
scaling APIs without a field or cancellation instance.
-/

namespace TestPurelib.Polynomial.Dense.Ring

open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division
open Purelib.Polynomial.Dense

/-- The original two-coordinate algebra with a square-zero generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The actual nonzero nilpotent coordinate, retained without a field instance. -/
private def epsilon : Dual := Pair.generator

/-- A leading nilpotent coefficient and unit constant term. -/
private def polynomial : DensePolynomial Dual := ⟨[epsilon, 1]⟩

/-- The retained generator has a nonzero coordinate. -/
private theorem epsilon_nonzero : epsilon ≠ 0 := by decide +kernel

/-- The retained generator squares to the scalar zero. -/
private theorem epsilon_square_zero : epsilon * epsilon = 0 := by decide +kernel

/-- Scaling may remove a nonzero leading coefficient over the original zero-divisor algebra. -/
private theorem nilpotent_scale_removes_leading :
    DensePolynomial.scale epsilon polynomial = DensePolynomial.constant epsilon := by decide +kernel

/-- The same nilpotent generator evaluates the original table to its unit constant. -/
private theorem nilpotent_evaluation : polynomial.eval epsilon = 1 := by decide +kernel

/-- Normalization before scaling preserves every original coefficient calculation. -/
private theorem arbitrary_scale_normalize (factor : Dual) (input : DensePolynomial Dual) :
    DensePolynomial.scale factor input.normalize = DensePolynomial.scale factor input :=
  DensePolynomial.scale_normalize factor input

/-- The original integer evaluator consumes the same ring operations without a field. -/
private theorem integer_evaluation (point : Dual) : Purelib.Polynomial.Ascending.Integer.Basic.eval [1, 0, 1] point =
    1 + point * (point * 1) := by
  change (1 : Dual) + point * ((0 : Dual) + point * ((1 : Dual) + point * 0)) = _
  rewrite [mul_zero, add_zero, zero_add]
  rfl

/-- The automatic division retains the actual nilpotent quotient coefficients. -/
private theorem nilpotent_quotient : (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).quotient.coeffs =
    [1, epsilon] := by decide +kernel

/-- The automatic division retains its exact zero Horner remainder. -/
private theorem nilpotent_remainder :
    (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).remainder = 0 := by decide +kernel

/-- The same public division reconstructs every original polynomial at every supplied point. -/
private theorem synthetic_reconstruction (input : DensePolynomial Dual) (root point : Dual) :
    input.eval point = (point - root) * (Synthetic.divide input root).quotient.eval point +
      (Synthetic.divide input root).remainder :=
  (Synthetic.divide input root).eval_eq point

/-- Exact coefficient reconstruction retains the entire nilpotent quadratic source. -/
private theorem nilpotent_coefficient_reconstruction :
    Synthetic.reassemble epsilon
      (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).quotient.coeffs
      (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).remainder = [1, 0, 0] :=
  (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).reassemble_eq (by decide +kernel)

/-- Coefficient reconstruction preserves all original zero slots before normalization. -/
private theorem zero_slots_reconstruction :
    Synthetic.reassemble epsilon
      (Synthetic.divide (⟨[0, 0, 0]⟩ : DensePolynomial Dual) epsilon).quotient.coeffs
      (Synthetic.divide (⟨[0, 0, 0]⟩ : DensePolynomial Dual) epsilon).remainder = [0, 0, 0] :=
  (Synthetic.divide (⟨[0, 0, 0]⟩ : DensePolynomial Dual) epsilon).reassemble_eq (by decide +kernel)

/-- The original scalar embedding into a second exact square-zero pair algebra. -/
private def coefficientMap : Dual → Pair Dual 0 := Pair.scalar

/-- Reading the retained real coordinate proves injectivity without a field instance. -/
private theorem coefficientMap_injective : Function.Injective coefficientMap := fun _ _ same =>
  congrArg Pair.re same

/-- The original Horner product maps through rings with actual nonzero nilpotents. -/
private theorem nilpotent_map_mul (left right : DensePolynomial Dual) :
    Map.map coefficientMap (left * right) = Map.map coefficientMap left * Map.map coefficientMap right :=
  Map.map_mul coefficientMap Pair.scalar_zero coefficientMap_injective Pair.scalar_add Pair.scalar_mul left right

/-- Mapping the actual nilpotent scale retains the same normalization and coefficient loss. -/
private theorem nilpotent_map_scale :
    Map.map coefficientMap (DensePolynomial.scale epsilon polynomial) =
      DensePolynomial.scale (coefficientMap epsilon) (Map.map coefficientMap polynomial) :=
  Map.map_scale coefficientMap Pair.scalar_zero coefficientMap_injective Pair.scalar_mul epsilon polynomial

/-- Mapping the actual nilpotent division retains its same two quotient coefficients. -/
private theorem nilpotent_map_quotient :
    (Synthetic.divide (Map.map coefficientMap (⟨[1, 0, 0]⟩ : DensePolynomial Dual))
      (coefficientMap epsilon)).quotient.coeffs = [1, coefficientMap epsilon] := by
  rewrite [Synthetic.map_quotient coefficientMap Pair.scalar_add Pair.scalar_mul]
  change (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).quotient.coeffs.map coefficientMap = _
  rewrite [nilpotent_quotient]
  rfl

/-- The mapped original nilpotent division retains its exact zero remainder. -/
private theorem nilpotent_map_remainder :
    (Synthetic.divide (Map.map coefficientMap (⟨[1, 0, 0]⟩ : DensePolynomial Dual))
      (coefficientMap epsilon)).remainder = 0 := by
  rewrite [Synthetic.map_remainder coefficientMap Pair.scalar_zero Pair.scalar_add Pair.scalar_mul,
    nilpotent_remainder]
  exact Pair.scalar_zero

/-- The original multiplication recovers the actual nilpotent quadratic coefficient table. -/
private theorem nilpotent_literal_factorization :
    (⟨[1, 0, 0]⟩ : DensePolynomial Dual).normalize =
      (⟨[1, -epsilon]⟩ : DensePolynomial Dual) *
        (Synthetic.divide (⟨[1, 0, 0]⟩ : DensePolynomial Dual) epsilon).quotient :=
  Synthetic.factorization_of_root _ epsilon
    ((Synthetic.divide _ epsilon).remainder_eval.symm.trans nilpotent_remainder)

/-- The original two-coordinate algebra with generator square one half. -/
private abbrev Quadratic := Pair Purelib.Data.Gaussian.Basic.Canonical (-1 / 2)

/-- The same original formal generator supplies an exact irrational-root calculation. -/
private def theta : Quadratic := Pair.generator

/-- The coefficient table of the quadratic relation in its original pair algebra. -/
private def relation : DensePolynomial Quadratic := ⟨[1, 0, Pair.scalar (-1 / 2)]⟩

/-- The original quadratic pair generator satisfies its exact coefficient relation. -/
private theorem quadratic_relation : relation.eval theta = 0 := by decide +kernel

/-- The automatic division retains the exact quadratic-generator quotient. -/
private theorem quadratic_quotient : (Synthetic.divide relation theta).quotient.coeffs = [1, theta] := by decide +kernel

/-- The automatic division certifies the same quadratic-generator remainder as zero. -/
private theorem quadratic_remainder : (Synthetic.divide relation theta).remainder = 0 := by decide +kernel

end TestPurelib.Polynomial.Dense.Ring
