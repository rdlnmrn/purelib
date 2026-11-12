module

import Purelib.Polynomial.Dense.Companion.Algebra
import Purelib.Algebra.Monogenic.Coordinates.Bounds
import Purelib.Algebra.Monogenic.Coordinates.Multiplication
import Purelib.Algebra.Monogenic.Coordinates.Reading
import Purelib.Algebra.Monogenic.Coordinates.Reading.Request
import Purelib.Algebra.Monogenic.Coordinates.Reading.Observation
import Purelib.Algebra.Monogenic.Cyclic.Weights
import Purelib.Algebra.Ring.GaussianReading
import Purelib.Data.Gaussian.Power.Radius
import Purelib.Algebra.Monogenic.Weight
import Purelib.Data.Gaussian.Norm.Weight
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Companion.Adjunction
import Purelib.Polynomial.Dense.Roots.Tower
import Purelib.Polynomial.Dense.Roots.Tower.Algebra
import Purelib.Polynomial.Dense.Roots.Tower.Factorization
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Parameters
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Request
import Purelib.Polynomial.Dense.Gaussian.Coprime.Identity
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Division.Synthetic
import Purelib.Polynomial.Dense.Division.Synthetic.Factorization
import Purelib.Tactic.Ring

/-!
# Exact quadratic companion coordinates

The retained two-dimensional generator satisfies its quadratic relation by
finite matrix arithmetic. Its cached first two powers form a cyclic table
and recover every commuting matrix from the same distinguished column.
-/

namespace TestPurelib.Polynomial.Dense.Cyclic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading (Parameters Request Observation ColumnBound)
open Purelib.Data.Gaussian.Power (Radius)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)

/-- The original scalar source polynomial `z²-1/2`. -/
private def sourcePolynomial : DensePolynomial Canonical := ⟨[1, 0, -(1 / 2)]⟩

/-- The original source-indexed companion constructor computes the same feedback and matrix caches. -/
private def companion : Companion sourcePolynomial := Companion.ofPositive sourcePolynomial (by decide +kernel)

/-- The transposed companion computed from the original scalar polynomial. -/
private def generator : SquareMatrix Canonical 2 := Rectangular.transpose companion.matrix

/-- The public constructor computes the original generator's whole cyclic table without supplied basis data. -/
private def cyclic : Cyclic generator := companion.cyclic

/-- The retained matrix satisfies its exact quadratic relation. -/
private theorem generator_square : Multiplication.mul generator generator = Multiplication.scaleIdentity (1 / 2) := by
  apply matrix_ext
  decide +kernel

/-- The cached original powers reconstruct the same generator entry at every coordinate. -/
private theorem generator_reconstruction (row column : Fin 2) :
    generator row column = sumFin (fun index => generator index cyclic.origin * cyclic.powers index row column) :=
  cyclic.reconstruct_entry generator rfl row column

/-- The same cached cyclic table certifies commutation of arbitrary compatible matrix payloads. -/
private theorem commuting_reconstruction (left right : SquareMatrix Canonical 2)
    (leftCommutes : Multiplication.mul left generator = Multiplication.mul generator left)
    (rightCommutes : Multiplication.mul right generator = Multiplication.mul generator right) :
    Multiplication.mul left right = Multiplication.mul right left :=
  cyclic.commuting_pair left right leftCommutes rightCommutes

/-- The original retained generator satisfies the same relation in the executable cyclic coefficient ring. -/
private theorem algebra_root_square :
    Cyclic.Element.root cyclic * Cyclic.Element.root cyclic = Cyclic.Element.scalar cyclic (1 / 2) := by
  apply Cyclic.Element.ext
  exact generator_square

/-- The original quadratic coefficient table over the same retained cyclic algebra. -/
private def relation : DensePolynomial (Cyclic.Element cyclic) :=
  Map.map (Cyclic.Element.scalar cyclic) sourcePolynomial

/-- Exact finite Horner evaluation of the original relation vanishes at its retained algebra generator. -/
private theorem algebra_relation : relation.eval (Cyclic.Element.root cyclic) = 0 := companion.root_relation

/-- The public original division constructor retains the exact quotient over the new cyclic coefficient algebra. -/
private theorem algebra_quotient :
    (Synthetic.divide relation (Cyclic.Element.root cyclic)).quotient.coeffs =
      [1, Cyclic.Element.root cyclic] := by decide +kernel

/-- The same public original division constructor certifies its quadratic-root remainder. -/
private theorem algebra_remainder :
    (Synthetic.divide relation (Cyclic.Element.root cyclic)).remainder = 0 :=
  (Synthetic.divide relation (Cyclic.Element.root cyclic)).remainder_eval.trans algebra_relation

/-- The retained irrational generator gives literal factorization using the original coefficient product. -/
private theorem algebra_factorization :
    relation.normalize =
      (⟨[1, -(Cyclic.Element.root cyclic)]⟩ : DensePolynomial (Cyclic.Element cyclic)) *
        (Synthetic.divide relation (Cyclic.Element.root cyclic)).quotient :=
  Synthetic.factorization_of_root relation (Cyclic.Element.root cyclic) algebra_relation

/-- The public builder retains the same companion, root table, division and literal product. -/
private def adjunction : Companion.Adjunction sourcePolynomial := companion.adjoin

/-- The public cached construction retains the original three coefficient slots. -/
private theorem cached_source : adjunction.source.coeffs =
    [1, 0, Cyclic.Element.scalar adjunction.table (-(1 / 2))] := by
  rewrite [adjunction.source_eq]
  change [Cyclic.Element.scalar adjunction.table 1, Cyclic.Element.scalar adjunction.table 0,
    Cyclic.Element.scalar adjunction.table (-(1 / 2))] = _
  rewrite [Cyclic.Element.scalar_one, Cyclic.Element.scalar_zero]
  rfl

/-- The actual cached division keeps its unit leading coefficient and same retained algebraic root. -/
private theorem cached_quotient : adjunction.division.quotient.coeffs = [1, adjunction.root] := by
  decide +kernel

/-- The same cached original product recovers the original source coefficient table literally. -/
private theorem cached_product : adjunction.product.coeffs =
    [1, 0, Cyclic.Element.scalar adjunction.table (-(1 / 2))] := by
  have normalized : adjunction.source.normalize = adjunction.source := by
    rewrite [adjunction.source_eq,
      ← Map.map_normalize (Cyclic.Element.scalar adjunction.table) (Cyclic.Element.scalar_zero adjunction.table)
        (fun _ _ same => Cyclic.Element.scalar_injective adjunction.table same)]
    exact congrArg (Map.map (Cyclic.Element.scalar adjunction.table)) (by decide +kernel)
  exact (congrArg DensePolynomial.coeffs (adjunction.factorization.symm.trans normalized)).trans cached_source

/-- The actual cached quadratic division constructs its root inverse from the original constant inverse. -/
private def rootInverse : {inverse : Cyclic.Element adjunction.table // adjunction.root * inverse = 1} :=
  adjunction.division.rootInverse adjunction.remainder_zero
    (Cyclic.Element.scalar adjunction.table (-2)) (by decide +kernel)

/-- The constructed inverse is twice the same exact irrational generator. -/
private theorem cached_root_inverse : rootInverse.val = adjunction.root + adjunction.root := by
  apply Cyclic.Element.ext
  apply matrix_ext
  decide +kernel

/-- A second original companion is constructed from the actual first quotient and its retained leading unit. -/
private def quotientCompanion : Companion adjunction.division.quotient :=
  Companion.ofUnit adjunction.division.quotient (by decide +kernel)
    (Cyclic.Element.scalar adjunction.table companion.leadingInverse)
    (adjunction.quotient_unit (by decide +kernel))

/-- The second public adjunction strips the actual remaining factor in the original quadratic tower. -/
private def secondAdjunction : Companion.Adjunction adjunction.division.quotient := quotientCompanion.adjoin

/-- The second retained stripping step leaves the original unit constant. -/
private theorem second_quotient : secondAdjunction.division.quotient.coeffs = [1] := by
  decide +kernel

/-- Both successive actual quotient degrees are certified by the original source-dependent readbacks. -/
private theorem second_quotient_degree : secondAdjunction.division.quotient.natDegree + 1 =
    adjunction.division.quotient.natDegree :=
  secondAdjunction.quotient_degree (adjunction.quotient_normalized (by decide +kernel))

/-- The automatic public tower constructor computes every stage from the original quadratic source alone. -/
private def automaticTower : Roots.Tower Canonical inferInstance inferInstance sourcePolynomial :=
  Roots.Tower.prepare sourcePolynomial (by decide +kernel) 1 (by decide +kernel)

/-- Executing the automatic quadratic construction produces exactly its two certified stripping stages. -/
private theorem automatic_tower_computes : automaticTower.steps = 2 := by decide +kernel

/-- A cubic source for the same degree-driven automatic constructor. -/
private def cubic : DensePolynomial Canonical := ⟨[1, 0, 0, -2]⟩

/-- The same public procedure constructs the cubic's heterogeneous coefficient-algebra tower. -/
private def cubicTower : Roots.Tower Canonical inferInstance inferInstance cubic :=
  Roots.Tower.prepare cubic (by decide +kernel) 1 (by decide +kernel)

/-- The original cubic degree certifies exhaustion of all three actual adjoining stages. -/
private theorem cubic_tower_steps : cubicTower.steps = 3 :=
  cubicTower.steps_eq_degree.trans (by decide +kernel)

/-- Original quadratic evaluations map through the actual final tower algebra by its retained scalar embedding. -/
private theorem automatic_embedding_evaluation (point : Canonical) :
    automaticTower.embed (sourcePolynomial.eval point) =
      (Map.map automaticTower.embed sourcePolynomial).eval (automaticTower.embed point) :=
  Map.map_eval automaticTower.embed automaticTower.embed_zero automaticTower.embed_add automaticTower.embed_mul
    sourcePolynomial point

/-- Equality of scalar images in the actual cubic tower reflects equality of the original coefficients. -/
private theorem cubic_embedding_injective (left right : Canonical)
    (same : cubicTower.embed left = cubicTower.embed right) : left = right :=
  cubicTower.embed_injective same

/-- Executing the quadratic construction collects both retained roots in their original stage order. -/
private theorem automatic_blocks_compute : automaticTower.blocks.length = 2 := by decide +kernel

/-- The actual irrational quadratic tower gives a complete literal product in its final coefficient algebra. -/
private theorem automatic_factorization : (Map.map automaticTower.embed sourcePolynomial).normalize =
    DensePolynomial.scale (automaticTower.embed sourcePolynomial.leadingCoeff) (Roots.product automaticTower.blocks) :=
  automaticTower.factorization (by decide +kernel)

/-- The same public all-stage factorization applies to the original cubic without supplied roots. -/
private theorem cubic_factorization : (Map.map cubicTower.embed cubic).normalize =
    DensePolynomial.scale (cubicTower.embed cubic.leadingCoeff) (Roots.product cubicTower.blocks) :=
  cubicTower.factorization (by decide +kernel)

/-- The original completed quadratic Euclidean result supplies a cached squarefree certificate. -/
private def quadraticSquarefree : CoprimeCertificate sourcePolynomial (Gaussian.GCD.derivative sourcePolynomial) :=
  let derivative := Gaussian.GCD.derivative sourcePolynomial
  let result := Gaussian.GCD.extendedGCD sourcePolynomial derivative
  Gaussian.Coprime.Decision.certificateOfConstantGCD sourcePolynomial derivative result rfl
    (by decide +kernel) (by decide +kernel)

/-- The actual cached right Bezout coefficient of the quadratic is the original coordinate polynomial. -/
private theorem quadratic_right_cofactor : quadraticSquarefree.right.coeffs = [1, 0] := by decide +kernel

/-- The retained Gaussian cofactors explicitly invert the derivative at the exact irrational generator. -/
private theorem quadratic_derivative_unit :
    (Map.map (Cyclic.Element.scalar adjunction.table) (Gaussian.GCD.derivative sourcePolynomial)).eval adjunction.root *
      (Map.map (Cyclic.Element.scalar adjunction.table) quadraticSquarefree.right).eval adjunction.root = 1 :=
  quadraticSquarefree.right_unit (Cyclic.Element.scalar adjunction.table)
    (Cyclic.Element.scalar_zero adjunction.table)
    (fun _ _ same => Cyclic.Element.scalar_injective adjunction.table same)
    (Cyclic.Element.scalar_one adjunction.table) (Cyclic.Element.scalar_add adjunction.table)
    (Cyclic.Element.scalar_mul adjunction.table) adjunction.root
    (adjunction.source_eq ▸ adjunction.root_vanishes)

/-- The original quadratic generator's same retained column has the coordinate polynomial `z`. -/
private theorem generator_coordinate_polynomial : (Cyclic.Element.root cyclic).polynomial.coeffs = [1, 0] := by
  decide +kernel

/-- Every original linear coefficient table reads as its same rational polynomial below the quadratic degree. -/
private theorem linear_readback (coefficient constant point : Canonical) :
    Cyclic.Element.evaluate id point
        ((Map.map (Cyclic.Element.scalar cyclic) (⟨[coefficient, constant]⟩ : DensePolynomial Canonical)).eval
          (Cyclic.Element.root cyclic)) = coefficient * point + constant := by
  have retained := Cyclic.Element.evaluate_polynomial (cyclic := cyclic) id rfl (fun _ _ => rfl)
    point (⟨[coefficient, constant]⟩ : DensePolynomial Canonical) (Nat.le_refl 2)
  rewrite [Map.map_id] at retained
  change _ = (0 * point + coefficient) * point + constant at retained
  rewrite [zero_mul, zero_add] at retained
  exact retained

/-- The retained coordinate reading exposes the actual quadratic relation residual at a rational candidate. -/
private theorem quadratic_reading_residual :
    Cyclic.Element.evaluate id (1 / 4 : Canonical) (Cyclic.Element.root cyclic * Cyclic.Element.root cyclic) -
      Cyclic.Element.evaluate id (1 / 4 : Canonical) (Cyclic.Element.root cyclic) *
        Cyclic.Element.evaluate id (1 / 4 : Canonical) (Cyclic.Element.root cyclic) = 7 / 16 := by
  have rootReading := Cyclic.Element.evaluate_root (cyclic := cyclic) id rfl rfl (1 / 4 : Canonical) (by decide)
  have decomposition := Cyclic.Element.evaluate_root_mul_sub id rfl (fun _ _ => rfl)
    (1 / 4 : Canonical) (Cyclic.Element.root cyclic)
  rewrite [rootReading] at decomposition ⊢
  apply decomposition.trans
  decide +kernel

/-- The original quadratic matrix contributes its actual two nonzero entry quadrances. -/
private theorem quadratic_root_weight :
    (Cyclic.Element.weight cyclic Norm.weight).value (Cyclic.Element.root cyclic) =
      5 / 4 := by
  decide +kernel

/-- The same finite squared weight lifts with the actual original intermediate dimension two. -/
private theorem quadratic_weight_multiplier :
    (Cyclic.Element.weight cyclic Norm.weight).multiplier = 4 := by
  decide +kernel

/-- Original quadratic power weights are materialized once before choosing a candidate reading. -/
private def cachedWeights : Cyclic.Weights cyclic Norm.weight := Cyclic.Weights.prepare cyclic Norm.weight

/-- The actual retained quadratic table preserves both original power weights and their total. -/
private theorem cached_weights_compute : cachedWeights.generatorWeight = 5 / 4 ∧
    cachedWeights.powerWeights 0 = 2 ∧ cachedWeights.powerWeights 1 = 5 / 4 ∧
      cachedWeights.powerTotal = 13 / 4 := by decide +kernel

/-- Every same original bounded quadratic power uses the cached total as its uniform weight ceiling. -/
private theorem quadratic_cached_power_weight_bound (index : Fin 2) :
    (Cyclic.Element.weight cyclic Norm.weight).value (Cyclic.Element.root cyclic ^ index.val) ≤
      cachedWeights.powerTotal := cachedWeights.root_power_weight_le index

/-- The original identity reading begins the finite algebra model with gain one and zero product error. -/
private theorem identity_reading_constants : GaussianReading.identity.gain = 1 ∧
    GaussianReading.identity.error = 0 := ⟨rfl, rfl⟩

/-- Materialize the fixed-radius powers before requesting a more accurate original candidate. -/
private def readingRadius : Radius 2 (1 / 16) := Radius.prepare 2 (1 / 16) (by decide +kernel)

/-- The original finite scans retain the exact independent quadratic radius and growth totals. -/
private theorem reading_radius_computes : readingRadius.powers 0 = 1 ∧
    readingRadius.powers 1 = 1 / 16 ∧ readingRadius.powers 2 = (1 / 16) ^ 2 ∧
      readingRadius.powerTotal = 17 / 16 ∧ readingRadius.growth = 17 / 8 ∧
        readingRadius.growthTotal = 25 / 8 := by decide +kernel

/-- The same stored radius total controls every finite original candidate power within its fixed bound. -/
private theorem reading_radius_bound (point : Canonical) (bounded : Norm.Basic.normSq point ≤ 1 / 16)
    (index : Fin 2) : Norm.Basic.normSq (point ^ index.val) ≤ readingRadius.powerTotal :=
  readingRadius.normSq_pow_le point bounded index

/-- The original quadratic relation has the exact retained total weight one half. -/
private theorem quadratic_square_weight :
    (Cyclic.Element.weight cyclic Norm.weight).value
      (Cyclic.Element.root cyclic * Cyclic.Element.root cyclic) = 1 / 2 := by
  decide +kernel

/-- Every retained quadratic algebra element has a rational reading bounded by its same original entry weights. -/
private theorem quadratic_reading_bound (value : Cyclic.Element cyclic) :
    Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
      4 * (Cyclic.Element.weight cyclic Norm.weight).value value := by
  have coefficientBound (scalar : Canonical) : Norm.Basic.normSq (id scalar) ≤ 1 * Norm.weight.value scalar := by
    change Norm.Basic.normSq scalar ≤ 1 * Norm.Basic.normSq scalar
    rewrite [one_mul]
    exact le_rfl
  have retained := Cyclic.Element.evaluate_normSq_le Norm.weight id rfl 1 1 (by decide) (by decide)
    coefficientBound (1 / 4 : Canonical) (by decide +kernel) value
  have factor : (2 : Purelib.Data.Rat.Fraction.Rational) ^ 2 * 1 * 1 = 4 := by decide +kernel
  change Norm.Basic.normSq _ ≤ ((2 : Purelib.Data.Rat.Fraction.Rational) ^ 2 * 1 * 1) * _ at retained
  rewrite [factor] at retained
  exact retained

/-- Read only the original real coordinate as a Gaussian value. -/
private def realProjection (value : Canonical) : Canonical := ⟨value.re, 0⟩

/-- The actual real-coordinate reading has a uniform finite product-discrepancy certificate. -/
private theorem realProjection_product_bound (left right : Canonical) :
    Norm.Basic.normSq (realProjection (left * right) - realProjection left * realProjection right) ≤
      1 * Norm.weight.value left * Norm.weight.value right := by
  have imaginaryNonnegative (value : Canonical) : 0 ≤ value.im * value.im := by
    have bound := Arithmetic.sq_nonneg_direct value.im
    rewrite [pow_two] at bound
    exact bound
  have imaginaryBound (value : Canonical) : value.im * value.im ≤ Norm.Basic.normSq value := by
    have realNonnegative := Arithmetic.sq_nonneg_direct value.re
    rewrite [pow_two] at realNonnegative
    have bound := Arithmetic.add_le_add_right_direct realNonnegative (value.im * value.im)
    rewrite [zero_add] at bound
    change value.im * value.im ≤ value.re ^ 2 + value.im ^ 2
    rewrite [pow_two, pow_two]
    exact bound
  have discrepancy : Norm.Basic.normSq
      (realProjection (left * right) - realProjection left * realProjection right) =
      (left.im * left.im) * (right.im * right.im) := by
    change ((left.re * right.re - left.im * right.im) - (left.re * right.re - 0 * 0)) ^ 2 +
      (0 - (left.re * 0 + 0 * right.re)) ^ 2 = _
    ring0
  rewrite [discrepancy, _root_.one_mul]
  exact Arithmetic.mul_le_mul_direct (imaginaryBound left) (imaginaryBound right)
    (imaginaryNonnegative right) (Norm.Basic.normSq_nonneg left)

/-- A genuinely nonmultiplicative original coefficient reading uses the same scalar-error bound. -/
private theorem quadratic_projection_scalar_bound (coefficient : Canonical) (value : Cyclic.Element cyclic) :
    Norm.Basic.normSq (Cyclic.Element.evaluate realProjection (1 / 4 : Canonical)
        (Cyclic.Element.scalar cyclic coefficient * value) - realProjection coefficient *
          Cyclic.Element.evaluate realProjection (1 / 4 : Canonical) value) ≤
      4 * Norm.weight.value coefficient * (Cyclic.Element.weight cyclic Norm.weight).value value := by
  have bounded := Cyclic.Element.evaluate_scalar_mul_normSq_sub_le Norm.weight realProjection rfl 1 1
    (by decide) (by decide) realProjection_product_bound (1 / 4 : Canonical) (by decide +kernel) coefficient value
  have factor : (2 : Rational) ^ 2 * 1 * 1 = 4 := by decide +kernel
  change Norm.Basic.normSq _ ≤ ((2 : Rational) ^ 2 * 1 * 1) * _ * _ at bounded
  rewrite [factor] at bounded
  exact bounded

/-- The actual quadratic generator's computed rational column residual bounds its action on every algebra element. -/
private theorem quadratic_generator_reading_bound (value : Cyclic.Element cyclic) :
    Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical) (Cyclic.Element.root cyclic * value) -
      (1 / 4 : Canonical) * Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
        (49 / 32) * (Cyclic.Element.weight cyclic Norm.weight).value value := by
  have coefficients (scalar : Canonical) : Norm.Basic.normSq (id scalar) ≤ 1 * Norm.weight.value scalar := by
    change Norm.Basic.normSq scalar ≤ 1 * Norm.Basic.normSq scalar
    rewrite [one_mul]
    exact le_rfl
  have products (left right : Canonical) :
      Norm.Basic.normSq (id (left * right) - id left * id right) ≤
        0 * Norm.weight.value left * Norm.weight.value right := by
    change Norm.Basic.normSq (left * right - left * right) ≤ 0 * _ * _
    rewrite [sub_self, Norm.Basic.normSq_zero, zero_mul, zero_mul]
    exact le_rfl
  have bounded := Cyclic.Element.evaluate_root_mul_normSq_sub_le Norm.weight id rfl (fun _ _ => rfl)
    1 0 1 ((7 / 16) ^ 2) (by decide) (by decide) (Arithmetic.sq_nonneg_direct _)
    coefficients products (1 / 4 : Canonical)
    (by decide +kernel) (by decide +kernel) value
  have factor : (2 : Rational) * (2 ^ 2 * 1 * ((7 / 16) ^ 2) +
      (2 ^ 2 * 2 ^ 2 * 0 * 1) * Weight.total Norm.weight generator) = 49 / 32 := by
    rewrite [mul_zero, zero_mul, zero_mul, add_zero]
    decide +kernel
  change Norm.Basic.normSq _ ≤ (2 * (2 ^ 2 * 1 * ((7 / 16) ^ 2) +
    (2 ^ 2 * 2 ^ 2 * 0 * 1) * Weight.total Norm.weight generator)) * _ at bounded
  rewrite [factor] at bounded
  exact bounded

/-- The same original generator-action certificate propagates through every bounded quadratic power. -/
private theorem quadratic_power_reading_bound (exponent : Nat) (bounded : exponent ≤ 2)
    (value : Cyclic.Element cyclic) :
    Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical)
        (Cyclic.Element.root cyclic ^ exponent * value) -
      (1 / 4 : Canonical) ^ exponent * Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
        (((49 / 32 : Rational) * 4 * cachedWeights.powerTotal) * (17 / 8) ^ exponent) *
          (Cyclic.Element.weight cyclic Norm.weight).value value := by
  have retained := Cyclic.Element.evaluate_root_pow_mul_normSq_sub_le Norm.weight id (1 / 4 : Canonical)
    (49 / 32) cachedWeights.powerTotal (1 / 16) (by decide +kernel)
    cachedWeights.powerTotal_nonnegative (by decide +kernel)
    (by decide +kernel) quadratic_cached_power_weight_bound quadratic_generator_reading_bound exponent bounded value
  have ratio : 2 * (1 + (1 / 16 : Rational)) = 17 / 8 := by decide +kernel
  rewrite [quadratic_weight_multiplier, ratio] at retained
  exact retained

/-- Every pair of original quadratic algebra elements has its product-reading discrepancy uniformly bounded. -/
private theorem quadratic_product_reading_bound (left right : Cyclic.Element cyclic) :
    Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical) (left * right) -
      Cyclic.Element.evaluate id (1 / 4 : Canonical) left *
        Cyclic.Element.evaluate id (1 / 4 : Canonical) right) ≤
      (8 * (((49 / 32 : Rational) * 4 * cachedWeights.powerTotal) * (17 / 8) ^ 2)) *
        (Cyclic.Element.weight cyclic Norm.weight).value left *
          (Cyclic.Element.weight cyclic Norm.weight).value right := by
  let powerFactor := (49 / 32 : Rational) * 4 * cachedWeights.powerTotal
  let powerError := powerFactor * (17 / 8) ^ 2
  have powerFactorNonnegative : 0 ≤ powerFactor := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (by decide +kernel)) cachedWeights.powerTotal_nonnegative
  have coefficients (coefficient : Canonical) : Norm.Basic.normSq (id coefficient) ≤
      1 * Norm.weight.value coefficient := by
    change Norm.Basic.normSq coefficient ≤ 1 * Norm.Basic.normSq coefficient
    rewrite [one_mul]
    exact le_rfl
  have scalars (coefficient : Canonical) (value : Cyclic.Element cyclic) :
      Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical)
          (Cyclic.Element.scalar cyclic coefficient * value) -
        id coefficient * Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
          0 * Norm.weight.value coefficient * (Cyclic.Element.weight cyclic Norm.weight).value value := by
    rewrite [Cyclic.Element.evaluate_scalar_mul id rfl (1 / 4 : Canonical) coefficient coefficient (fun _ => rfl)]
    change Norm.Basic.normSq (coefficient * Cyclic.Element.evaluate id (1 / 4 : Canonical) value -
      coefficient * Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
        0 * Norm.weight.value coefficient * (Cyclic.Element.weight cyclic Norm.weight).value value
    rewrite [sub_self, Norm.Basic.normSq_zero, zero_mul, zero_mul]
    exact le_rfl
  have powers (index : Fin 2) (value : Cyclic.Element cyclic) :
      Norm.Basic.normSq (Cyclic.Element.evaluate id (1 / 4 : Canonical)
          (Cyclic.Element.root cyclic ^ index.val * value) -
        (1 / 4 : Canonical) ^ index.val * Cyclic.Element.evaluate id (1 / 4 : Canonical) value) ≤
          powerError * (Cyclic.Element.weight cyclic Norm.weight).value value := by
    have finiteBound : ∀ index : Fin 2, (17 / 8 : Rational) ^ index.val ≤ (17 / 8) ^ 2 := by decide +kernel
    have constantBound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (finiteBound index) powerFactorNonnegative
    exact (quadratic_power_reading_bound index.val (Nat.le_of_lt index.isLt) value).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct constantBound
        ((Cyclic.Element.weight cyclic Norm.weight).nonnegative value))
  have powerErrorNonnegative : 0 ≤ powerError := Arithmetic.mul_nonneg_direct
    powerFactorNonnegative (Arithmetic.sq_nonneg_direct _)
  have retained := Cyclic.Element.evaluate_mul_normSq_sub_le Norm.weight id rfl (fun _ _ => rfl)
    (1 / 4 : Canonical) 1 0 powerError cachedWeights.powerTotal (by decide) (by decide) powerErrorNonnegative
    cachedWeights.powerTotal_nonnegative coefficients quadratic_cached_power_weight_bound scalars powers left right
  have factor : (2 : Rational) ^ 2 * 2 *
      (0 * (Cyclic.Element.weight cyclic Norm.weight).multiplier * cachedWeights.powerTotal + 1 * powerError) =
        8 * powerError := by
    rewrite [zero_mul, zero_mul, zero_add, one_mul]
    ring0
  rewrite [factor] at retained
  exact retained

/-- Prepare the original quadratic model bounds before selecting its candidate. -/
private def readingParameters : Parameters cyclic Norm.weight 1 1 :=
  Parameters.prepare cyclic Norm.weight 1 1 (by decide) (by decide)

/-- The cached quadratic model has the independent finite gain and source-error coefficient. -/
private theorem reading_parameters_compute : readingParameters.gain = 8 ∧
    readingParameters.sourceFactor = 4 * 4 * 4 * 13 * 5 := by decide +kernel

/-- The original quadratic coordinate evaluator is an actual certified nonmultiplicative Gaussian reading. -/
private def quadraticObservation : Observation readingParameters GaussianReading.identity rfl :=
  Observation.prepare readingParameters GaussianReading.identity rfl (7 / 10 : Canonical) (by decide +kernel)
    ((1 / 100) ^ 2) (Arithmetic.sq_nonneg_direct _) (by unfold ColumnBound; decide +kernel)

/-- The actual certified reading keeps its computed gain and original source residual as retained data. -/
private theorem quadratic_reading_constants : quadraticObservation.child.gain = 8 ∧
    quadraticObservation.child.error = readingParameters.sourceFactor * (1 / 100) ^ 2 := by
  constructor
  · exact reading_parameters_compute.left
  · change readingParameters.parentFactor * 0 + readingParameters.sourceFactor * (1 / 100) ^ 2 = _
    rewrite [mul_zero, zero_add]
    rfl

/-- The same certified reading exposes its actual nonzero multiplication discrepancy. -/
private theorem quadratic_model_discrepancy :
    quadraticObservation.child.read (Cyclic.Element.root cyclic * Cyclic.Element.root cyclic) -
      quadraticObservation.child.read (Cyclic.Element.root cyclic) *
        quadraticObservation.child.read (Cyclic.Element.root cyclic) = 1 / 100 := by decide +kernel

/-- The actual irrational-root candidate gives a certified uniform product-error constant below one. -/
private theorem quadratic_model_error_lt_one : quadraticObservation.child.error < 1 := by
  rewrite [quadratic_reading_constants.right]
  decide +kernel

/-- The same original quadratic root reading consumes its retained source-fixed gain and generator weight. -/
private theorem quadratic_source_root_bound :
    Norm.Basic.normSq (quadraticObservation.child.read (Cyclic.Element.root cyclic)) ≤
      readingParameters.gain * readingParameters.weights.generatorWeight :=
  quadraticObservation.root_normSq_le

/-- The actual quadratic model's source-fixed root bound is ten, independently of its observed candidate. -/
private theorem quadratic_source_root_bound_value :
    readingParameters.gain * readingParameters.weights.generatorWeight = 10 := by decide +kernel

/-- The original fixed parameter cache computes a sufficient positive request before any observation. -/
private def readingRequest : Request readingParameters 1 := Request.prepare readingParameters 1 (by decide)

/-- Actual future parent and source certificates paying the stored request imply the requested child bound. -/
private theorem reading_request_sufficient (parentError residual : Rational)
    (parentBound : parentError ≤ readingRequest.tolerance) (sourceBound : residual ≤ readingRequest.tolerance) :
    readingParameters.parentFactor * parentError + readingParameters.sourceFactor * residual < 1 :=
  readingRequest.error_lt parentError residual parentBound sourceBound

/-- Every original quadratic adjunction prepares its bounds before any candidate is observed. -/
private def towerReadingParameters : Roots.Tower.Reading.Parameters automaticTower Norm.weight 1 1 :=
  Roots.Tower.Reading.Parameters.prepare automaticTower Norm.weight 1 1 (by decide) (by decide)

/-- Both original stages occur once, with the gain computed by their retained radius/weight caches. -/
private theorem tower_reading_parameters_compute :
    towerReadingParameters.layers = 2 ∧ towerReadingParameters.finalGain = 16 := by decide +kernel

/-- The same two-stage original parameter chain sums its fixed root bounds before any observation. -/
private theorem tower_source_root_bound_total : towerReadingParameters.rootBoundTotal = 30 := by decide +kernel

/-- The original heterogeneous tower receives a complete positive request before root observations. -/
private def towerReadingRequest : Roots.Tower.Reading.Request towerReadingParameters 1 :=
  Roots.Tower.Reading.Request.prepare towerReadingParameters 1 (by decide)

/-- The computed sufficient budget covers both original adjunctions and has a positive initial tolerance. -/
private theorem tower_reading_request_covers_source :
    towerReadingRequest.budget.layers = 2 ∧ 0 < towerReadingRequest.tolerance := by
  constructor
  · exact towerReadingRequest.layers_eq_degree.trans (by decide +kernel)
  · exact towerReadingRequest.positive

end TestPurelib.Polynomial.Dense.Cyclic
