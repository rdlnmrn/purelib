module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction.Numerator
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-!
# Hyperelliptic coefficient bases modulo admitted rational primitives

The original curve and finite infinity jet select `2g` polynomial numerator
coordinates. Odd degree uses all affine reduced coordinates; even degree uses
the original cached correction columns for its computed infinity functional.
The actual low-degree polynomial forms are independent modulo derivatives of
admitted original rational expressions. Bounded coefficient spanning is
computed, with an exact functional obstruction in even degree.

These are finite coefficient and rational-exactness results. Identification
of the computed functional with physical residues, branch regularity and the
full compact meromorphic quotient remain separate geometric statements.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.Basis

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian.Dense
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction (Preparation)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq sumFin_swap sumFin_mul_left sumFin_mul_right)

variable {genus : Nat}

/-- Construct the actual normalized numerator from the original bounded coordinates and retained infinity jet.

The even branch consumes the original stored corrected-column combination;
the odd branch preserves every original coordinate directly. Both use the
same original structural-vector coefficient conversion.
-/
@[expose] def combination (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) :
    Dense.Basic.DensePolynomial Canonical :=
  match curve.degreeShape with
  | .odd _ =>
      (Evaluation.toDense
        (Evaluation.fromVector coordinates)).normalize
  | .even _ =>
      (Evaluation.toDense
        (Evaluation.fromVector
          (InfinityCoefficients.evenCombination curve jet coordinates))).normalize

/-- One actual bounded basis numerator on the original curve and retained infinity jet.

Odd degree retains the original monomial coordinate. Even degree reads the
original corrected column at the same bounded nonpivot index.
-/
@[expose] def column (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (index : Fin (2 * genus)) : Dense.Basic.DensePolynomial Canonical :=
  match curve.degreeShape with
  | .odd _ => (Evaluation.toDense
      (Evaluation.fromVector (LinearAlgebra.Vector.Unit.unitVector index))).normalize
  | .even _ => (Evaluation.toDense
      (Evaluation.fromVector (InfinityCoefficients.evenColumns curve jet index))).normalize

/-- The constructed combination is the finite linear combination of the actual original basis columns. -/
theorem combination_eval_columns (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) (point : Canonical) :
    (combination curve jet coordinates).eval point =
      sumFin (fun index => coordinates index * (column curve jet index).eval point) := by
  cases shape : curve.degreeShape with
  | odd degree =>
      have columnEval (index : Fin (2 * genus)) : (column curve jet index).eval point = point ^ index.val := by
        rewrite [column, shape, eval_normalize, Evaluation.fromVector_eval_sum]
        calc
          _ = sumFin (fun position => if position = index then point ^ position.val else 0) := by
            apply sumFin_congr
            intro position
            rewrite [LinearAlgebra.Vector.Unit.unitVector_apply]
            by_cases same : position = index
            · rewrite [if_pos same, if_pos same, one_mul]; rfl
            · rewrite [if_neg same, if_neg same, zero_mul]; rfl
          _ = _ := sumFin_ite_eq index _
      rewrite [combination, shape, eval_normalize, Evaluation.fromVector_eval_sum]
      apply sumFin_congr
      intro index
      exact congrArg (fun value : Canonical => coordinates index * value) (columnEval index).symm
  | even degree =>
      have columnEval (index : Fin (2 * genus)) : (column curve jet index).eval point =
          sumFin (fun position => InfinityCoefficients.evenColumn curve jet index position * point ^ position.val) := by
        rewrite [column, shape, eval_normalize, InfinityCoefficients.evenColumns_apply,
          Evaluation.fromVector_eval_sum]
        rfl
      rewrite [combination, shape, eval_normalize, Evaluation.fromVector_eval_sum]
      calc
        _ = sumFin (fun position => sumFin (fun index =>
            coordinates index *
              (InfinityCoefficients.evenColumn curve jet index position * point ^ position.val))) := by
          apply sumFin_congr
          intro position
          rewrite [InfinityCoefficients.evenCombination_apply]
          exact (sumFin_mul_right _ _).symm.trans (sumFin_congr (fun index => by ring1))
        _ = sumFin (fun index => coordinates index * sumFin (fun position =>
            InfinityCoefficients.evenColumn curve jet index position * point ^ position.val)) :=
          (sumFin_swap _).trans (sumFin_congr (fun _ => sumFin_mul_left _ _))
        _ = _ := by
          apply sumFin_congr
          intro index
          exact congrArg (fun value : Canonical => coordinates index * value) (columnEval index).symm

/-- The constructed numerator is the original normalized polynomial record. -/
theorem combination_normalized (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) :
    (combination curve jet coordinates).normalize = combination curve jet coordinates := by
  cases shape : curve.degreeShape with
  | odd degree => rewrite [combination, shape]; exact normalize_normalize _
  | even degree => rewrite [combination, shape]; exact normalize_normalize _

/-- The original selected column is the combination with its actual structural coordinate unit. -/
theorem column_eq_combination (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (index : Fin (2 * genus)) :
    column curve jet index = combination curve jet (LinearAlgebra.Vector.Unit.unitVector index) := by
  have normalized : (column curve jet index).normalize = column curve jet index := by
    cases shape : curve.degreeShape with
    | odd degree => rewrite [column, shape]; exact normalize_normalize _
    | even degree => rewrite [column, shape]; exact normalize_normalize _
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq normalized
    (combination_normalized curve jet _)
  intro point
  symm
  rewrite [combination_eval_columns]
  calc
    _ = sumFin (fun position => if position = index then (column curve jet position).eval point else 0) := by
      apply sumFin_congr
      intro position
      rewrite [LinearAlgebra.Vector.Unit.unitVector_apply]
      by_cases same : position = index
      · rewrite [if_pos same, if_pos same, one_mul]; rfl
      · rewrite [if_neg same, if_neg same, zero_mul]; rfl
    _ = _ := sumFin_ite_eq index _

/-- Both retained parity branches have at most the original affine remainder coefficient count. -/
theorem combination_small (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) :
    (combination curve jet coordinates).degreeCount ≤ curve.polynomial.natDegree - 1 := by
  cases shape : curve.degreeShape with
  | odd degree =>
      rewrite [combination, shape]
      change (Evaluation.toDense
        (Evaluation.fromVector coordinates)).normalize.degreeCount ≤ _
      rewrite [degreeCount_normalize, degree]
      exact (Evaluation.fromVector_degreeCount_le coordinates).trans_eq (by omega0)
  | even degree =>
      rewrite [combination, shape]
      change (Evaluation.toDense
        (Evaluation.fromVector
          (InfinityCoefficients.evenCombination curve jet coordinates))).normalize.degreeCount ≤ _
      rewrite [degreeCount_normalize, degree]
      exact (Evaluation.fromVector_degreeCount_le _).trans_eq (by omega0)

/-- Equality of actual numerator combinations identifies the complete original bounded coordinates. -/
theorem combination_injective (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    {left right : Data.Vector Canonical (2 * genus)}
    (same : combination curve jet left = combination curve jet right) : left = right := by
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [combination, shape] at same
      exact Evaluation.fromVector_normalized_injective same
  | even degree =>
      simp only [combination, shape] at same
      exact InfinityCoefficients.evenCombination_injective curve jet
        (Evaluation.fromVector_normalized_injective same)

/-- Two combinations differing by an admitted original rational derivative have the same complete coordinates.

The original nonzero-denominator certificate is required for the primitive,
not merely a cleared cross identity. The original finite coefficient-count
search supplies an admitted point. The squarefree preparation and derivative cache
reduce its polynomial witness; the strict degree bound then forces zero.
-/
theorem combination_independent (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (preparation : Preparation curve.polynomial curve.squarefree)
    (left right : Data.Vector Canonical (2 * genus))
    (primitive : Expression curve.polynomial) (denominatorNonzero : primitive.denominator.isZero = false)
    (exactDerivative : primitive.derivative.Equal
      (Expression.oddReciprocal curve.polynomial 0 (combination curve jet left - combination curve jet right))) :
    left = right := by
  have small : (combination curve jet left - combination curve jet right).degreeCount ≤
      curve.polynomial.natDegree - 1 :=
    (degreeCount_sub_le_of_normalized (combination_normalized curve jet left)).trans
      (Data.Nat.Order.max_le (combination_small curve jet left) (combination_small curve jet right))
  have zero := Reduction.Numerator.reduced_exact_zero preparation curve.nonzero curve.degree_positive
    (combination curve jet left - combination curve jet right) small primitive denominatorNonzero exactDerivative
  apply combination_injective curve jet
  exact Dense.Extensionality.normalized_eq_of_sub_isZero
    (combination_normalized curve jet left) (combination_normalized curve jet right) zero

/-- The original differential constructor realizes a basis numerator with its supplied scalar.

The default scalar is one, retaining the original normalized representative.
Other scalars retain the identical numerator and inverse-root denominator.
-/
@[expose] def differential (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) (scale : Canonical := 1) :
    OddPowerDifferential curve.polynomial :=
  OddPowerDifferential.ofCoefficients curve.polynomial (combination curve jet coordinates) 0 scale

/-- Every combination retains the actual original numerator, inverse-root denominator and supplied scalar. -/
theorem differential_data (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) (scale : Canonical := 1) :
    (differential curve jet coordinates scale).numerator = combination curve jet coordinates ∧
      (differential curve jet coordinates scale).denominatorPairs = 0 ∧
      (differential curve jet coordinates scale).scale = scale := ⟨rfl, rfl, rfl⟩

/-- Every retained basis differential has numerator degree within the original genus bound.

The bound concerns its actual original numerator, including the zero
polynomial convention. It follows from the same stored combination's
coefficient count in either degree shape.
-/
theorem differential_numerator_degree_le (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) (scale : Canonical := 1) :
    (differential curve jet coordinates scale).numerator.natDegree ≤ 2 * genus := by
  rewrite [(differential_data curve jet coordinates scale).1]
  change (combination curve jet coordinates).degreeCount - 1 ≤ 2 * genus
  have small := combination_small curve jet coordinates
  cases curve.degreeShape with
  | odd degree => rewrite [degree] at small; omega0
  | even degree => rewrite [degree] at small; omega0

/-- The actual inverse-root differential has a polynomial generator-coefficient presentation from its original caches.

The supplied differential retains its own numerator and scale. The original
preparation supplies its stored Bézout coefficients and curve derivative,
without another Euclidean calculation. This is a finite coefficient identity,
not an assumed regularity certificate at branch points.
-/
theorem affine_generator_identity (curve : HyperellipticCurve genus)
    (preparation : Preparation curve.polynomial curve.squarefree)
    (original : OddPowerDifferential curve.polynomial) (pairs : original.denominatorPairs = 0) :
    original.coefficient.Equal
      (((Expression.generator (radicand := curve.polynomial)).scale
          (original.numerator.scale original.scale * preparation.left)).add
        ((Expression.generatorDerivative curve.polynomial).scale
          ((original.numerator.scale original.scale * preparation.right).scale 2))) := by
  rewrite [original.coefficient_eq, OddPower.Basic.coefficientSpec, pairs]
  apply Expression.oddReciprocal_generator_identity
  intro point
  have unit := preparation.identity point
  rewrite [preparation.polynomialDerivative_eq] at unit
  exact unit

/-- The computed infinity coefficient of the actual bounded normalized numerator.

The odd branch consumes the original finite parity functional. The even branch
reads the retained jet through its original coefficient weights. This is not a
physical residue or a claim of meromorphic regularity.
-/
@[expose] def infinityCoefficient (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical) : Canonical :=
  match curve.degreeShape with
  | .odd _ => InfinityCoefficients.oddFunctional curve jet
      (Evaluation.toVector (2 * genus)
        (Evaluation.fromDense numerator.normalize))
  | .even _ => InfinityCoefficients.evenFunctional curve jet
      (Evaluation.toVector (2 * genus + 1)
        (Evaluation.fromDense numerator.normalize))

/-- Every constructed combination lies in the actual computed infinity-coefficient kernel. -/
theorem infinityCoefficient_combination (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) :
    infinityCoefficient curve jet (combination curve jet coordinates) = 0 := by
  cases shape : curve.degreeShape with
  | odd degree =>
      rewrite [infinityCoefficient, shape]
      exact InfinityCoefficients.oddFunctional_zero curve jet _
  | even degree =>
      let retained := InfinityCoefficients.evenCombination curve jet coordinates
      have record : Evaluation.toVector (2 * genus + 1)
          (Evaluation.fromDense (combination curve jet coordinates).normalize) = retained := by
        apply Evaluation.fromVector_normalized_injective
        have bound : (combination curve jet coordinates).degreeCount ≤ 2 * genus + 1 := by
          have original := combination_small curve jet coordinates
          rewrite [degree] at original
          omega0
        have readback := Evaluation.toVector_fromDense_normalized
          (2 * genus + 1) (combination curve jet coordinates) bound
        exact readback.trans (by rewrite [combination, shape, normalize_normalize]; rfl)
      simp only [infinityCoefficient, shape]
      rewrite [record]
      exact InfinityCoefficients.evenCombination_zero curve jet coordinates

/-- Every original selected column satisfies the computed infinity-coefficient condition. -/
theorem infinityCoefficient_column (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (index : Fin (2 * genus)) : infinityCoefficient curve jet (column curve jet index) = 0 := by
  rewrite [column_eq_combination]
  exact infinityCoefficient_combination curve jet _

/-- The exact coefficient-spanning or actual computed infinity obstruction for one original polynomial.

Success retains original bounded coordinates and complete normalized
polynomial equality. Obstruction retains the actual computed coefficient and
its nonzero proof, indexed by the same curve, jet and original numerator.
-/
abbrev Decomposition (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical) :=
  ({ coordinates : Data.Vector Canonical (2 * genus) // combination curve jet coordinates = numerator.normalize } ⊕
    { obstruction : Canonical // obstruction = infinityCoefficient curve jet numerator ∧ obstruction ≠ 0 })

/-- Compute complete bounded coefficient spanning or its exact infinity obstruction.

The original normalized polynomial supplies its finite coefficient vector
once. Even degree delegates the decision and retained-column construction to
the original `decomposeEven`; odd degree retains all coordinates directly.
No residue-vanishing or successful-reduction hypothesis is requested.
-/
@[expose] def decompose (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical)
    (small : numerator.degreeCount ≤ curve.polynomial.natDegree - 1) : Decomposition curve jet numerator := by
  cases shape : curve.degreeShape with
  | odd degree =>
      let coordinates := Evaluation.toVector (2 * genus)
        (Evaluation.fromDense numerator.normalize)
      have bound : numerator.degreeCount ≤ 2 * genus := by rewrite [degree] at small; omega0
      refine .inl ⟨coordinates, ?_⟩
      rewrite [combination, shape]
      change (Evaluation.toDense
        (Evaluation.fromVector coordinates)).normalize = numerator.normalize
      exact Evaluation.toVector_fromDense_normalized _ _ bound
  | even degree =>
      let coefficients := Evaluation.toVector (2 * genus + 1)
        (Evaluation.fromDense numerator.normalize)
      have bound : numerator.degreeCount ≤ 2 * genus + 1 := by rewrite [degree] at small; omega0
      match InfinityCoefficients.decomposeEven curve jet coefficients with
      | .inl coordinates =>
          refine .inl ⟨coordinates.val, ?_⟩
          rewrite [combination, shape]
          change (Evaluation.toDense
            (Evaluation.fromVector
              (InfinityCoefficients.evenCombination curve jet coordinates.val))).normalize = numerator.normalize
          rewrite [coordinates.property]
          exact Evaluation.toVector_fromDense_normalized _ _ bound
      | .inr obstruction =>
          refine .inr ⟨obstruction.val, ?_, obstruction.property.2⟩
          rewrite [infinityCoefficient, shape]
          exact obstruction.property.1

/-- The actual computed coefficient kernel is spanned by the retained bounded columns.

The zero premise is membership in this explicitly computed finite kernel; it
is not an assumed analytic residue statement. The same typed decomposition
returns a witness or an actual nonzero coefficient contradicting membership.
-/
theorem kernel_spanning (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical)
    (small : numerator.degreeCount ≤ curve.polynomial.natDegree - 1)
    (zero : infinityCoefficient curve jet numerator = 0) :
    ∃ coordinates : Data.Vector Canonical (2 * genus), combination curve jet coordinates = numerator.normalize := by
  match decompose curve jet numerator small with
  | .inl coordinates => exact ⟨coordinates.val, coordinates.property⟩
  | .inr obstruction => exact (obstruction.property.2 (obstruction.property.1.trans zero)).elim

/-- Decompose the actual retained remainder differential, including its original scalar coefficient.

The original numerator reduction is supplied and never replayed. Its same
stored numerator and scale determine the actual unit-scale basis numerator;
the original finite infinity procedure then computes spanning or obstruction.
-/
@[expose] def decomposeReduced (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (preparation : Preparation curve.polynomial curve.squarefree) (input : OddPowerDifferential curve.polynomial)
    (reduced : Reduction.Numerator.Reduced preparation input) :
    Decomposition curve jet (reduced.remainder.numerator.scale reduced.remainder.scale) :=
  decompose curve jet _
    ((degreeCount_le_coeffs_length _).trans
      ((coeffs_length_scale_le _ _).trans
        ((degreeCount_le_coeffs_length _).trans reduced.remainder_small)))

/-- Successful retained-remainder coordinates preserve both original cached coefficient expressions.

The original scalar is already included in the decomposed numerator. The
original pair-count and coefficient-cache identities then give a finite
cross-coefficient certificate on the same defining curve; admission of an
operational readback remains the original differential's separate guard.
-/
theorem decomposeReduced_coefficient_equal (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (preparation : Preparation curve.polynomial curve.squarefree) (input : OddPowerDifferential curve.polynomial)
    (reduced : Reduction.Numerator.Reduced preparation input) (coordinates : Data.Vector Canonical (2 * genus))
    (same : combination curve jet coordinates =
      (reduced.remainder.numerator.scale reduced.remainder.scale).normalize) :
    (differential curve jet coordinates).coefficient.Equal reduced.remainder.coefficient := by
  rewrite [(differential curve jet coordinates).coefficient_eq, reduced.remainder.coefficient_eq]
  change (Expression.oddReciprocal curve.polynomial 0 ((combination curve jet coordinates).scale 1)).Equal
    (Expression.oddReciprocal curve.polynomial reduced.remainder.denominatorPairs
      (reduced.remainder.numerator.scale reduced.remainder.scale))
  rewrite [reduced.remainder_pairs]
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [Expression.oddReciprocal, eval_zero, zero_mul, -eq_self, -iff_self]
    rfl
  · intro point
    have readback := congrArg (fun p : Dense.Basic.DensePolynomial Canonical => p.eval point) same
    rewrite [eval_normalize, eval_scale] at readback
    simp only [Expression.oddReciprocal, eval_scale, Dense.Power.eval_power]
    rewrite [readback]
    ring1

/-- A computed successful spanning result has unique complete original bounded coordinates. -/
theorem decomposition_unique (curve : HyperellipticCurve genus) (jet : InfinityCoefficients.Jet curve)
    (numerator : Dense.Basic.DensePolynomial Canonical)
    (left right : { coordinates : Data.Vector Canonical (2 * genus) //
      combination curve jet coordinates = numerator.normalize }) : left = right := by
  have coordinates := combination_injective curve jet (left.property.trans right.property.symm)
  exact Subtype.ext coordinates

end Purelib.Curves.Hyperelliptic.Differentials.Basis
