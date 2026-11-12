module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Constants
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Product
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Products
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Build
import Purelib.Polynomial.Dense.RootBound
import Purelib.Tactic.Ring

public section

/-!
# Parity-aware finite square-factor reduction

An exact multiplicity basis gives `p = s * s * q`: half of each
multiplicity goes into `s`, and only odd multiplicities remain in `q`.
The scalar stays in `q`, without extracting a square root in the coefficient
field.  This is not the squarefree radical, which would retain even factors.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Compute

open Purelib.Polynomial

/-- The squarefree fast path retains the normalized input with square factor one.

The supplied certificate concerns the exact normalized input; no multiplicity
basis is computed and no coefficient or scalar is replaced. -/
@[expose] def ofSquarefreeNormalized (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (squarefree : Basic.SquarefreeCertificate polynomial.normalize) :
    Basic.Reduction polynomial := by
  refine
    { squareFactor := Basic.DensePolynomial.constant 1
      radicand := polynomial.normalize
      squareFactorNonzero := (Leading.LeadingTerm.constant one_ne_zero).nonzero
      radicandNonzero := by simpa only [Basic.DensePolynomial.isZero_normalize] using nonzero
      squareFactorNormalized := (Leading.LeadingTerm.constant one_ne_zero).normalized
      radicandNormalized := Basic.DensePolynomial.normalize_normalize polynomial
      squarefree := squarefree
      identity := ?_ }
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  simp only [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_constant,
    Basic.DensePolynomial.eval_normalize, one_mul, -eq_self]
  rfl

set_option backward.match.sparseCases false in
/-- Inspect the already computed occurrence list before overlap refinement.

For a single squarefree occurrence, retain the input and avoid rebuilding its
multiplicity basis. Every other case uses the same parity-aware reduction. -/
@[expose] def ofDecomposition (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (decomposition : Decomposition polynomial.normalize) :
    Basic.Reduction polynomial :=
  match single : decomposition.factors with
  | [factor] => ofSquarefreeNormalized polynomial nonzero
      (by
        have difference : (polynomial.normalize - factor.polynomial).isZero = true := by
          apply NonzeroEvaluation.difference_isZero_of_candidate_evals
          intro point _
          have identity := decomposition.evalIdentity point
          simpa only [single, Decomposition.Basic.factorProduct,
            Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_constant, mul_one] using identity
        have same := Extensionality.normalized_eq_of_sub_isZero
          (Basic.DensePolynomial.normalize_normalize polynomial) factor.normalized difference
        rw [same]
        exact factor.squarefree)
  | _ => by
      let basis := decomposition.multiplicityBasis
      let entries := Multiplicity.Basis.Positive.positiveEntries basis.entries
      let scalar := Multiplicity.Basis.Positive.unitValue basis.entries
      have scalarNonzero : scalar ≠ 0 := Multiplicity.Basis.Positive.unitValue_ne_zero basis.entries
      let squareFactor := Products.halfProduct entries
      let radicand := Basic.DensePolynomial.constant scalar *
        Products.oddProduct entries
      have pairwise : entries.Pairwise
          (fun left right => Multiplicity.CoprimeRelation left.part right.part) :=
        Multiplicity.Basis.Positive.positiveEntries_pairwise basis.pairwise
      refine
        { squareFactor := squareFactor
          radicand := radicand
          squareFactorNonzero := Products.halfProduct_nonzero entries
          radicandNonzero := Basic.DensePolynomial.isZero_mul_eq_false (Leading.LeadingTerm.constant
            scalarNonzero).nonzero
            (Products.oddProduct_nonzero entries)
          squareFactorNormalized := Products.halfProduct_normalized entries
          radicandNormalized := Basic.DensePolynomial.normalize_mul _ _
          squarefree := Product.product
            (Leading.LeadingTerm.constant scalarNonzero).nonzero
              (Products.oddProduct_nonzero entries)
            (Constants.constant scalar scalarNonzero)
            (Products.oddProductSquarefree entries pairwise)
            (Coprime.Operations.CoprimeCertificate.symm
              (Coprime.Operations.CoprimeCertificate.constantRightOfNe
                (Products.oddProduct_nonzero entries) scalar scalarNonzero))
          identity := ?_ }
      apply Factorization.Identity.factorizationOfCandidateEvals
      intro point _
      have original := decomposition.eval_positiveMultiplicityEntries point
      change polynomial.normalize.eval point = scalar * Multiplicity.Basis.Positive.positiveValue entries
        point at original
      rw [Basic.DensePolynomial.eval_normalize, Products.parityIdentity]
        at original
      dsimp only [squareFactor, radicand]
      simp only [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_constant]
      calc
        polynomial.eval point = scalar *
            ((Products.halfProduct entries).eval point *
              (Products.halfProduct entries).eval point *
              (Products.oddProduct entries).eval point) := original
        _ = _ := by ring1

/-- A singleton decomposition retains square factor one and the original normalized radicand. -/
theorem ofDecomposition_singleton (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (decomposition : Decomposition polynomial.normalize)
    (factor : Decomposition.Basic.Factor) (single : decomposition.factors = [factor]) :
    (ofDecomposition polynomial nonzero decomposition).squareFactor = Basic.DensePolynomial.constant 1 ∧
      (ofDecomposition polynomial nonzero decomposition).radicand = polynomial.normalize := by
  unfold ofDecomposition
  split
  · exact ⟨rfl, rfl⟩
  · rename_i notSingle
    exact False.elim (notSingle factor single)

/-- Squarefree input really takes the singleton fast path: this follows from
the computed gcd certificate, not a heuristic on degree or coefficient shape. -/
theorem squarefree_decomposition_length (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (normalized : polynomial.normalize = polynomial) (nonzero : polynomial.isZero = false)
    (positive : 0 < polynomial.natDegree)
    (squarefree : Basic.SquarefreeCertificate polynomial) :
    (Decomposition.Compute.decomposeNormalized polynomial normalized nonzero
      positive).factors.length = 1 := by
  have degreeZero : (GCD.extendedGCD polynomial
      (GCD.derivative polynomial)).gcd.natDegree = 0 := by
    rw [squarefree.gcd_eq_constant]
    exact (Leading.LeadingTerm.constant squarefree.unit_ne_zero).degree_eq
  delta Decomposition.Compute.decomposeNormalized
    Dense.Gaussian.Squarefree.Decomposition.Compute.decomposeNormalized._unary
  have fixStep {α : Sort _} {motive : α → Sort _}
      (measure : α → Nat)
      (step : (x : α) → ((y : α) → measure y < measure x → motive y) → motive x)
      (x : α) :
      WellFounded.Nat.fix measure step x =
        step x (fun y smaller => WellFounded.Nat.fix.go measure step (measure x) y smaller) := by
    have changeFuel {left right : Nat} (same : left = right)
        (leftBound : measure x < left) (rightBound : measure x < right) :
        WellFounded.Nat.fix.go measure step left x leftBound =
          WellFounded.Nat.fix.go measure step right x rightBound := by
      cases same
      rfl
    exact (changeFuel (WellFounded.Nat.eager_eq (measure x + 1))
      (WellFounded.Nat.eager_eq _ ▸ Nat.lt_add_one _) (Nat.lt_add_one _)).trans rfl
  rw [fixStep]
  dsimp only
  split
  · rfl
  · rename_i common outcome
    unfold Decision.squarefreeOutcome Coprime.Decision.coprimeOutcome
      at outcome
    rw [dif_pos degreeZero] at outcome
    cases outcome

/-- Constants retain their entire scalar as the reduced radicand. -/
@[expose] def ofConstant (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false) (degreeZero : polynomial.natDegree = 0) :
    Basic.Reduction polynomial := by
  have normalized : polynomial.normalize = Basic.DensePolynomial.constant polynomial.leadingCoeff :=
    Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
  have coefficientNonzero : polynomial.leadingCoeff ≠ 0 := Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
  refine
    { squareFactor := Basic.DensePolynomial.constant 1
      radicand := polynomial.normalize
      squareFactorNonzero := (Leading.LeadingTerm.constant one_ne_zero).nonzero
      radicandNonzero := by simpa only [Basic.DensePolynomial.isZero_normalize] using nonzero
      squareFactorNormalized := (Leading.LeadingTerm.constant one_ne_zero).normalized
      radicandNormalized := Basic.DensePolynomial.normalize_normalize polynomial
      squarefree := ?_
      identity := ?_ }
  · rw [normalized]
    exact Constants.constant polynomial.leadingCoeff coefficientNonzero
  · apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    simp only [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_constant,
      Basic.DensePolynomial.eval_normalize, one_mul, -eq_self]
    rfl

set_option genInjectivity false in
/-- Total reduction: zero is an explicit branch; every nonzero input gets
computed, certified square and squarefree factors, even when it is singular. -/
inductive Outcome (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The input polynomial is certified zero. -/ | zero (certificate : polynomial.isZero = true)
  /-- The nonzero input has a certified square factor and squarefree residual radicand. -/ | reduced (nonzero :
    polynomial.isZero = false) (result : Basic.Reduction polynomial)

constructive_injectivity Outcome

/-- Compute a certified parity reduction of any Gaussian polynomial.

Zero has an explicit certificate; constants retain their scalar; positive-degree inputs reuse their computed
decomposition and its squarefree fast path. -/
@[expose] def reduce (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) : Outcome polynomial :=
  match Decomposition.Compute.preprocess polynomial with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .reduced nonzero (ofConstant polynomial nonzero degreeZero)
  | .positive result => .reduced result.nonzero
      (ofDecomposition polynomial result.nonzero result.decomposition)

/-- The total constructor preserves an already squarefree normalized input
literally.  This is a property of the coefficient-first algorithm, not a
certificate required by that algorithm's public argument list. -/
theorem reduce_preserves_squarefree (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : polynomial.isZero = false)
    (squarefree : Basic.SquarefreeCertificate polynomial.normalize) :
    match reduce polynomial with
    | .zero _ => False
    | .reduced _ result =>
        result.squareFactor = Basic.DensePolynomial.constant 1 ∧ result.radicand = polynomial.normalize := by
  have notZero : ¬ polynomial.isZero = true := by rw [nonzero]; decide
  by_cases degreeZero : polynomial.natDegree = 0
  · have preprocessing : Decomposition.Compute.preprocess polynomial =
        .constant nonzero degreeZero := by
      unfold Decomposition.Compute.preprocess
      rw [dif_neg notZero, dif_pos degreeZero]
    rw [reduce, preprocessing]
    exact ⟨rfl, rfl⟩
  · have normalizedNonzero : polynomial.normalize.isZero = false := by
      simpa only [Basic.DensePolynomial.isZero_normalize] using nonzero
    have positive : 0 < polynomial.normalize.natDegree := by
      simpa only [Basic.DensePolynomial.natDegree_normalize] using Nat.pos_of_ne_zero degreeZero
    let decomposition := Decomposition.Compute.decomposeNormalized polynomial.normalize
      (Basic.DensePolynomial.normalize_normalize polynomial) normalizedNonzero positive
    have preprocessing : Decomposition.Compute.preprocess polynomial =
        .positive ⟨nonzero, Nat.pos_of_ne_zero degreeZero, decomposition⟩ := by
      unfold Decomposition.Compute.preprocess
      rw [dif_neg notZero, dif_neg degreeZero]
    rw [reduce, preprocessing]
    have length := squarefree_decomposition_length polynomial.normalize
      (Basic.DensePolynomial.normalize_normalize polynomial) normalizedNonzero positive squarefree
    have single : ∃ factor, decomposition.factors = [factor] := by
      cases factorsEquation : decomposition.factors with
      | nil =>
          have impossible : (0 : Nat) = 1 := by rw [factorsEquation] at length; exact length
          exact Nat.noConfusion impossible
      | cons factor remaining =>
          cases remaining with
          | nil => exact ⟨factor, rfl⟩
          | cons next rest =>
              have impossible : rest.length + 2 = 1 := by rw [factorsEquation] at length; exact length
              exact Nat.noConfusion (Nat.noConfusion impossible (fun zero => zero))
    obtain ⟨factor, single⟩ := single
    exact ofDecomposition_singleton polynomial nonzero decomposition factor single

end Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Compute

end
