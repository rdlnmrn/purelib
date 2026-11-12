module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Compute
import Purelib.RationalFunctions.Reduction.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Leading
meta import Purelib.Elab.Deriving.Repr
import Purelib.RationalFunctions.Reduction.Evaluation
public import Purelib.RationalFunctions.Reduction.Build
public import Purelib.Algebra.Quadratic.Pair.Polynomial
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor

open Purelib.Polynomial.Dense.Leading
open _root_.Purelib.Polynomial.Dense.Leading renaming CoefficientPolynomial -> Dense

open Purelib.RationalFunctions

open Purelib.RationalFunctions.Reduction

@[expose] public section

/-!
# Differential coefficients under square-factor reduction

For the computed identity `p = s²q`, the coordinate map is `y = s(x)z`.
Original `x^k dx/y` and normalized `x^k dx/z` are distinct requests.  The
former compiles to the rational weight `x^k/s(x)`; the latter has weight
`x^k`, and original numerator `s(x)x^k`.  Euclid cancels the weight before
checking its denominator.  No genus or holomorphic-basis index is involved.

These are exact finite coefficient and pointwise transport laws, not yet a
path integration or branch-continuation theorem.  At a removed coordinate
zero the reduced expression is an extension, not a value of the undefined
original quotient.  A weight pole is not a claim of integral divergence.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.SquareFactor

/-- Exact Gaussian rational coefficients for the square-factor differential calculation. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials used by the differential requests. -/
abbrev GaussianPolynomial := Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The certified square-factor decomposition of the original polynomial. -/
abbrev Reduction := Basic.Reduction

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- The coordinate in which the requested differential has numerator `x^k`. Both constructors allow every finite
exponent, including genus-zero curves. -/
inductive Request where
  /-- Request x to the specified power divided by the original sheet coordinate. -/ | original (exponent : Nat)
  /-- Request x to the specified power divided by the normalized sheet coordinate. -/ | normalized (exponent : Nat)
deriving DecidableEq

constructive_injectivity Request

derive_exposed_repr Request

namespace Request

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request in
/-- Read the finite monomial exponent from either differential coordinate convention. -/
def exponent : Request → Nat
  | .original exponent | .normalized exponent => exponent

/-- Construct the monomial polynomial with coefficient one at the requested exponent. -/
def power (request : Request) : GaussianPolynomial :=
  shift request.exponent (constant 1)

/-- Evaluating the request monomial gives the corresponding power of the point. -/
theorem power_eval (request : Request) (point :
  Gaussian) :
    request.power.eval point = point ^ request.exponent := by
  rw [power, eval_shift,
    eval_constant, Data.Gaussian.Basic.one_mul]

/-- Select the square factor for an original-coordinate request and one for a normalized request. -/
def weightDenominator {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) :
      Request →
      GaussianPolynomial
  | .original _ => reduction.squareFactor
  | .normalized _ => constant 1

/-- The rational weight denominator is a nonzero polynomial for either request convention. -/
theorem weightDenominator_nonzero {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) :
    (request.weightDenominator reduction).isZero = false := by
  cases request with
  | original _ => exact reduction.squareFactorNonzero
  | normalized _ => exact (LeadingTerm.constant
      (one_ne_zero : (1 : Gaussian) ≠ 0)).nonzero

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request in
/-- Express the request numerator in the original sheet coordinate.

A normalized-coordinate request acquires the evaluated square factor; an original-coordinate request keeps its monomial
numerator. -/
def originalNumerator {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) (point :
      Gaussian) : Gaussian :=
  match request with
  | .original exponent => point ^ exponent
  | .normalized exponent => reduction.squareFactor.eval point * point ^ exponent

/-- Retain the request numerator as finite coefficients in the original coordinate. -/
def originalNumeratorPolynomial {polynomial : GaussianPolynomial} (reduction : Reduction polynomial)
    (request : Request) : GaussianPolynomial :=
  match request with
  | .original _ => request.power
  | .normalized _ => reduction.squareFactor * request.power

/-- The retained numerator coefficients evaluate to the original request numerator. -/
theorem originalNumeratorPolynomial_eval {polynomial : GaussianPolynomial} (reduction : Reduction polynomial)
    (request : Request) (point : Gaussian) :
    (request.originalNumeratorPolynomial reduction).eval point = request.originalNumerator reduction point := by
  cases request with
  | original exponent => exact Request.power_eval _ point
  | normalized exponent =>
    change (reduction.squareFactor * (Request.normalized exponent).power).eval point = _
    rewrite [DensePolynomial.eval_mul, Request.power_eval]
    rfl

end Request

open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)

/-- Compile the cancelled weight divided by the same normalized generator into exact quadratic coefficients.

The retained denominator includes the original radicand; source-coordinate
guards remain separately owned by the square-factor request. -/
def algebraicSpec {polynomial : GaussianPolynomial} (reduction : Reduction polynomial) (request : Request)
    (cancellation : Reduction.Basic.ReducedPair request.power (request.weightDenominator reduction)) :
    Expression reduction.radicand :=
  ⟨⟨0, cancellation.numeratorReduced⟩, cancellation.denominatorReduced * reduction.radicand⟩

/-- The original coordinate map is the square factor times the same normalized generator. -/
def coordinateSpec {polynomial : GaussianPolynomial} (reduction : Reduction polynomial) :
    Expression reduction.radicand :=
  ⟨⟨0, reduction.squareFactor⟩, DensePolynomial.constant 1⟩

set_option genInjectivity false in
/-- One retained Euclidean cancellation, consumed by all downstream tests and coefficient evaluations instead of
recalculating the gcd. -/
structure Weight {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) where
  /-- The retained Euclidean cancellation of the monomial and its requested weight denominator. -/ cancellation :
    Basic.ReducedPair request.power
    (request.weightDenominator reduction)
  /-- The cached exact coefficient at the original normalized generator. -/
  algebraic : Expression reduction.radicand
  /-- The cached coefficients use this same Euclidean cancellation and radicand. -/
  algebraic_eq : algebraic = algebraicSpec reduction request cancellation

constructive_injectivity Weight

/-- Compile a differential request into one retained reduced rational weight.

The Euclidean reduction is computed once and its certificate supplies subsequent denominator checks and evaluation
identities. -/
def compile {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) : Weight
      reduction request :=
  let cancellation := Build.reduce request.power (request.weightDenominator reduction)
    (request.weightDenominator_nonzero reduction)
  ⟨cancellation, algebraicSpec reduction request cancellation, rfl⟩

namespace Weight

/-- Read the reduced numerator polynomial from the retained cancellation. -/
def numerator {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) : GaussianPolynomial :=
  weight.cancellation.numeratorReduced

/-- Read the reduced denominator polynomial from the retained cancellation. -/
def denominator {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) : GaussianPolynomial :=
  weight.cancellation.denominatorReduced

/-- Exact expression of the cancelled rational weight. Its use as a value is guarded by the denominator evidence below.
-/
def expression {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian) : Gaussian :=
  weight.numerator.eval point / weight.denominator.eval point

/-- The path displacement is deliberately absent; integration applies `dx` once, after this coefficient has been
transported. -/
def coefficient {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point root :
      Gaussian) : Gaussian :=
  weight.expression point / root

/-- The original monomial and reduced numerator satisfy the cleared rational-weight identity at every point. -/
theorem crossIdentity {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian) :
    point ^ request.exponent * weight.denominator.eval point =
      weight.numerator.eval point * (request.weightDenominator reduction).eval point := by
  rw [← request.power_eval point, weight.cancellation.numerator_eval point,
    weight.cancellation.denominator_eval point]
  dsimp only [numerator,
    denominator]
  ring1

/-- Where the original weight denominator is nonzero, the reduced weight equals the original rational expression. -/
theorem expression_eq {polynomial : GaussianPolynomial} {reduction :
  Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian)
    (nonzero : (request.weightDenominator reduction).eval point ≠ 0) :
    weight.expression point =
      point ^ request.exponent / (request.weightDenominator reduction).eval point := by
  have cancelled := weight.cancellation.quotient_eval_eq_reduced point nonzero
  rw [request.power_eval point] at cancelled
  simpa only [expression,
    numerator,
    denominator, ExplicitField.div_eq_mul_inv]
    using cancelled.symm

/-- A zero of the reduced denominator cannot also be a numerator zero. The cached Bézout identity establishes this
without rerunning Euclid. -/
theorem numerator_nonzero_at_denominator_zero
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian)
    (zero : weight.denominator.eval point = 0) : weight.numerator.eval point ≠ 0 := by
  intro numeratorZero
  have identity := weight.cancellation.reduced_identity point
  change 1 = _ * weight.numerator.eval point + _ * weight.denominator.eval point at identity
  rw [numeratorZero, zero, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.zero_add]
    at identity
  exact one_ne_zero identity

/-- The reduced denominator and radicand supply the exact algebraic coefficient's guard. -/
theorem algebraic_defined {polynomial : GaussianPolynomial} {reduction : Reduction polynomial} {request : Request}
    (weight : Weight reduction request) (point : Gaussian)
    (denominatorNonzero : weight.denominator.eval point ≠ 0)
    (radicandNonzero : reduction.radicand.eval point ≠ 0) : weight.algebraic.Defined point := by
  rewrite [weight.algebraic_eq]
  change (weight.denominator * reduction.radicand).eval point ≠ 0
  rewrite [DensePolynomial.eval_mul]
  exact Algebra.Field.ExplicitField.mul_ne_zero denominatorNonzero radicandNonzero

/-- The cached divided coefficient reads back at the same original evaluated radicand. -/
theorem algebraic_evaluate {polynomial : GaussianPolynomial} {reduction : Reduction polynomial} {request : Request}
    (weight : Weight reduction request) (point : Gaussian) :
    weight.algebraic.evaluate point =
      (⟨0, weight.numerator.eval point / (weight.denominator.eval point * reduction.radicand.eval point)⟩ :
        Algebra.Quadratic.Pair Gaussian (-reduction.radicand.eval point)) := by
  rewrite [weight.algebraic_eq]
  apply Algebra.Quadratic.Pair.ext
  · change (0 : GaussianPolynomial).eval point / _ = 0
    rewrite [DensePolynomial.eval_zero, Algebra.Field.ExplicitField.zero_div]
    rfl
  · change weight.numerator.eval point / (weight.denominator * reduction.radicand).eval point = _
    rewrite [DensePolynomial.eval_mul]
    rfl

/-- The exact coefficient times the original coordinate map gives the original numerator on cleared coefficients.

The same cached cancellation supplies both request conventions. No selected
root or numerical sample is needed for this finite coefficient certificate. -/
theorem algebraic_cleared {polynomial : GaussianPolynomial} {reduction : Reduction polynomial} {request : Request}
    (weight : Weight reduction request) :
    (weight.algebraic.mul (coordinateSpec reduction)).Equal
      (Expression.scalar (request.originalNumeratorPolynomial reduction)) := by
  apply Expression.equal_of_cross_eval
  · intro point
    have cross := weight.crossIdentity point
    rewrite [weight.algebraic_eq]
    dsimp only [Expression.mul, algebraicSpec, coordinateSpec, Expression.scalar, Algebra.Quadratic.Pair.scalar]
    rewrite [Algebra.Quadratic.Pair.mul_re]
    dsimp only
    simp only [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_zero, DensePolynomial.eval_neg,
      DensePolynomial.eval_constant, Request.originalNumeratorPolynomial_eval]
    change (0 * 0 - (-reduction.radicand.eval point) * weight.numerator.eval point *
        reduction.squareFactor.eval point) * 1 = request.originalNumerator reduction point *
      ((weight.denominator.eval point * reduction.radicand.eval point) * 1)
    cases request with
    | original exponent =>
      change point ^ exponent * weight.denominator.eval point =
        weight.numerator.eval point * reduction.squareFactor.eval point at cross
      change _ = point ^ exponent * _
      calc
        _ = (weight.numerator.eval point * reduction.squareFactor.eval point) * reduction.radicand.eval point := by
          ring1
        _ = _ := by rewrite [← cross]; ring1
    | normalized exponent =>
      change point ^ exponent * weight.denominator.eval point =
        weight.numerator.eval point * (DensePolynomial.constant 1).eval point at cross
      rewrite [DensePolynomial.eval_constant, Data.Gaussian.Basic.mul_one] at cross
      change _ = (reduction.squareFactor.eval point * point ^ exponent) * _
      calc
        _ = weight.numerator.eval point * reduction.squareFactor.eval point * reduction.radicand.eval point := by
          ring1
        _ = _ := by rewrite [← cross]; ring1
  · intro point
    rewrite [weight.algebraic_eq]
    dsimp only [Expression.mul, algebraicSpec, coordinateSpec, Expression.scalar, Algebra.Quadratic.Pair.scalar]
    rewrite [Algebra.Quadratic.Pair.mul_im]
    dsimp only
    simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_zero,
      DensePolynomial.eval_constant]
    ring1

end Weight

/-- Lift a chosen reduced root, rather than choosing a second unrelated root of the original equation. -/
def coordinate {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (point root :
      Gaussian) : Gaussian :=
  reduction.squareFactor.eval point * root

/-- Multiplying a normalized sheet root by the evaluated square factor gives a root of the original polynomial. -/
theorem coordinate_square {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (point root :
      Gaussian)
    (rootEquation : root ^ 2 = reduction.radicand.eval point) :
    coordinate reduction point root ^ 2 = polynomial.eval point := by
  rw [coordinate, pow_two]
  have square : (reduction.squareFactor.eval point * root) *
      (reduction.squareFactor.eval point * root) =
      reduction.squareFactor.eval point * reduction.squareFactor.eval point * (root ^ 2) := by
    rw [pow_two]
    ring1
  rw [square, rootEquation]
  exact (reduction.evalIdentity point).symm

/-- Negating the normalized sheet root negates its lifted original coordinate. -/
theorem coordinate_neg {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (point root :
      Gaussian) :
    coordinate reduction point (-root) =
      -coordinate reduction point root := by
  exact mul_neg _ _

namespace Weight

/-- Denominator-cleared differential identity on the original coordinate domain. The numerator differs for the two
request constructors. -/
theorem coefficient_cleared
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point root :
      Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) (rootNonzero : root ≠ 0) :
    weight.coefficient point root * coordinate reduction point root =
      request.originalNumerator reduction point := by
  have rawNonzero : (request.weightDenominator reduction).eval point ≠ 0 := by
    cases request with
    | original _ => exact squareNonzero
    | normalized _ =>
      simpa only [Request.weightDenominator,
        eval_constant] using
        (one_ne_zero : (1 : Gaussian) ≠ 0)
  rw [coefficient,
    coordinate]
  calc
    weight.expression point / root * (reduction.squareFactor.eval point * root) =
        (weight.expression point / root * root) * reduction.squareFactor.eval point := by
          ring1
    _ = weight.expression point * reduction.squareFactor.eval point := by
      rw [ExplicitField.div_mul_cancel _ rootNonzero]
    _ = _ := by
      rw [weight.expression_eq point rawNonzero]
      cases request with
      | original exponent => exact ExplicitField.div_mul_cancel _ squareNonzero
      | normalized exponent =>
          simp only [Request.exponent,
            Request.weightDenominator,
            Request.originalNumerator,
            eval_constant, ExplicitField.div_eq_mul_inv]
          have inverseOne : (1 : Gaussian)⁻¹ = 1 := by
            simpa only [Data.Gaussian.Basic.one_mul] using ExplicitField.mul_inv_cancel
              (1 : Gaussian) one_ne_zero
          rw [inverseOne, Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.mul_comm]

/-- The reduced differential coefficient equals the original-coordinate quotient away from square-factor and sheet
zeros. -/
theorem coefficient_transport
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point root :
      Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) (rootNonzero : root ≠ 0) :
    weight.coefficient point root =
      request.originalNumerator reduction point / coordinate reduction
        point root := by
  have nonzero : coordinate reduction point root ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct squareNonzero rootNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne nonzero
  exact (weight.coefficient_cleared point root squareNonzero rootNonzero).trans
    (ExplicitField.div_mul_cancel _ nonzero).symm

/-- Changing the sheet sign negates the differential coefficient. -/
theorem coefficient_neg
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point root :
      Gaussian) :
    weight.coefficient point (-root) = -weight.coefficient point root :=
  ExplicitField.div_neg _ _

/-- Exact point classification after cancellation. The second accepted case explicitly records that the original
coordinate formula is undefined. This is a point test only, not evidence for a whole path. -/
inductive PointOutcome
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian) : Type where
  /-- Both coordinate descriptions are defined and the normalized point is not a branch point. -/ | regular
    (denominatorNonzero : weight.denominator.eval point ≠ 0)
      (radicandNonzero : reduction.radicand.eval point ≠ 0)
      (squareNonzero : reduction.squareFactor.eval point ≠ 0)
  /-- The reduced coefficient is regular but the original coordinate vanishes at a removed square-factor zero. -/ |
    removedCoordinateZero (denominatorNonzero : weight.denominator.eval point ≠ 0)
      (radicandNonzero : reduction.radicand.eval point ≠ 0)
      (squareZero : reduction.squareFactor.eval point = 0)
  /-- The reduced denominator vanishes and the cached numerator is certified nonzero. -/ | weightPole (denominatorZero :
    weight.denominator.eval point = 0)
      (numeratorNonzero : weight.numerator.eval point ≠ 0)
  /-- The normalized radicand vanishes while the reduced weight denominator is nonzero. -/ | branchPoint
    (denominatorNonzero : weight.denominator.eval point ≠ 0)
      (radicandZero : reduction.radicand.eval point = 0)

/-- Classify a point using the retained cancelled weight and square-factor reduction.

Exact tests distinguish a weight pole, a normalized branch point, a removed coordinate zero and a regular point. Each
result retains the equations or nonvanishing evidence establishing that case. -/
def checkPoint
    {polynomial : GaussianPolynomial} {reduction :
      Reduction polynomial}
    {request : Request} (weight :
      Weight reduction request) (point :
      Gaussian) :
    weight.PointOutcome point :=
  if denominatorZero : weight.denominator.eval point = 0 then
    .weightPole denominatorZero (weight.numerator_nonzero_at_denominator_zero point denominatorZero)
  else if radicandZero : reduction.radicand.eval point = 0 then
    .branchPoint denominatorZero radicandZero
  else if squareZero : reduction.squareFactor.eval point = 0 then
    .removedCoordinateZero denominatorZero radicandZero squareZero
  else .regular denominatorZero radicandZero squareZero

end Weight

set_option genInjectivity false in
/-- Raw coefficients prepare both the reduction and the cancelled weight. Nonzero constants and square-times-constant
inputs are retained here: this is the separate differential interface, not a standard period-basis API. -/
structure Prepared (polynomial : GaussianPolynomial) (request :
  Request) where
  /-- The computed square-factor decomposition of the original polynomial. -/ reduction :
    Reduction polynomial
  /-- The compiled reduced weight indexed by this exact decomposition and differential request. -/ weight :
    Weight reduction request

constructive_injectivity Prepared

/-- Compute a square-factor reduction and compile its differential weight.

The zero polynomial returns its certified zero equation; every nonzero input retains the computed reduction and the
cancellation for the requested coordinate convention. -/
def prepare (polynomial : GaussianPolynomial) (request :
  Request) :
    Except (PLift (polynomial.isZero = true)) (Prepared polynomial
      request) :=
  match Compute.reduce polynomial with
  | .zero zero => .error ⟨zero⟩
  | .reduced _ reduction => .ok ⟨reduction, compile reduction request⟩

end Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
