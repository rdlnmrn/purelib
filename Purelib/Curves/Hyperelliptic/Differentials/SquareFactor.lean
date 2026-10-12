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
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

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
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The certified square-factor decomposition of the original polynomial. -/
abbrev Reduction := SquareFactor.Basic.Reduction

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
def exponent : Curves.Hyperelliptic.Differentials.SquareFactor.Request → Nat
  | .original exponent | .normalized exponent => exponent

/-- Construct the monomial polynomial with coefficient one at the requested exponent. -/
def power (request : Curves.Hyperelliptic.Differentials.SquareFactor.Request) : GaussianPolynomial :=
  DensePolynomial.shift request.exponent (DensePolynomial.constant 1)

/-- Evaluating the request monomial gives the corresponding power of the point. -/
theorem power_eval (request : Curves.Hyperelliptic.Differentials.SquareFactor.Request) (point :
  Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) :
    request.power.eval point = point ^ request.exponent := by
  rw [power, DensePolynomial.eval_shift,
    DensePolynomial.eval_constant, Data.Gaussian.Basic.one_mul]

/-- Select the square factor for an original-coordinate request and one for a normalized request. -/
def weightDenominator {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial}
    (reduction : Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial) :
      Curves.Hyperelliptic.Differentials.SquareFactor.Request →
      Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial
  | .original _ => reduction.squareFactor
  | .normalized _ => DensePolynomial.constant 1

/-- The rational weight denominator is a nonzero polynomial for either request convention. -/
theorem weightDenominator_nonzero {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial}
    (reduction : Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial) (request :
      Curves.Hyperelliptic.Differentials.SquareFactor.Request) :
    (request.weightDenominator reduction).isZero = false := by
  cases request with
  | original _ => exact reduction.squareFactorNonzero
  | normalized _ => exact (LeadingTerm.constant
      (one_ne_zero : (1 : Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) ≠ 0)).nonzero

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request in
/-- Express the request numerator in the original sheet coordinate.

A normalized-coordinate request acquires the evaluated square factor; an original-coordinate request keeps its monomial
numerator. -/
def originalNumerator {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial}
    (reduction : Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial) (request :
      Curves.Hyperelliptic.Differentials.SquareFactor.Request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) : Gaussian :=
  match request with
  | .original exponent => point ^ exponent
  | .normalized exponent => reduction.squareFactor.eval point * point ^ exponent

end Request

set_option genInjectivity false in
/-- One retained Euclidean cancellation, consumed by all downstream tests and coefficient evaluations instead of
recalculating the gcd. -/
structure Weight {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) where
  /-- The retained Euclidean cancellation of the monomial and its requested weight denominator. -/ cancellation :
    Reduction.Basic.ReducedPair request.power
    (request.weightDenominator reduction)

constructive_injectivity Weight

/-- Compile a differential request into one retained reduced rational weight.

The Euclidean reduction is computed once and its certificate supplies subsequent denominator checks and evaluation
identities. -/
def compile {polynomial : GaussianPolynomial}
    (reduction : Reduction polynomial) (request :
      Request) : Weight
      reduction request :=
  ⟨Build.reduce request.power (request.weightDenominator reduction)
    (request.weightDenominator_nonzero reduction)⟩

namespace Weight

/-- Read the reduced numerator polynomial from the retained cancellation. -/
def numerator {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) : GaussianPolynomial :=
  weight.cancellation.numeratorReduced

/-- Read the reduced denominator polynomial from the retained cancellation. -/
def denominator {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) : GaussianPolynomial :=
  weight.cancellation.denominatorReduced

/-- Exact expression of the cancelled rational weight. Its use as a value is guarded by the denominator evidence below.
-/
def expression {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) : Gaussian :=
  weight.numerator.eval point / weight.denominator.eval point

/-- The path displacement is deliberately absent; integration applies `dx` once, after this coefficient has been
transported. -/
def coefficient {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point root :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) : Gaussian :=
  weight.expression point / root

/-- The original monomial and reduced numerator satisfy the cleared rational-weight identity at every point. -/
theorem crossIdentity {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) :
    point ^ request.exponent * weight.denominator.eval point =
      weight.numerator.eval point * (request.weightDenominator reduction).eval point := by
  rw [← request.power_eval point, weight.cancellation.numerator_eval point,
    weight.cancellation.denominator_eval point]
  dsimp only [numerator,
    denominator]
  ring1

/-- Where the original weight denominator is nonzero, the reduced weight equals the original rational expression. -/
theorem expression_eq {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
  Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian)
    (nonzero : (request.weightDenominator reduction).eval point ≠ 0) :
    weight.expression point =
      point ^ request.exponent / (request.weightDenominator reduction).eval point := by
  have cancelled := weight.cancellation.quotient_eval_eq_reduced point nonzero
  rw [request.power_eval point] at cancelled
  simpa only [expression,
    numerator,
    denominator, Algebra.Field.ExplicitField.div_eq_mul_inv]
    using cancelled.symm

/-- A zero of the reduced denominator cannot also be a numerator zero. The cached Bézout identity establishes this
without rerunning Euclid. -/
theorem numerator_nonzero_at_denominator_zero
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian)
    (zero : weight.denominator.eval point = 0) : weight.numerator.eval point ≠ 0 := by
  intro numeratorZero
  have identity := weight.cancellation.reduced_identity point
  change 1 = _ * weight.numerator.eval point + _ * weight.denominator.eval point at identity
  rw [numeratorZero, zero, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.zero_add]
    at identity
  exact one_ne_zero identity

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
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point root :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) (rootNonzero : root ≠ 0) :
    weight.coefficient point root * Curves.Hyperelliptic.Differentials.SquareFactor.coordinate reduction point root =
      request.originalNumerator reduction point := by
  have rawNonzero : (request.weightDenominator reduction).eval point ≠ 0 := by
    cases request with
    | original _ => exact squareNonzero
    | normalized _ =>
      simpa only [Curves.Hyperelliptic.Differentials.SquareFactor.Request.weightDenominator,
        DensePolynomial.eval_constant] using
        (one_ne_zero : (1 : Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) ≠ 0)
  rw [coefficient,
    Curves.Hyperelliptic.Differentials.SquareFactor.coordinate]
  calc
    weight.expression point / root * (reduction.squareFactor.eval point * root) =
        (weight.expression point / root * root) * reduction.squareFactor.eval point := by
          ring1
    _ = weight.expression point * reduction.squareFactor.eval point := by
      rw [Algebra.Field.ExplicitField.div_mul_cancel _ rootNonzero]
    _ = _ := by
      rw [weight.expression_eq point rawNonzero]
      cases request with
      | original exponent => exact Algebra.Field.ExplicitField.div_mul_cancel _ squareNonzero
      | normalized exponent =>
          simp only [Curves.Hyperelliptic.Differentials.SquareFactor.Request.exponent,
            Curves.Hyperelliptic.Differentials.SquareFactor.Request.weightDenominator,
            Curves.Hyperelliptic.Differentials.SquareFactor.Request.originalNumerator,
            DensePolynomial.eval_constant, Algebra.Field.ExplicitField.div_eq_mul_inv]
          have inverseOne : (1 : Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian)⁻¹ = 1 := by
            simpa only [Data.Gaussian.Basic.one_mul] using Algebra.Field.ExplicitField.mul_inv_cancel
              (1 : Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) one_ne_zero
          rw [inverseOne, Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.mul_comm]

/-- The reduced differential coefficient equals the original-coordinate quotient away from square-factor and sheet
zeros. -/
theorem coefficient_transport
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point root :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) (rootNonzero : root ≠ 0) :
    weight.coefficient point root =
      request.originalNumerator reduction point / Curves.Hyperelliptic.Differentials.SquareFactor.coordinate reduction
        point root := by
  have nonzero : Curves.Hyperelliptic.Differentials.SquareFactor.coordinate reduction point root ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct squareNonzero rootNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne nonzero
  exact (weight.coefficient_cleared point root squareNonzero rootNonzero).trans
    (Algebra.Field.ExplicitField.div_mul_cancel _ nonzero).symm

/-- Changing the sheet sign negates the differential coefficient. -/
theorem coefficient_neg
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point root :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) :
    weight.coefficient point (-root) = -weight.coefficient point root :=
  Algebra.Field.ExplicitField.div_neg _ _

/-- Exact point classification after cancellation. The second accepted case explicitly records that the original
coordinate formula is undefined. This is a point test only, not evidence for a whole path. -/
inductive PointOutcome
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) : Type where
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
    {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {reduction :
      Curves.Hyperelliptic.Differentials.SquareFactor.Reduction polynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request} (weight :
      Curves.Hyperelliptic.Differentials.SquareFactor.Weight reduction request) (point :
      Curves.Hyperelliptic.Differentials.SquareFactor.Gaussian) :
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
