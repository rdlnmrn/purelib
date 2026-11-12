module
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
public import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
public import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Approximation.Gaussian.Provenance.Power.Nonzero
import Purelib.Algebra.Ring.Multiplication

open Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
# Operational coordinate and differential transport on the retained root

Finite root readings need not satisfy a polynomial exactly.  The coordinate
law here is instead an operational equivalence of coherent names.  Multiplying
the retained root name by the exact square factor gives a name whose square
is the original polynomial.  On the checked original domain, the cancelled
coefficient name is equivalent to the original numerator divided by this
same coordinate name, prepared for division using its generated lower bound.
No second root is selected and no caller supplies either identity.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.NamedTransport

open Purelib.Algebra
open Purelib.Algebra.Quadratic
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- The original coherent Gaussian approximation name carrier. -/
abbrev CoherentNamed := Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- The original nonzero certificate for a retained Gaussian approximation name. -/
abbrev Apart := Approximation.Gaussian.Name.Basic.Named.Apart
/-- The original equivalence relation on retained Gaussian approximation names. -/
abbrev NamedEquivalent := Approximation.Gaussian.Equivalence.NamedEquivalent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)

section
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
/-- Multiply the retained root name by the exact original square-factor value at the supplied point. -/
def coordinateName {polynomial : GaussianPolynomial} (reduction : Reduction polynomial)
    (point : Gaussian) (root : CoherentNamed) :
      CoherentNamed :=
  CoherentNamed.mul (exact (reduction.squareFactor.eval point)) root

/-- The transported coordinate name squares to the exact original polynomial value.

The retained root-square equivalence and original square-factor identity are composed without replacing either named
owner. -/
def coordinate_square {polynomial : GaussianPolynomial} (reduction : Reduction polynomial)
    (point : Gaussian) (root : CoherentNamed)
    (square : NamedEquivalent (CoherentNamed.mul root
      root).name (exact (reduction.radicand.eval point)).name) :
    NamedEquivalent
      (CoherentNamed.mul (coordinateName reduction point
        root) (coordinateName reduction point root)).name
      (exact (polynomial.eval point)).name := by
  let scalar := exact (reduction.squareFactor.eval point)
  have rearrange := Equivalence.NamedEquivalent.symm
    (Arithmetic.Product.Laws.coherentMul_squares_interchange scalar root)
  have replace := Congruence.coherentMul_respects (CoherentNamed.mul
    scalar scalar)
    (exact (reduction.squareFactor.eval point * reduction.squareFactor.eval
      point))
    (CoherentNamed.mul root root) (exact (reduction.radicand.eval
      point))
    (Exact.Arithmetic.exact_mul _ _) square
  have finish := Exact.Arithmetic.exact_mul
    (reduction.squareFactor.eval point * reduction.squareFactor.eval point) (reduction.radicand.eval point)
  rw [← reduction.evalIdentity point] at finish
  exact Equivalence.NamedEquivalent.trans rearrange (Equivalence.NamedEquivalent.trans replace finish)

end

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Certify a positive lower squared norm for every possible transported-coordinate reading.

The bound multiplies the exact nonzero square-factor norm by the retained root's original lower certificate. -/
def coordinatePossibleApart {polynomial : GaussianPolynomial} (reduction : Reduction
  polynomial)
    (point : Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : CoherentNamed) (apart :
      Apart root.name) :
    Process.Apart.Possible.PossibleApart (coordinateName reduction
      point root).name.process where
  lowerSq := Norm.Basic.normSq (reduction.squareFactor.eval point) * apart.certificate.lowerSq
  positive := Fraction.Order.Arithmetic.mul_pos_direct (Norm.Basic.normSq_pos squareNonzero) apart.certificate.positive
  lower := by
    intro state value possible
    rcases possible with ⟨scalar, candidate, scalarPossible, rootPossible, rfl⟩
    change scalar = reduction.squareFactor.eval point at scalarPossible
    rw [scalarPossible, Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (apart.certificate.lower state.2 (root.name.process.possible_inside rootPossible)) (Norm.Basic.normSq_nonneg _)

section
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
/-- Prepare the exact transported coordinate for division while retaining its name-equivalence certificate. -/
def preparedCoordinate {polynomial : GaussianPolynomial} (reduction : Reduction polynomial)
    (point : Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : CoherentNamed) (apart :
      Apart root.name) :
    Division.Prepared (coordinateName reduction
        point
      root) :=
  let lower := coordinatePossibleApart reduction point squareNonzero
    root apart
  { denominator := CoherentNamed.apartify
      (coordinateName reduction point root) lower
    apart := ⟨Process.Apart.Preparation.apartifyApart lower⟩
    equivalent := CoherentNamed.apartifyEquivalent
      (coordinateName reduction point root) lower }

/-- Divide the exact reduced weight value by the retained original root name and its nonzero certificate. -/
def reducedName {polynomial : GaussianPolynomial} {reduction : Reduction polynomial} {request
  : Request}
    (weight : Weight reduction request) (point : Gaussian) (root :
      CoherentNamed) (apart :
      Apart root.name) :
    CoherentNamed := CoherentNamed.div (exact (weight.expression
      point)) root apart

/-- Cache the exact reduced coefficient at the same original division-ready square root.

The root's retained square equation derives the radicand guard. The original
cancelled denominator guard remains an explicit input from path preparation. -/
def interpretation {polynomial : GaussianPolynomial} {reduction : Reduction polynomial}
    {request : Request} (weight : Weight reduction request) (point : Gaussian)
    (root : CoherentNamed) (apart : Apart root.name)
    (identity : PowerIdentity root 2 (reduction.radicand.eval point))
    (denominatorNonzero : weight.denominator.eval point ≠ 0) : Expression.Denotation weight.algebraic point root :=
  Expression.retain weight.algebraic point root
    (weight.algebraic_defined point denominatorNonzero (identity.square_coefficient_nonzero apart)) identity

/-- The interpreted exact coefficient times its original generator realizes the cancelled rational weight. -/
def interpreted_root_product {polynomial : GaussianPolynomial}
    {reduction : Reduction polynomial}
    {request : Request} (weight : Weight reduction request) (point : Gaussian)
    (root : CoherentNamed) (apart : Apart root.name)
    (retained : Expression.Denotation weight.algebraic point root)
    (denominatorNonzero : weight.denominator.eval point ≠ 0) :
    NamedEquivalent (CoherentNamed.mul retained.channel root).name
      (exact (weight.expression point)).name := by
  let generator : Pair Gaussian (-reduction.radicand.eval point) :=
    Pair.generator
  have normalized : PowerIdentity root 2 (-(-reduction.radicand.eval point)) := by
    rewrite [neg_neg]
    exact retained.identity
  have product := Pair.Gaussian.denote_mul id (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) root normalized retained.value generator
  have pairProduct : retained.value * generator =
      Pair.scalar (weight.expression point) := by
    rewrite [retained.value_eq, weight.algebraic_evaluate]
    apply Pair.ext
    · change 0 * 0 - (-reduction.radicand.eval point) *
        (weight.numerator.eval point / (weight.denominator.eval point * reduction.radicand.eval point)) * 1 =
      weight.numerator.eval point / weight.denominator.eval point
      apply Field.ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
      calc
        _ = (weight.numerator.eval point / (weight.denominator.eval point * reduction.radicand.eval point)) *
            (weight.denominator.eval point * reduction.radicand.eval point) := by
          rewrite [Basic.zero_mul, Basic.mul_one, zero_sub]
          rewrite [Ring.Multiplication.neg_mul (reduction.radicand.eval point)
            (weight.numerator.eval point / (weight.denominator.eval point * reduction.radicand.eval point)), neg_neg]
          rewrite [Basic.mul_comm (reduction.radicand.eval point)
            (weight.numerator.eval point / (weight.denominator.eval point * reduction.radicand.eval point)),
            Basic.mul_assoc,
            Basic.mul_comm (reduction.radicand.eval point) (weight.denominator.eval point)]
          rfl
        _ = weight.numerator.eval point := Field.ExplicitField.div_mul_cancel _
          (Field.ExplicitField.mul_ne_zero denominatorNonzero
            (retained.identity.square_coefficient_nonzero apart))
        _ = _ := (Field.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
    · change 0 * 1 + _ * 0 = 0
      rewrite [Basic.zero_mul, Basic.mul_zero, Basic.zero_add]
      rfl
  rewrite [pairProduct] at product
  have replace := Congruence.coherentMul_respects
    retained.channel (Pair.Gaussian.denote id root retained.value)
    root (Pair.Gaussian.denote id root generator)
    (by rewrite [retained.channel_eq]; exact Equivalence.NamedEquivalent.refl _)
    (Pair.Gaussian.denote_generator
      (parameter := -reduction.radicand.eval point) id rfl rfl root).symm
  exact replace.trans (product.trans (Pair.Gaussian.denote_scalar
    (parameter := -reduction.radicand.eval point) id rfl root
    (weight.expression point)))

/-- The original quotient program agrees with its cached exact quadratic coefficient at the same selected root. -/
def reduced_equivalent {polynomial : GaussianPolynomial} {reduction : Reduction polynomial}
    {request : Request} (weight : Weight reduction request) (point : Gaussian)
    (root : CoherentNamed) (apart : Apart root.name)
    (retained : Expression.Denotation weight.algebraic point root)
    (denominatorNonzero : weight.denominator.eval point ≠ 0) :
    NamedEquivalent (reducedName weight point root apart).name
      retained.channel.name := by
  have leftProduct := (Arithmetic.Product.Laws.coherentMul_comm root
    (reducedName weight point root apart)).trans
    (Division.Cancellation.coherentDiv_mul_cancel (exact
      (weight.expression point)) root apart)
  have rightProduct := (Arithmetic.Product.Laws.coherentMul_comm root retained.channel).trans
    (interpreted_root_product weight point root apart retained denominatorNonzero)
  exact Division.Cancellation.coherentMul_cancel_left root _ retained.channel apart
    (leftProduct.trans rightProduct.symm)

/-- Divide the exact original numerator by the prepared transported coordinate at the same original point. -/
def originalName {polynomial : GaussianPolynomial} (reduction : Reduction polynomial) (request
  : Request)
    (point : Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : CoherentNamed) (apart :
      Apart root.name) : CoherentNamed :=
  (preparedCoordinate reduction point squareNonzero root
    apart).quotient
    (exact (request.originalNumerator reduction point))

end

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
/-- The reduced weight times the nonzero original square factor equals the original numerator. -/
public theorem weight_times_square {polynomial : GaussianPolynomial} {reduction : Reduction
  polynomial}
    {request : Request} (weight : Weight reduction request) (point : Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) :
    weight.expression point * reduction.squareFactor.eval point = request.originalNumerator reduction point := by
  have identity := weight.coefficient_cleared point 1 squareNonzero one_ne_zero
  have divideOne : weight.expression point / (1 : Gaussian) = weight.expression point := by
    simpa only [Basic.mul_one] using Field.ExplicitField.div_mul_cancel (weight.expression point) one_ne_zero
  simpa only [Weight.coefficient, SquareFactor.coordinate, divideOne, Basic.mul_one] using identity

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
/-- Multiplying the reduced coefficient name by the retained transported coordinate gives the exact original numerator
name. -/
def coefficient_cleared {polynomial : GaussianPolynomial} {reduction : Reduction polynomial}
  {request : Request}
    (weight : Weight reduction request) (point : Gaussian) (squareNonzero :
      reduction.squareFactor.eval point ≠ 0)
    (root : CoherentNamed) (apart :
      Apart root.name)
    (identity : PowerIdentity root 2 (reduction.radicand.eval point))
    (denominatorNonzero : weight.denominator.eval point ≠ 0) :
    NamedEquivalent (CoherentNamed.mul
      (reducedName weight point root apart)
      (coordinateName reduction point root)).name
      (exact (request.originalNumerator reduction point)).name := by
  let scalar := exact (reduction.squareFactor.eval point)
  let coefficient := reducedName weight point root apart
  let retained := interpretation weight point root apart identity denominatorNonzero
  have coefficientRoot := (Congruence.coherentMul_respects coefficient
    retained.channel root root (reduced_equivalent weight point root apart retained denominatorNonzero)
    (Equivalence.NamedEquivalent.refl _)).trans
    (interpreted_root_product weight point root apart retained denominatorNonzero)
  have reorder := Congruence.coherentMul_respects coefficient coefficient
    (CoherentNamed.mul scalar root) (CoherentNamed.mul root scalar)
    (Equivalence.NamedEquivalent.refl _) (Arithmetic.Product.Laws.coherentMul_comm scalar root)
  have associate := Equivalence.NamedEquivalent.symm (Arithmetic.Product.Laws.coherentMul_assoc
    coefficient root scalar)
  have cancel := Congruence.coherentMul_respects (CoherentNamed.mul
    coefficient root) (exact (weight.expression point)) scalar scalar
    coefficientRoot (Equivalence.NamedEquivalent.refl _)
  have finish := Exact.Arithmetic.exact_mul (weight.expression point) (reduction.squareFactor.eval point)
  rw [weight_times_square weight point squareNonzero] at finish
  exact Equivalence.NamedEquivalent.trans reorder (Equivalence.NamedEquivalent.trans associate
    (Equivalence.NamedEquivalent.trans cancel finish))

/-- The reduced and original coefficient names are equivalent on the original nonzero square-factor domain.

Both constructions retain the same root name and point; cancellation uses the exact prepared coordinate's nonzero
certificate. -/
def coefficient_transport {polynomial : GaussianPolynomial} {reduction : Reduction polynomial}
  {request : Request}
    (weight : Weight reduction request) (point : Gaussian) (squareNonzero :
      reduction.squareFactor.eval point ≠ 0)
    (root : CoherentNamed) (apart :
      Apart root.name)
    (identity : PowerIdentity root 2 (reduction.radicand.eval point))
    (denominatorNonzero : weight.denominator.eval point ≠ 0) :
    NamedEquivalent
      (reducedName weight point root apart).name
      (originalName reduction request point squareNonzero root
        apart).name := by
  let prepared := preparedCoordinate reduction point squareNonzero
    root apart
  let coefficient := reducedName weight point root apart
  let original := originalName reduction request point squareNonzero
    root apart
  have leftCleared := Equivalence.NamedEquivalent.trans (Arithmetic.Product.Laws.coherentMul_comm
    prepared.denominator coefficient)
    (Equivalence.NamedEquivalent.trans (Congruence.coherentMul_respects coefficient
      coefficient prepared.denominator (coordinateName reduction point
      root)
      (Equivalence.NamedEquivalent.refl _) (Equivalence.NamedEquivalent.symm prepared.equivalent))
        (coefficient_cleared weight point squareNonzero root apart
          identity denominatorNonzero))
  have rightCleared := Equivalence.NamedEquivalent.trans (Arithmetic.Product.Laws.coherentMul_comm
    prepared.denominator original)
    (Division.Cancellation.coherentDiv_mul_cancel (exact
      (request.originalNumerator reduction point)) prepared.denominator prepared.apart)
  exact Division.Cancellation.coherentMul_cancel_left prepared.denominator coefficient original prepared.apart
    (Equivalence.NamedEquivalent.trans leftCleared (Equivalence.NamedEquivalent.symm rightCleared))

end Purelib.Integration.Algebraic.SquareFactor.NamedTransport
