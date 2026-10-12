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

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Data.Gaussian.Basic.Canonical

/-- The original coherent Gaussian approximation name carrier. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- The original nonzero certificate for a retained Gaussian approximation name. -/
abbrev Apart := Purelib.Approximation.Gaussian.Name.Basic.Named.Apart
/-- The original equivalence relation on retained Gaussian approximation names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)

section
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
/-- Multiply the retained root name by the exact original square-factor value at the supplied point. -/
def coordinateName {polynomial : SquareFactor.GaussianPolynomial} (reduction : SquareFactor.Reduction polynomial)
    (point : SquareFactor.Gaussian) (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) :
      CoherentNamed :=
  Name.Coherent.CoherentNamed.mul (Name.Coherent.CoherentNamed.Coherence.exact (reduction.squareFactor.eval point)) root

/-- The transported coordinate name squares to the exact original polynomial value.

The retained root-square equivalence and original square-factor identity are composed without replacing either named
owner. -/
def coordinate_square {polynomial : SquareFactor.GaussianPolynomial} (reduction : SquareFactor.Reduction polynomial)
    (point : SquareFactor.Gaussian) (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed)
    (square : Integration.Algebraic.SquareFactor.NamedTransport.NamedEquivalent (Name.Coherent.CoherentNamed.mul root
      root).name (Name.Coherent.CoherentNamed.Coherence.exact (reduction.radicand.eval point)).name) :
    Integration.Algebraic.SquareFactor.NamedTransport.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point
        root) (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point root)).name
      (Name.Coherent.CoherentNamed.Coherence.exact (polynomial.eval point)).name := by
  let scalar := Name.Coherent.CoherentNamed.Coherence.exact (reduction.squareFactor.eval point)
  have rearrange := Equivalence.NamedEquivalent.symm
    (Name.Coherent.Arithmetic.Product.Laws.coherentMul_squares_interchange scalar root)
  have replace := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects (Name.Coherent.CoherentNamed.mul
    scalar scalar)
    (Name.Coherent.CoherentNamed.Coherence.exact (reduction.squareFactor.eval point * reduction.squareFactor.eval
      point))
    (Name.Coherent.CoherentNamed.mul root root) (Name.Coherent.CoherentNamed.Coherence.exact (reduction.radicand.eval
      point))
    (Name.Coherent.Exact.Arithmetic.exact_mul _ _) square
  have finish := Name.Coherent.Exact.Arithmetic.exact_mul
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
def coordinatePossibleApart {polynomial : SquareFactor.GaussianPolynomial} (reduction : SquareFactor.Reduction
  polynomial)
    (point : SquareFactor.Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) :
    Process.Apart.Possible.PossibleApart (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction
      point root).name.process where
  lowerSq := Data.Gaussian.Norm.Basic.normSq (reduction.squareFactor.eval point) * apart.certificate.lowerSq
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
def preparedCoordinate {polynomial : SquareFactor.GaussianPolynomial} (reduction : SquareFactor.Reduction polynomial)
    (point : SquareFactor.Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) :
    Approximation.Gaussian.Division.Prepared (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction
        point
      root) :=
  let lower := Integration.Algebraic.SquareFactor.NamedTransport.coordinatePossibleApart reduction point squareNonzero
    root apart
  { denominator := Name.Coherent.CoherentNamed.apartify
      (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point root) lower
    apart := ⟨Process.Apart.Preparation.apartifyApart lower⟩
    equivalent := Name.Coherent.CoherentNamed.apartifyEquivalent
      (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point root) lower }

/-- Divide the exact reduced weight value by the retained original root name and its nonzero certificate. -/
def reducedName {polynomial : SquareFactor.GaussianPolynomial} {reduction : SquareFactor.Reduction polynomial} {request
  : SquareFactor.Request}
    (weight : SquareFactor.Weight reduction request) (point : SquareFactor.Gaussian) (root :
      Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) :
    CoherentNamed := Name.Coherent.CoherentNamed.div (Name.Coherent.CoherentNamed.Coherence.exact (weight.expression
      point)) root apart

/-- Divide the exact original numerator by the prepared transported coordinate at the same original point. -/
def originalName {polynomial : SquareFactor.GaussianPolynomial} (reduction : SquareFactor.Reduction polynomial) (request
  : SquareFactor.Request)
    (point : SquareFactor.Gaussian) (squareNonzero : reduction.squareFactor.eval point ≠ 0)
    (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) : CoherentNamed :=
  (Integration.Algebraic.SquareFactor.NamedTransport.preparedCoordinate reduction point squareNonzero root
    apart).quotient
    (Name.Coherent.CoherentNamed.Coherence.exact (request.originalNumerator reduction point))

end

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
/-- The reduced weight times the nonzero original square factor equals the original numerator. -/
public theorem weight_times_square {polynomial : SquareFactor.GaussianPolynomial} {reduction : SquareFactor.Reduction
  polynomial}
    {request : SquareFactor.Request} (weight : SquareFactor.Weight reduction request) (point : SquareFactor.Gaussian)
    (squareNonzero : reduction.squareFactor.eval point ≠ 0) :
    weight.expression point * reduction.squareFactor.eval point = request.originalNumerator reduction point := by
  have identity := weight.coefficient_cleared point 1 squareNonzero one_ne_zero
  have divideOne : weight.expression point / (1 : SquareFactor.Gaussian) = weight.expression point := by
    simpa only [Basic.mul_one] using Field.ExplicitField.div_mul_cancel (weight.expression point) one_ne_zero
  simpa only [SquareFactor.Weight.coefficient, SquareFactor.coordinate, divideOne, Basic.mul_one] using identity

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
/-- Multiplying the reduced coefficient name by the retained transported coordinate gives the exact original numerator
name. -/
def coefficient_cleared {polynomial : SquareFactor.GaussianPolynomial} {reduction : SquareFactor.Reduction polynomial}
  {request : SquareFactor.Request}
    (weight : SquareFactor.Weight reduction request) (point : SquareFactor.Gaussian) (squareNonzero :
      reduction.squareFactor.eval point ≠ 0)
    (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) :
    Integration.Algebraic.SquareFactor.NamedTransport.NamedEquivalent (Name.Coherent.CoherentNamed.mul
      (Integration.Algebraic.SquareFactor.NamedTransport.reducedName weight point root apart)
      (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point root)).name
      (Name.Coherent.CoherentNamed.Coherence.exact (request.originalNumerator reduction point)).name := by
  let scalar := Name.Coherent.CoherentNamed.Coherence.exact (reduction.squareFactor.eval point)
  let coefficient := Integration.Algebraic.SquareFactor.NamedTransport.reducedName weight point root apart
  have reorder := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects coefficient coefficient
    (Name.Coherent.CoherentNamed.mul scalar root) (Name.Coherent.CoherentNamed.mul root scalar)
    (Equivalence.NamedEquivalent.refl _) (Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm scalar root)
  have associate := Equivalence.NamedEquivalent.symm (Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc
    coefficient root scalar)
  have cancel := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects (Name.Coherent.CoherentNamed.mul
    coefficient root) (Name.Coherent.CoherentNamed.Coherence.exact (weight.expression point)) scalar scalar
    (Division.Cancellation.coherentDiv_mul_cancel (Name.Coherent.CoherentNamed.Coherence.exact (weight.expression
      point)) root apart) (Equivalence.NamedEquivalent.refl _)
  have finish := Name.Coherent.Exact.Arithmetic.exact_mul (weight.expression point) (reduction.squareFactor.eval point)
  rw [Integration.Algebraic.SquareFactor.NamedTransport.weight_times_square weight point squareNonzero] at finish
  exact Equivalence.NamedEquivalent.trans reorder (Equivalence.NamedEquivalent.trans associate
    (Equivalence.NamedEquivalent.trans cancel finish))

/-- The reduced and original coefficient names are equivalent on the original nonzero square-factor domain.

Both constructions retain the same root name and point; cancellation uses the exact prepared coordinate's nonzero
certificate. -/
def coefficient_transport {polynomial : SquareFactor.GaussianPolynomial} {reduction : SquareFactor.Reduction polynomial}
  {request : SquareFactor.Request}
    (weight : SquareFactor.Weight reduction request) (point : SquareFactor.Gaussian) (squareNonzero :
      reduction.squareFactor.eval point ≠ 0)
    (root : Integration.Algebraic.SquareFactor.NamedTransport.CoherentNamed) (apart :
      Integration.Algebraic.SquareFactor.NamedTransport.Apart root.name) :
    Integration.Algebraic.SquareFactor.NamedTransport.NamedEquivalent
      (Integration.Algebraic.SquareFactor.NamedTransport.reducedName weight point root apart).name
      (Integration.Algebraic.SquareFactor.NamedTransport.originalName reduction request point squareNonzero root
        apart).name := by
  let prepared := Integration.Algebraic.SquareFactor.NamedTransport.preparedCoordinate reduction point squareNonzero
    root apart
  let coefficient := Integration.Algebraic.SquareFactor.NamedTransport.reducedName weight point root apart
  let original := Integration.Algebraic.SquareFactor.NamedTransport.originalName reduction request point squareNonzero
    root apart
  have leftCleared := Equivalence.NamedEquivalent.trans (Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm
    prepared.denominator coefficient)
    (Equivalence.NamedEquivalent.trans (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects coefficient
      coefficient prepared.denominator (Integration.Algebraic.SquareFactor.NamedTransport.coordinateName reduction point
      root)
      (Equivalence.NamedEquivalent.refl _) (Equivalence.NamedEquivalent.symm prepared.equivalent))
        (Integration.Algebraic.SquareFactor.NamedTransport.coefficient_cleared weight point squareNonzero root apart))
  have rightCleared := Equivalence.NamedEquivalent.trans (Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm
    prepared.denominator original)
    (Division.Cancellation.coherentDiv_mul_cancel (Name.Coherent.CoherentNamed.Coherence.exact
      (request.originalNumerator reduction point)) prepared.denominator prepared.apart)
  exact Division.Cancellation.coherentMul_cancel_left prepared.denominator coefficient original prepared.apart
    (Equivalence.NamedEquivalent.trans leftCleared (Equivalence.NamedEquivalent.symm rightCleared))

end Purelib.Integration.Algebraic.SquareFactor.NamedTransport
