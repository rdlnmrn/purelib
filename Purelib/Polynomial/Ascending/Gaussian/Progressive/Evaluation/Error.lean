module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.Reading
public import Purelib.Polynomial.Ascending.Gaussian.Error
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite error transport for progressive Taylor tables

The progressive higher-jet layer emits every displayed coefficient.  This
module transports those finitely many coefficient allowances through Horner
evaluation and through an explicit finite truncation.  The bounds are coarse
recursive rational expressions; no omitted infinite tail or formal power
series is introduced.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Evaluation.Error

/-- Paper-facing transport theorem for every finite progressive coefficient
table, including tables produced by arithmetic or finite composition. -/
theorem progressive_eval_error_le (channels :
  List Name.Coherent.CoherentNamed)
    (readings : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical) (target : Fraction.Rational)
    (positive : 0 < target)
    (possible : Table.Reading.SharedReadingsPossible channels channels readings target
      positive) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList readings input -
        Ascending.Gaussian.Evaluation.evalList (Table.Reading.sharedCenters channels channels target positive) input) ≤
      Ascending.Gaussian.Error.evaluationErrorBudget readings.length target (Data.Gaussian.Norm.Basic.normSq input)
        :=
  Ascending.Gaussian.Error.eval_error_le readings (Table.Reading.sharedCenters channels channels target positive)
    input target (Table.Reading.sharedReadings_close channels channels readings target
      positive possible)

/-! ## Direct wrappers for the progressive higher-jet constructors -/

/-- Bound the Horner error of permitted readings from the product jet's shared coefficient request.

The squared discrepancy from its shared centers is bounded by the finite error budget for the retained reading length,
target allowance and input quadrance. -/
theorem TaylorJet.mul_evaluation_error
    (left right : Ascending.Gaussian.Progressive.Basic.TaylorJet)
    (readings : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical) (target : Fraction.Rational)
    (positive : 0 < target)
    (possible : Table.Reading.SharedReadingsPossible
      (left.mul right).coefficients (left.mul right).coefficients readings
      target positive) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList readings input -
        Ascending.Gaussian.Evaluation.evalList (Table.Reading.sharedCenters (left.mul right).coefficients
          (left.mul right).coefficients target positive) input) ≤
      Ascending.Gaussian.Error.evaluationErrorBudget readings.length target (Data.Gaussian.Norm.Basic.normSq input)
        :=
  progressive_eval_error_le (left.mul right).coefficients readings input
    target
    positive possible

/-- Bound the Horner error of permitted readings from the composed jet's shared coefficient request.

The bound uses that exact composition table's shared centers and the finite evaluation budget at the supplied positive
allowance. -/
theorem TaylorJet.compose_evaluation_error
    (outer inner : Ascending.Gaussian.Progressive.Basic.TaylorJet)
    (readings : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical) (target : Fraction.Rational)
    (positive : 0 < target)
    (possible : Table.Reading.SharedReadingsPossible
      (outer.compose inner).coefficients (outer.compose inner).coefficients
      readings target positive) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Gaussian.Evaluation.evalList readings input -
        Ascending.Gaussian.Evaluation.evalList (Table.Reading.sharedCenters (outer.compose inner).coefficients
          (outer.compose inner).coefficients target positive) input) ≤
      Ascending.Gaussian.Error.evaluationErrorBudget readings.length target (Data.Gaussian.Norm.Basic.normSq input)
        :=
  progressive_eval_error_le (outer.compose inner).coefficients readings
    input
    target positive possible
end Purelib.Polynomial.Ascending.Gaussian.Progressive.Evaluation.Error

end
