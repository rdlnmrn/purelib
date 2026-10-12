module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Value
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Perturbation
open Purelib.Data.Gaussian

/-- The coefficientwise bound made uniform over one rational box. -/
theorem normSq_evalCoeffs_sub_le_onBox
    (left right : List Gaussian.Basic.Canonical) (coefficientBound : Fraction.Rational)
    (coefficientNonnegative : 0 ≤ coefficientBound) (box : Geometry.Rational.Box)
    {input : Gaussian.Basic.Canonical} (inside : box.Contains input)
    (close : Gaussian.List.Proximity.CoefficientsClose left right coefficientBound) :
    Data.Gaussian.Norm.Basic.normSq
        (Dense.Basic.DensePolynomial.evalCoeffs input left -
          Dense.Basic.DensePolynomial.evalCoeffs input right) ≤
      Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget left.length coefficientBound
        (Geometry.Rational.Box.normSqBound box) :=
  (Dense.Gaussian.Bounds.Perturbation.Value.normSq_evalCoeffs_sub_le left right input coefficientBound close).trans
    (Dense.Gaussian.Bounds.Perturbation.Value.hornerPerturbationBudget_mono_input left.length coefficientNonnegative
      (Gaussian.Norm.Basic.normSq_nonneg input) (box.normSq_le_normSqBound inside))

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Perturbation

end
