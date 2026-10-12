module
import Purelib.Data.Gaussian.Basic
public import Purelib.Examples.RationalFunctions.ArgumentPrinciple.Fixtures
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree
public import Purelib.RationalFunctions.ArgumentPrinciple.General
public import Purelib.RootIsolation.Squarefree.Observation.Certified
public import Purelib.RootIsolation.Squarefree.Observation.Separation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Executable RFAP examples

These small displayed dense polynomials exercise both public branches.  The
first quotient has two coprime squarefree numerator zeros and one coprime
squarefree denominator pole.  The second has one repeated numerator factor;
its finite rational box has ordinary winding two rather than one.
-/

namespace Purelib.Examples.RationalFunctions.ArgumentPrinciple.Squarefree.WorkedExamples

open Purelib.Examples

open Purelib.Examples.RationalFunctions.ArgumentPrinciple
open Purelib.Polynomial.Dense.Gaussian.Linear

/-- The explicit coprimality certificate `1 = Z - (Z - 1)` for the displayed numerator and denominator. -/
def squarefreeCoprime :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate Fixtures.squarefreeNumerator
      Fixtures.squarefreeDenominator := by
  apply Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity
    Fixtures.squarefreeNumerator
      Fixtures.squarefreeDenominator
    (Or.inl Fixtures.squarefreeNumerator_nonzero)
      (Dense.Basic.DensePolynomial.constant 1) (Dense.Basic.DensePolynomial.constant (-1))
  intro point
  simp only [Dense.Basic.DensePolynomial.eval_constant,
    Fixtures.squarefreeNumerator,
    Fixtures.squarefreeDenominator,
      Translated.translatedCoordinate_eval]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im,
      Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;> ring1

/-- The squarefree numerator-side input retaining its nonzero certificate and original cross-coprimality witness. -/
def squarefreeNumeratorInput :
    Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput
      Fixtures.squarefreeNumerator
        Fixtures.squarefreeDenominator where
  sourceSquarefree := Translated.Squarefree.certificate 0
  sourceNonzero := Fixtures.squarefreeNumerator_nonzero
  oppositeNonzero := Fixtures.squarefreeDenominator_nonzero
  sourceOppositeCoprime := squarefreeCoprime

/-- The squarefree denominator-side input retaining the reversed original coprimality certificate. -/
def squarefreeDenominatorInput :
    Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput
      Fixtures.squarefreeDenominator
        Fixtures.squarefreeNumerator where
  sourceSquarefree := Translated.Squarefree.certificate 1
  sourceNonzero := Fixtures.squarefreeDenominator_nonzero
  oppositeNonzero := Fixtures.squarefreeNumerator_nonzero
  sourceOppositeCoprime :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      squarefreeCoprime

/-- The certified squarefree observations of the original numerator polynomial. -/
def squarefreeNumeratorSites :=
  Squarefree.Observation.Certified.proveSquarefreeSide
    squarefreeNumeratorInput

/-- The certified squarefree observations of the original denominator polynomial. -/
def squarefreeDenominatorSites :=
  Squarefree.Observation.Certified.proveSquarefreeSide
    squarefreeDenominatorInput

/-- The joint separation certificate for the retained numerator and denominator observations.

The original cross-coprimality witness excludes coincident zero and pole sites. -/
def squarefreeJointSeparation :
    Squarefree.Observation.Separation.SquarefreeObservationsSeparated
      squarefreeNumeratorSites.observation
      squarefreeDenominatorSites.observation :=
  Squarefree.Observation.Separation.separateSquarefreeObservations
    squarefreeNumeratorSites.observation
    squarefreeDenominatorSites.observation
      squarefreeCoprime

/-- The executable signed-site argument-principle result for the same coprime squarefree quotient. -/
def squarefreeResult :=
  ArgumentPrinciple.General.prove Fixtures.squarefreeNumerator
    Fixtures.squarefreeDenominator
      Fixtures.squarefreeDenominator_nonzero
end Purelib.Examples.RationalFunctions.ArgumentPrinciple.Squarefree.WorkedExamples

end
