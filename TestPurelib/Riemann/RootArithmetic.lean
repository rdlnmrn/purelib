module

import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic.Localization
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Polynomial.Approximation.Gaussian.Arithmetic

/-!
# Original arithmetic-root channel equations and independent requests

Arbitrary-degree original root certificates supply all scalar construction
data and quantitative bounds. The computed polynomial equation concerns the
actual coherent sum/product and supports unrelated original request starts.
-/

namespace TestPurelib.Riemann.RootArithmetic

open Purelib
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Rat.Fraction (Rational)

variable {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
variable {firstAmbient secondAmbient : CoherentRoot.Box}
variable {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}

example (operation : Operation) (first : CoherentRoot.CertifiedName firstTrack)
    (second : CoherentRoot.CertifiedName secondTrack) :
    Equivalence.NamedEquivalent
      (Horner.polynomialEval (CoherentRoot.Arithmetic.ofRoots operation first second).polynomial
        (PolynomialArithmetic.channel operation first.value second.value)).name (Coherence.exact 0).name :=
  (CoherentRoot.Arithmetic.ofRoots operation first second).equation

example (operation : Operation) (first : CoherentRoot.CertifiedName firstTrack)
    (second : CoherentRoot.CertifiedName secondTrack) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      ((CoherentRoot.Arithmetic.ofRoots operation first second).polynomial.eval
        ((CoherentRoot.Arithmetic.ofRoots operation first second).result.sample index)) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius
        (CoherentRoot.Arithmetic.ofRoots operation first second).residualScale index :=
  (CoherentRoot.Arithmetic.ofRoots operation first second).sample_residual index

example (operation : Operation) (first : CoherentRoot.CertifiedName firstTrack)
    (second : CoherentRoot.CertifiedName secondTrack) (firstStart zeroStart : Nat)
    (target : Rational) (positive : 0 < target) :
    Equivalence.Comparison
      (Name.Sampling.approximation
        (Horner.polynomialEval (CoherentRoot.Arithmetic.ofRoots operation first second).polynomial
          (PolynomialArithmetic.channel operation first.value second.value)).name)
      (Name.Sampling.approximation (Coherence.exact 0).name) firstStart zeroStart target :=
  (CoherentRoot.Arithmetic.ofRoots operation first second).equation.compare firstStart zeroStart target positive

/-- Original sum/product residual data computes bounded localization without a supplied successful search. -/
example (operation : Operation) (first : CoherentRoot.CertifiedName firstTrack)
    (second : CoherentRoot.CertifiedName secondTrack) (arithmetic : CoherentRoot.Arithmetic operation first second)
    (current : Nat)
    {epsilon : Purelib.Data.Rat.Fraction.Rational} (positive : 0 < epsilon) :
    current ≤ (arithmetic.prepareLocalization.observe current positive).index :=
  (arithmetic.prepareLocalization.observe current positive).index_ge

end TestPurelib.Riemann.RootArithmetic
