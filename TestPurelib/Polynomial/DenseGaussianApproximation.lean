module

import Purelib.Polynomial.Dense.Gaussian.Approximation
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent

/-!
# Original-index polynomial evaluation and root residual comparisons

The closed example evaluates a degree-seventeen polynomial while retaining
the original constant-input refinement. Quantified comparisons keep distinct
starting indices and the actual source cache of arbitrary root certificates.
-/

namespace TestPurelib.Polynomial.DenseGaussianApproximation

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Sequence.Constant (constantApproximation)
open Purelib.Approximation.Gaussian.Equivalence (Comparison Equivalent)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Fraction (Rational)

/-- A degree-seventeen input with a lower-degree cancellation at the retained sample one. -/
private def polynomial : CoefficientPolynomial :=
  ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 3]⟩

/-- The original finite box used for the coefficient-computed bounds. -/
private def ambient : Box := ⟨-2, 2, -2, 2, by decide, by decide⟩

/-- Every sample of the original exact-one approximation lies in the retained box. -/
private theorem inside (index : Nat) : ambient.Contains ((constantApproximation 1).sample index) := by
  change ambient.Contains 1
  decide +kernel

/-- Polynomial evaluation retains the original exact-one sample program. -/
private def evaluated : ApproximationData :=
  Approximation.evaluate polynomial ambient (constantApproximation 1) inside

example (index : Nat) : evaluated.sample index = 3 :=
  (Approximation.evaluate_sample polynomial ambient (constantApproximation 1) inside index).trans
    (by change polynomial.eval 1 = 3; decide +kernel)

example (current : Nat) (target : Rational) (positive : 0 < target) :
    evaluated.refineIndex current target positive = current := rfl

example (polynomial : CoefficientPolynomial) (ambient : Box)
    (first second : ApproximationData)
    (firstInside : ∀ index, ambient.Contains (first.sample index))
    (secondInside : ∀ index, ambient.Contains (second.sample index))
    (equivalent : Equivalent first second) (firstStart secondStart : Nat)
    (target : Rational) (positive : 0 < target) :
    Comparison (Approximation.evaluate polynomial ambient first firstInside)
      (Approximation.evaluate polynomial ambient second secondInside) firstStart secondStart target :=
  (Approximation.respects polynomial ambient firstInside secondInside equivalent).compare
    firstStart secondStart target positive

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) (index : Nat) :
    certificate.evaluation.sample index = polynomial.eval (certificate.approximation.sample index) := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) (firstStart secondStart : Nat)
    (target : Rational) (positive : 0 < target) :
    Comparison (Purelib.Approximation.Gaussian.Name.Sampling.approximation certificate.evaluation.toNamed)
      (Purelib.Approximation.Gaussian.Name.Sampling.approximation
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0).name)
      firstStart secondStart target :=
  certificate.evaluation_zero.compare firstStart secondStart target positive

end TestPurelib.Polynomial.DenseGaussianApproximation
