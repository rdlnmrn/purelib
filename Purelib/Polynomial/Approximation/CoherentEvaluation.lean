module
public import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
public import Purelib.Polynomial.Approximation.Evaluation
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite polynomial evaluation at one retained sample index

Horner arithmetic supplies geometric bounds and an operational certificate.
The executable sample reads its input once and evaluates the cached dense
polynomial directly, with a proof tying it to those same Horner bounds.
-/

namespace Purelib.Polynomial.Approximation.CoherentEvaluation

open _root_.Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open _root_.Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)

/-- The geometric approximation obtained from a coherent name retains an equivalent named process. -/
def named_agrees (input : CoherentNamed) : NamedEquivalent
  input.name
    (Geometric.GeometricApproximation.ofNamed input.name).toApproximation.toNamed :=
  (Sequence.Name.Equivalence.named_toSamplingNamed input.name).trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Name.Sampling.approximation input.name) (Geometric.GeometricApproximation.ofNamed input.name).toApproximation (fun
      _ => rfl)).toNamed)

/-- The exact coherent name agrees with the constant geometric approximation. -/
def exact_agrees (value : Gaussian.Basic.Canonical) :
  NamedEquivalent (Name.Coherent.CoherentNamed.Coherence.exact value).name
    (Geometric.GeometricApproximation.exact value).toApproximation.toNamed :=
  (Sequence.Name.Exact.exact_toConstantNamed value).trans ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (Sequence.Constant.constantApproximation value) (Geometric.GeometricApproximation.exact value).toApproximation (fun
      _ => rfl)).toNamed)

/-- Multiplication preserves the supplied equivalences between coherent names and geometric approximations. -/
def mul_agrees (left right : CoherentNamed) (first second :
  Geometric.GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed) :
    NamedEquivalent (CoherentNamed.mul left right).name (first.mul second).toApproximation.toNamed :=
  (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects left (Name.Coherent.CoherentNamed.ofApproximation
    first.toApproximation) right (Name.Coherent.CoherentNamed.ofApproximation second.toApproximation) leftEq
    rightEq).trans
    (Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise first.toApproximation
      second.toApproximation (first.mul second).toApproximation (fun _ => rfl))

/-- Addition preserves the supplied equivalences between coherent names and geometric approximations. -/
public def add_agrees (left right : CoherentNamed) (first
  second : Geometric.GeometricApproximation)
    (leftEq : NamedEquivalent left.name first.toApproximation.toNamed)
    (rightEq : NamedEquivalent right.name second.toApproximation.toNamed) :
    NamedEquivalent (CoherentNamed.add left right).name (first.add second).toApproximation.toNamed :=
  (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects left (Name.Coherent.CoherentNamed.ofApproximation
    first.toApproximation) right (Name.Coherent.CoherentNamed.ofApproximation second.toApproximation) leftEq
    rightEq).trans
    (Arithmetic.Sampling.addToNamed_equivalent_pointwise first.toApproximation second.toApproximation
      (first.add second).toApproximation (fun _ => rfl))

/-- The coherent and geometric Horner loops retain equivalent names for equivalent inputs and initial accumulators. -/
public def loop_agrees (input : CoherentNamed) (source :
  Geometric.GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    (initial : CoherentNamed) → (start : Geometric.GeometricApproximation) → NamedEquivalent initial.name
      start.toApproximation.toNamed →
    (coefficients : List Gaussian.Basic.Canonical) → NamedEquivalent (Approximation.Gaussian.Evaluation.Horner.horner
      input initial coefficients).name (Approximation.Evaluation.loop source start
      coefficients).toApproximation.toNamed
  | _, _, initialEq, [] => initialEq
  | initial, start, initialEq, coefficient :: remaining =>
      loop_agrees input source sourceEq (CoherentNamed.add
        (CoherentNamed.mul initial input) (Name.Coherent.CoherentNamed.Coherence.exact coefficient))
        ((start.mul source).add (.exact coefficient))
        (add_agrees (CoherentNamed.mul initial input)
          (Name.Coherent.CoherentNamed.Coherence.exact coefficient) (start.mul source) (.exact coefficient)
          (mul_agrees initial input start source initialEq sourceEq)
            (exact_agrees coefficient)) remaining

/-- Coherent Horner evaluation and sampled geometric evaluation give equivalent names on the same retained input.

The supplied source equivalence is transported through every coefficient operation and the final exact sample readback.
-/
def evaluate_agrees (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (input : CoherentNamed) (source :
  Geometric.GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Approximation.Gaussian.Evaluation.Horner.polynomialEval polynomial input).name
      (Approximation.Evaluation.evaluate polynomial source).toApproximation.toNamed :=
  (loop_agrees input source sourceEq
    (Name.Coherent.CoherentNamed.Coherence.exact 0) (.exact 0) (exact_agrees 0)
    polynomial.coeffs).trans
    ((Sequence.Equivalence.approximationEquivalentOfSamplesEq (Approximation.Evaluation.loop source (.exact 0)
      polynomial.coeffs).toApproximation
      (Approximation.Evaluation.evaluate polynomial source).toApproximation (fun index =>
        Approximation.Evaluation.loop_sample source index _ _)).toNamed)

end Purelib.Polynomial.Approximation.CoherentEvaluation

end
