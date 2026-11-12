module

public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # The original value-zero coefficient and the same apart root reciprocal

Only the displayed unit numerator and first reciprocal power are removed.
The original denotation, root process, square identity and apartness remain
indices of the comparison; no observation state is replaced or cast.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Specification

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The first value coefficient uses the same original apart root reciprocal without an extra unit multiplication. -/
def valueZero_reciprocal (parameter point : Canonical) (root : CoherentNamed) (apart : Named.Apart root.name) :
    NamedEquivalent ((valueSpecification parameter 0).value point root apart).name
      (CoherentNamed.div (Coherence.exact 1) root apart).name := by
  let reciprocal := CoherentNamed.div (Coherence.exact 1) root apart
  have unit : (valueSpecification parameter 0).scale *
      (valueSpecification parameter 0).numerator.eval point = 1 := by
    change 1 * (Polynomial.Dense.Basic.DensePolynomial.constant 1).eval point = (1 : Canonical)
    rewrite [Polynomial.Dense.Basic.DensePolynomial.eval_constant]
    ring1
  have exponent : (valueSpecification parameter 0).denominatorExponent = 1 := rfl
  change NamedEquivalent
    (CoherentNamed.mul
      (Coherence.exact ((valueSpecification parameter 0).scale *
        (valueSpecification parameter 0).numerator.eval point))
      (Power.namedPower reciprocal (valueSpecification parameter 0).denominatorExponent)).name reciprocal.name
  rewrite [unit, exponent]
  exact (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    (Coherence.exact 1) (Coherence.exact 1) (Power.namedPower reciprocal 1) reciprocal
    (NamedEquivalent.refl _) (Power.namedPower_one reciprocal)).trans
      (Approximation.Gaussian.Arithmetic.Mul.coherentMul_one_left reciprocal)

/-- An actual cached value-zero denotation compares to its same original root reciprocal.

The exact channel readback identifies the supplied cache with the original
coefficient interpretation. Its state and selected reading are not moved
to the reciprocal process; consumers compare both original states instead.
-/
def valueZero_denotation_reciprocal (parameter point : Canonical) (root : CoherentNamed)
    (identity : PowerIdentity root 2 ((Paths.polynomial parameter).eval point))
    (apart : Named.Apart root.name)
    (retained : Expression.Denotation (valueSpecification parameter 0).coefficient point root) :
    NamedEquivalent retained.channel.name (CoherentNamed.div (Coherence.exact 1) root apart).name := by
  let differential := valueSpecification parameter 0
  have normalized := differential.reciprocal_power_equivalent point root identity apart
  have same : (differential.interpret point root identity apart).channel = retained.channel :=
    (differential.interpret point root identity apart).channel_readback.trans retained.channel_readback.symm
  have actual : NamedEquivalent (differential.value point root apart).name retained.channel.name := by
    change NamedEquivalent
      (CoherentNamed.mul (Coherence.exact (differential.scale * differential.numerator.eval point))
        (Power.namedPower (CoherentNamed.div (Coherence.exact 1) root apart) differential.denominatorExponent)).name _
    rewrite [same] at normalized
    exact normalized
  exact actual.symm.trans (valueZero_reciprocal parameter point root apart)

end Purelib.Curves.Legendre.Periods.Jets.Specification

end
