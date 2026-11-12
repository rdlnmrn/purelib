module

import TestPurelib.Curves.Legendre.PeriodVariation.Sampling
import Purelib.Curves.Legendre.Periods.Jets.Connection.Operational
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs.Operational
import Purelib.Curves.Legendre.Paths
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent

/-! # Original pointwise reductions on the retained nonsquare sheet

Both connection rows and the scalar residual reuse the original target
certificate whose radicand is three quarters. The independent primitive
derivative specifications retain their original polynomial numerators,
scales and exponents. Their materialized primitive, derivative and Leibniz
channels use the same complete prepared sheet and apartness certificate.

These pointwise comparisons do not assert a primitive edge integral or
closed-cycle cancellation.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Reduction

open Purelib.Curves.Legendre.Periods.Jets

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)

-- Keep the complete existing root and owner caches opaque during assertions.
attribute [local irreducible] Sampling.targetOwner Sampling.target

/-- The original target parameter retains the fixed source parameter and its actual increment. -/
private def parameter : Canonical := Sampling.parameter + Sampling.increment

/-- The actual target square comparison is transported by the original polynomial's exact scalar readback. -/
private def square : NamedEquivalent (Sampling.target.value.mul Sampling.target.value).name
    (Coherence.exact ((Paths.polynomial parameter).eval 2)).name := by
  have radicand : PicardFuchs.Polynomials.curveValue parameter 2 =
      (Paths.polynomial parameter).eval 2 := by
    rewrite [Paths.polynomial_eval]
    rfl
  exact NamedEquivalent.transport rfl
    (congrArg (fun value : Canonical => (Coherence.exact value).name) radicand) Sampling.target.square

/-- Each original connection primitive has its independent spatial derivative computed once. -/
private def connectionDerivative (coordinate : Fin 2) :
    OddPower.Derivative.Specification (Paths.polynomial parameter)
      (Connection.Operational.primitiveForm parameter coordinate) :=
  Connection.Operational.primitiveDerivative parameter coordinate

/-- Both connection rows materialize their complete primitive and derivative evaluators on the same target sheet. -/
private def connectionValues (coordinate : Fin 2) :
    (connectionDerivative coordinate).Values 2 Sampling.target.value Sampling.target.apart :=
  OddPower.Derivative.Specification.Values.build (connectionDerivative coordinate) 2
    Sampling.target.value Sampling.target.apart square

/-- The scalar residual primitive has its independently computed spatial derivative retained once. -/
private def residualDerivative :
    OddPower.Derivative.Specification (Paths.polynomial parameter)
      (Jets.PicardFuchs.Operational.primitiveForm parameter) :=
  Jets.PicardFuchs.Operational.primitiveDerivative parameter

/-- The scalar primitive and derivative channels retain the identical nonsquare target root and apartness cache. -/
private def residualValues : residualDerivative.Values 2 Sampling.target.value Sampling.target.apart :=
  OddPower.Derivative.Specification.Values.build residualDerivative 2
    Sampling.target.value Sampling.target.apart square

attribute [local irreducible] connectionDerivative connectionValues residualDerivative residualValues

/-- Each connection primitive cache preserves its complete original numerator, scale, exponent, point and sheet. -/
theorem connection_primitive_owner (coordinate : Fin 2) :
    (connectionValues coordinate).primitiveValue =
      (Connection.Operational.primitiveForm parameter coordinate).value
        2 Sampling.target.value Sampling.target.apart :=
  (connectionValues coordinate).primitiveValue_eq

/-- Both independently constructed connection derivative caches retain their complete original evaluators. -/
theorem connection_derivative_owner (coordinate : Fin 2) :
    (connectionValues coordinate).derivative =
      (connectionDerivative coordinate).differential.value 2 Sampling.target.value Sampling.target.apart :=
  (connectionValues coordinate).derivative_eq

/-- The original positive connection Leibniz term retains the same complete prepared root and point. -/
theorem connection_first_owner (coordinate : Fin 2) :
    (connectionValues coordinate).first =
      (connectionDerivative coordinate).first.value 2 Sampling.target.value Sampling.target.apart :=
  (connectionValues coordinate).first_eq

/-- The original negative connection Leibniz term retains its own complete evaluator on that identical sheet. -/
theorem connection_last_owner (coordinate : Fin 2) :
    (connectionValues coordinate).last =
      (connectionDerivative coordinate).last.value 2 Sampling.target.value Sampling.target.apart :=
  (connectionValues coordinate).last_eq

/-- The original signed connection difference uses both actual retained Leibniz caches. -/
theorem connection_difference_owner (coordinate : Fin 2) :
    (connectionValues coordinate).difference =
      (connectionValues coordinate).first.add
        (CoherentNamed.neg (connectionValues coordinate).last) :=
  (connectionValues coordinate).difference_eq

/-- Both connection rows construct their pointwise comparison from the original square and polynomial certificates. -/
def connection_reduced (coordinate : Fin 2) :
    NamedEquivalent
      (Connection.Operational.scaledFirstValue parameter coordinate 2
        Sampling.target.value Sampling.target.apart).name
      ((Connection.Operational.actionValue parameter coordinate 2
        Sampling.target.value Sampling.target.apart).add (connectionValues coordinate).derivative).name :=
  Connection.Operational.reduced parameter coordinate 2 Sampling.target.value Sampling.target.apart
    square (connectionDerivative coordinate) (connectionValues coordinate)

/-- The residual primitive cache preserves its original polynomial numerator over the actual sheet cube. -/
theorem residual_primitive_owner : residualValues.primitiveValue =
    (Jets.PicardFuchs.Operational.primitiveForm parameter).value 2 Sampling.target.value Sampling.target.apart :=
  residualValues.primitiveValue_eq

/-- The independent residual derivative retains its complete original evaluator on the same target sheet. -/
theorem residual_derivative_owner : residualValues.derivative =
    residualDerivative.differential.value 2 Sampling.target.value Sampling.target.apart :=
  residualValues.derivative_eq

/-- The scalar residual's positive Leibniz term retains its own complete original root evaluator. -/
theorem residual_first_owner : residualValues.first =
    residualDerivative.first.value 2 Sampling.target.value Sampling.target.apart :=
  residualValues.first_eq

/-- The scalar residual's negative Leibniz term retains its complete original root evaluator and scale. -/
theorem residual_last_owner : residualValues.last =
    residualDerivative.last.value 2 Sampling.target.value Sampling.target.apart :=
  residualValues.last_eq

/-- The scalar derivative comparison uses the signed difference of the two actual retained Leibniz caches. -/
theorem residual_difference_owner : residualValues.difference =
    residualValues.first.add (CoherentNamed.neg residualValues.last) :=
  residualValues.difference_eq

/-- The original three-term residual agrees pointwise with the independent retained primitive derivative. -/
def residual_reduced : NamedEquivalent
    (Jets.PicardFuchs.Operational.residualValue parameter 2 Sampling.target.value Sampling.target.apart).name
    residualValues.derivative.name :=
  Jets.PicardFuchs.Operational.reduced parameter 2 Sampling.target.value Sampling.target.apart
    square residualDerivative residualValues

end TestPurelib.Curves.Legendre.PeriodVariation.Reduction
