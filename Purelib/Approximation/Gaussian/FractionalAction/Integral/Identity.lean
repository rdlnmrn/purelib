module
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.LinearAlgebra.Matrix
open Purelib.Riemann.Integration

public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

/-! ## Identity and certified inverse laws -/

/-- Any matrix proved exactly equal to the identity has productive fractional action operationally equal to `tau`, while
retaining preparation at the caller's original matrix-indexed denominator. -/
@[expose] def fractionalLinear_of_matrix_eq_identity (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator matrix tau))
    (matrixEq : matrix = Multiplication.identity) :
    Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalLinear matrix tau preparation).name tau.name := by
  let one := Coherence.exact 1
  let output := LegendreModularMonodromy.fractionalLinear matrix tau preparation
  have denominatorOne := Action.matrixAction_identity (LegendreModularMonodromy.fractionalVector tau) 0
  rw [← matrixEq] at denominatorOne
  change Gaussian.Equivalence.NamedEquivalent
    (LegendreModularMonodromy.fractionalDenominator matrix tau).name
    one.name at denominatorOne
  have numeratorTau := Action.matrixAction_identity (LegendreModularMonodromy.fractionalVector tau) 1
  rw [← matrixEq] at numeratorTau
  change Gaussian.Equivalence.NamedEquivalent
    (LegendreModularMonodromy.fractionalNumerator matrix tau).name
    tau.name at numeratorTau
  have onePrepared : Gaussian.Equivalence.NamedEquivalent one.name preparation.prepared.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm denominatorOne)
      preparation.equivalent
  have scaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul one output).name tau.name :=
    NamedEquivalent.trans
      (Congruence.coherentMul_respects
        one preparation.prepared output output onePrepared
        (NamedEquivalent.refl output.name))
      (NamedEquivalent.trans
        (by
            simpa only [output, CoherentNamed.mul]
              using (LegendreModularMonodromy.prepared_denominator_mul_fractionalLinear matrix tau preparation))
        numeratorTau)
  change Gaussian.Equivalence.NamedEquivalent output.name tau.name
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      (Mul.coherentMul_one_left output)) scaled

/-- A prepared identity-matrix fractional output is operationally `tau`. -/
@[expose] def fractionalLinear_identity (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator Multiplication.identity tau)) :
    Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalLinear Multiplication.identity tau
        preparation).name tau.name :=
  Approximation.Gaussian.FractionalAction.Integral.Identity.fractionalLinear_of_matrix_eq_identity
    Multiplication.identity tau preparation rfl

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity
