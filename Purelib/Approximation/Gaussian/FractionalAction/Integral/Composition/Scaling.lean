module
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Vector
open Purelib.Approximation.Gaussian.Vector.Operational.Basic
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

/-! ## Scaling through one prepared fractional output -/

/-- One matrix action on `(1,tau)` is its denominator times the homogeneous vector of the prepared productive fractional
output. -/
@[expose] def matrixAction_fractional_scaled (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator matrix tau)) :
    Operational.Basic.VectorEquivalent
      (Action.matrixAction matrix (LegendreModularMonodromy.fractionalVector tau))
      (LegendreModularMonodromy.scaleVector (LegendreModularMonodromy.fractionalDenominator matrix tau)
        (LegendreModularMonodromy.fractionalVector (LegendreModularMonodromy.fractionalLinear matrix tau preparation)))
          := by
  intro coordinate
  refine Purelib.Data.Fin.casesDependent (motive := fun index =>
    Gaussian.Equivalence.NamedEquivalent
      (Action.matrixAction matrix (LegendreModularMonodromy.fractionalVector tau) index).name
      (LegendreModularMonodromy.scaleVector
        (LegendreModularMonodromy.fractionalDenominator matrix tau)
        (LegendreModularMonodromy.fractionalVector
          (LegendreModularMonodromy.fractionalLinear matrix tau preparation)) index).name)
    ?_ ?_ coordinate
  ·
    change Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator matrix tau).name
      (CoherentNamed.mul
        (LegendreModularMonodromy.fractionalDenominator matrix tau)
        (Coherence.exact 1)).name
    exact NamedEquivalent.symm
      (Mul.coherentMul_one_right
        (LegendreModularMonodromy.fractionalDenominator matrix tau))
  · intro tail
    refine Purelib.Data.Fin.casesDependent (motive := fun predecessor =>
      Gaussian.Equivalence.NamedEquivalent
        (Action.matrixAction matrix (LegendreModularMonodromy.fractionalVector tau)
          predecessor.succ).name
        (LegendreModularMonodromy.scaleVector
          (LegendreModularMonodromy.fractionalDenominator matrix tau)
          (LegendreModularMonodromy.fractionalVector
            (LegendreModularMonodromy.fractionalLinear matrix tau preparation))
          predecessor.succ).name)
      ?_ (fun impossible => Fin.elim0 impossible) tail
    change Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalNumerator matrix tau).name
      (CoherentNamed.mul
        (LegendreModularMonodromy.fractionalDenominator matrix tau)
        (LegendreModularMonodromy.fractionalLinear matrix tau preparation)).name
    exact NamedEquivalent.symm
      (LegendreModularMonodromy.denominator_mul_fractionalLinear matrix tau preparation)

/-- Fraction-free normalized composition with the inner quotient prepared: the combined homogeneous rows are the right
denominator times the outer rows evaluated at the inner productive output. -/
@[expose] def fractionalRows_mul_scaled (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed)
    (rightPreparation : Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator right tau)) :
    Operational.Basic.VectorEquivalent
      (Action.matrixAction (Multiplication.mul left right)
        (LegendreModularMonodromy.fractionalVector tau))
      (LegendreModularMonodromy.scaleVector (LegendreModularMonodromy.fractionalDenominator right tau)
        (Action.matrixAction left
          (LegendreModularMonodromy.fractionalVector
            (LegendreModularMonodromy.fractionalLinear right tau rightPreparation)))) :=
  VectorEquivalent.trans
    (Action.matrixAction_mul left right (LegendreModularMonodromy.fractionalVector tau))
    (VectorEquivalent.trans
      (Action.matrixAction_respects left
        (Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling.matrixAction_fractional_scaled right tau
          rightPreparation))
      (LegendreModularMonodromy.matrixAction_scale left (LegendreModularMonodromy.fractionalDenominator right tau)
        (LegendreModularMonodromy.fractionalVector
          (LegendreModularMonodromy.fractionalLinear right tau rightPreparation))))

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling
