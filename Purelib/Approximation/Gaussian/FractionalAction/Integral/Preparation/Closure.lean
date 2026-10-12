module
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Division.Prepared.Bounded
public import Purelib.Approximation.Gaussian.Division.Prepared.Ratio
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Matrix.Operational.Integral.Action

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Inverse

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Closure
open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- Transport an all-matrix denominator provider through a prepared invertible fractional action.

For each outer matrix, the combined and inner preparations yield an apart quotient equivalent to the outer denominator.
The original prepared processes and their comparison witnesses are retained. -/
def after {tau :
  Coherent.CoherentNamed} (provider : Preparation.Basic.Provider tau)
    (right : LinearAlgebra.Matrix.Basic.IntegralMatrix) (rightInverse : Right.RightInverse right)
    (inner : Prepared.DenominatorPreparation (fractionalDenominator right tau)) :
    Preparation.Basic.Provider (fractionalLinear right tau inner) := by
  intro left leftInverse
  let combined := provider (Multiplication.mul left right)
    (Right.mulInverse leftInverse rightInverse)
  let bottom := Bounded.basedPreparation inner
  let outer := fractionalDenominator left (fractionalLinear right tau inner)
  let value := Ratio.quotient combined inner
  let ready := DenominatorPreparation.ofPossibleApart value (Ratio.quotientApart combined inner)
  have scaled := Scaling.fractionalRows_mul_scaled left right tau inner 0
  have leftScaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul bottom.prepared outer).name
      combined.prepared.name :=
    NamedEquivalent.trans
      (Congruence.coherentMul_respects _ _ _ _
        (NamedEquivalent.symm bottom.equivalent)
        (NamedEquivalent.refl _))
      (NamedEquivalent.trans
        (NamedEquivalent.symm scaled) combined.equivalent)
  have rightScaled : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul bottom.prepared value).name
      combined.prepared.name :=
    NamedEquivalent.trans
      (Laws.coherentMul_comm _ _)
      (Cancellation.coherentDiv_mul_cancel _ _ bottom.apart)
  have equal := Cancellation.coherentMul_cancel_left
    bottom.prepared outer value bottom.apart
    (NamedEquivalent.trans leftScaled
      (NamedEquivalent.symm rightScaled))
  exact
    { prepared := ready.prepared
      apart := ready.apart
      equivalent := NamedEquivalent.trans equal ready.equivalent }

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Closure

end
