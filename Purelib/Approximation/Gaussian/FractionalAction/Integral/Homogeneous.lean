module
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
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

/-! ## Convention-locked homogeneous composition -/

/-- The homogeneous fractional rows of `left * right` are obtained by acting with `right` first and then `left`.

This is the division-free composition law and fixes the multiplication order used throughout the module. -/
@[expose] def fractionalRows_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed) :
    Operational.Basic.VectorEquivalent
      (fun row => LegendreModularMonodromy.fractionalRow
        (Multiplication.mul left right) tau row)
      (Action.matrixAction left (fun row => LegendreModularMonodromy.fractionalRow right tau row)) := by
  simpa only [LegendreModularMonodromy.fractionalRow] using
    (Action.matrixAction_mul left right (LegendreModularMonodromy.fractionalVector tau))

/-- Row-zero form of homogeneous composition. -/
@[expose] def fractionalDenominator_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalDenominator
        (Multiplication.mul left right) tau).name
      (Action.matrixAction left (fun row => LegendreModularMonodromy.fractionalRow right tau row) 0).name :=
  Approximation.Gaussian.FractionalAction.Integral.Homogeneous.fractionalRows_mul left right tau 0

/-- Row-one form of homogeneous composition. -/
@[expose] def fractionalNumerator_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalNumerator
        (Multiplication.mul left right) tau).name
      (Action.matrixAction left (fun row => LegendreModularMonodromy.fractionalRow right tau row) 1).name :=
  Approximation.Gaussian.FractionalAction.Integral.Homogeneous.fractionalRows_mul left right tau 1

/-- Homogeneous normalized columns respect operational equality of their `tau` coordinates. -/
@[expose] def fractionalVector_respects {first second : Coherent.CoherentNamed}
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    Operational.Basic.VectorEquivalent (LegendreModularMonodromy.fractionalVector first)
      (LegendreModularMonodromy.fractionalVector second) := by
  intro coordinate
  refine Purelib.Data.Fin.casesDependent (motive := fun index =>
    Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalVector first index).name
      (LegendreModularMonodromy.fractionalVector second index).name) ?_ ?_ coordinate
  · exact NamedEquivalent.refl _
  · intro tail
    refine Purelib.Data.Fin.casesDependent (motive := fun predecessor =>
      Gaussian.Equivalence.NamedEquivalent
        (LegendreModularMonodromy.fractionalVector first predecessor.succ).name
        (LegendreModularMonodromy.fractionalVector second predecessor.succ).name)
      ?_ (fun impossible => Fin.elim0 impossible) tail
    change Gaussian.Equivalence.NamedEquivalent
      (LegendreModularMonodromy.fractionalVector first (1 : Fin 2)).name
      (LegendreModularMonodromy.fractionalVector second (1 : Fin 2)).name
    simpa only [LegendreModularMonodromy.fractionalVector_one] using equivalent

/-- If `left * right` is the identity, the corresponding homogeneous nested action returns `(1,tau)` without any
division premise. -/
@[expose] def fractionalRows_inverse_of_mul_eq_identity
    (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (inverse : Multiplication.mul left right =
      Multiplication.identity) :
    Operational.Basic.VectorEquivalent
      (Action.matrixAction left
        (Action.matrixAction right (LegendreModularMonodromy.fractionalVector tau)))
      (LegendreModularMonodromy.fractionalVector tau) :=
  VectorEquivalent.trans
    (VectorEquivalent.symm
      (Action.matrixAction_mul left right (LegendreModularMonodromy.fractionalVector tau)))
    (by
        simpa only [inverse]
          using (Action.matrixAction_identity (LegendreModularMonodromy.fractionalVector tau)))

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
