module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Laws
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Inverse

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition
open Purelib.Approximation.Gaussian.Name
open Purelib.LinearAlgebra.Matrix

public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

/-- A certified left inverse undoes the corresponding productive inner action when all three precisely indexed
denominators have been prepared. -/
@[expose] def fractionalLinear_inverse_of_mul_eq_identity
    (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation left right tau)
    (inverse : Multiplication.mul left right =
      Multiplication.identity) :
    Gaussian.Equivalence.NamedEquivalent preparation.nestedOutput.name tau.name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (Laws.fractionalLinear_mul left right tau preparation))
    (Identity.fractionalLinear_of_matrix_eq_identity
      (Multiplication.mul left right) tau
      preparation.combined inverse)

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Inverse
