module
public import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Positive.Basic
public import Purelib.RootIsolation.FTA.Positive.Input

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.FTA.Squarefree.Input

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Positive.Build

/-- Integrate the exact linear formula with the constructive box theorem. -/
def provePositive {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) : FTA.Positive.Basic.PositiveResult p := by
  cases degreeEq : p.natDegree with
  | zero =>
      have := input.degreePositive
      rw [degreeEq] at this
      exact (Nat.lt_asymm this this).elim
  | succ degree =>
      cases degree with
      | zero =>
          have linear : p.natDegree = 1 := degreeEq
          let data := Dense.Gaussian.Roots.Linear.rootData linear
          exact .linear ⟨data.point, data.root⟩ linear
      | succ degree =>
          have degreeAtLeastTwo : 2 ≤ p.natDegree := by
            rw [degreeEq]
            omega
          exact .higher (FTA.Squarefree.Build.BoxFTA.prove ⟨input.squarefree, degreeAtLeastTwo⟩)
            degreeAtLeastTwo

/-- Degree-greater-than-one specialization of the unified positive-degree
result. -/
def provePositiveDegreeGtOne
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : FTA.Positive.Basic.PositiveResult p :=
  .higher (FTA.Squarefree.Build.BoxFTA.proveDegreeGtOne squarefree degree) degree

end Purelib.RootIsolation.FTA.Positive.Build

end
