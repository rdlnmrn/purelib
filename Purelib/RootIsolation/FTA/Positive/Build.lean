module
import Purelib.Data.Rat.Fraction.Basic
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
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.RootIsolation

open Purelib.Data.Rat.Fraction (Rational)

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

open Purelib.Polynomial.Dense.Gaussian

/-- Construct the original positive-degree result from its retained coefficient degree.

The degree readback identifies the original polynomial. Degree one retains
its exact linear formula; higher degrees retain the complete coefficient-
selected box family and its original squarefree certificate.
-/
def fromDegree {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (degree : Nat) (degreeEq : p.natDegree = degree)
    (request : Option Rational := none) :
    FTA.Positive.Basic.PositiveResult p := by
  cases degree with
  | zero =>
      have := input.degreePositive
      rw [degreeEq] at this
      exact (Nat.lt_asymm this this).elim
  | succ degree =>
      cases degree with
      | zero =>
          have linear : p.natDegree = 1 := degreeEq
          let data := Roots.Linear.rootData linear
          exact .linear ⟨data.point, data.root⟩ linear
      | succ degree =>
          have degreeAtLeastTwo : 2 ≤ p.natDegree := by
            rw [degreeEq]
            omega
          exact .higher (Squarefree.Build.BoxFTA.prove ⟨input.squarefree, degreeAtLeastTwo⟩ request)
            degreeAtLeastTwo

/-- Integrate the exact linear formula with the constructive box theorem. -/
def provePositive {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (request : Option Rational := none) :
    FTA.Positive.Basic.PositiveResult p :=
  fromDegree input p.natDegree rfl request

/-- Reading the same original coefficient degree preserves the complete positive-degree result. -/
theorem fromDegree_eq_provePositive
    {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (degree : Nat) (same : p.natDegree = degree)
    (request : Option Rational := none) :
    fromDegree input degree same request = provePositive input request := by
  cases same
  rfl

/-- The original positive-degree constructor selects the same complete box result when the degree is at least two. -/
theorem provePositive_eq_higher
    {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (request : Option Rational := none) :
    provePositive input request = .higher
      (Squarefree.Build.BoxFTA.prove ⟨input.squarefree, degreeAtLeastTwo⟩ request) degreeAtLeastTwo := by
  cases degreeEq : p.natDegree with
  | zero =>
      have impossible : 2 ≤ 0 := degreeEq ▸ degreeAtLeastTwo
      exact False.elim (Nat.not_succ_le_zero 1 impossible)
  | succ degree =>
      cases degree with
      | zero =>
          have impossible : 2 ≤ 1 := by
            rewrite [degreeEq] at degreeAtLeastTwo
            exact degreeAtLeastTwo
          exact False.elim (Nat.not_succ_le_self 1 impossible)
      | succ degree =>
          exact (fromDegree_eq_provePositive input (degree + 1 + 1) degreeEq request).symm

/-- A retained original complete isolation gives the same higher positive-degree result.

The cached family receives the original ownership and maximality
certificates. Its equality identifies the complete original result without
executing its isolation producer again.
-/
theorem fromIsolation_eq_provePositive
    {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (isolation : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
    {request : Option Rational}
    (same : isolation = (FTA.Squarefree.Input.mk input.squarefree degreeAtLeastTwo).isolation request) :
    FTA.Positive.Basic.PositiveResult.higher
      (Squarefree.Build.BoxFTA.fromIsolation ⟨input.squarefree, degreeAtLeastTwo⟩ isolation) degreeAtLeastTwo =
      provePositive input request :=
  (congrArg (fun boxes => FTA.Positive.Basic.PositiveResult.higher boxes degreeAtLeastTwo)
    (Squarefree.Build.BoxFTA.fromIsolation_eq_prove ⟨input.squarefree, degreeAtLeastTwo⟩ isolation
      (request := request) same)).trans
    (provePositive_eq_higher input degreeAtLeastTwo request).symm

/-- Degree-greater-than-one specialization of the unified positive-degree
result. -/
def provePositiveDegreeGtOne
    {p : CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) (request : Option Rational := none) : FTA.Positive.Basic.PositiveResult p :=
  .higher (Squarefree.Build.BoxFTA.proveDegreeGtOne squarefree degree request) degree

/-- The absent event request retains the original degree selector and complete positive result. -/
theorem provePositive_none {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) :
    provePositive input none = fromDegree input p.natDegree rfl := rfl

/-- Every request preserves the exact original degree-one formula and its root certificate. -/
theorem fromDegree_linear {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (degree : p.natDegree = 1)
    (request : Option Rational) :
    fromDegree input 1 degree request = .linear
      ⟨(Roots.Linear.rootData degree).point,
        (Roots.Linear.rootData degree).root⟩ degree := rfl

/-- The shared original degree branches preserve the complete earlier positive-degree value.

This equation retains the original nested degree cases, actual linear root
record and complete squarefree box result, including every owner operation.
-/
theorem provePositive_eq_original
    {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) : provePositive input = (by
  cases degreeEq : p.natDegree with
  | zero =>
      have := input.degreePositive
      rw [degreeEq] at this
      exact (Nat.lt_asymm this this).elim
  | succ degree =>
      cases degree with
      | zero =>
          have linear : p.natDegree = 1 := degreeEq
          let data := Roots.Linear.rootData linear
          exact .linear ⟨data.point, data.root⟩ linear
      | succ degree =>
          have degreeAtLeastTwo : 2 ≤ p.natDegree := by
            rw [degreeEq]
            omega
          exact .higher (Squarefree.Build.BoxFTA.prove ⟨input.squarefree, degreeAtLeastTwo⟩)
            degreeAtLeastTwo) := by
  rfl

/-- A certified linear degree selects the same original rational root record at every supplied request. -/
theorem provePositive_linear {p : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) (linear : p.natDegree = 1)
    (request : Option Rational := none) :
    provePositive input request = .linear
      ⟨(Roots.Linear.rootData linear).point,
        (Roots.Linear.rootData linear).root⟩ linear :=
  (fromDegree_eq_provePositive input 1 linear request).symm

end Purelib.RootIsolation.FTA.Positive.Build

end
