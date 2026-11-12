module

import Purelib.Polynomial.Winding.Circle.Transport

/-!
# Independent conjugate winding of a complex linear factor

A nonreal root strictly inside the circle and a nonreal leading coefficient
supply actual original clearances and chart substitutions on both sides.
The independently computed raw readings retain their positive orientation.
-/

namespace TestPurelib.Polynomial.Winding.Circle.Transport

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Winding.Circle
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RationalFunctions.Curve.Canonical.Circle

/-- The original strictly inside nonreal root. -/
private def root : Canonical := ⟨1/4, 1/4⟩

/-- The original nonreal leading coefficient. -/
private def scalar : Canonical := ⟨2, 1⟩

/-- The original dense coefficient owner retains the scaled complex linear factor. -/
private def polynomial := DensePolynomial.scale scalar (LinearFactor.linearFactor root)

/-- Original finite linear-factor and scale constructors supply the actual whole-circle margin. -/
private def clearance : Certificate polynomial :=
  (Certificate.linearInside root (by decide +kernel)).scale scalar (by decide +kernel)

/-- The source uses its own actual original chart-substitution constructor. -/
private def source := Boundary.Substitutions.prepare polynomial

/-- The coefficient conjugate uses its own actual original chart-substitution constructor. -/
private def target := Boundary.Substitutions.prepare (Conjugate.polynomial polynomial)

/-- The original independent source winding is positive one, represented by its raw value four. -/
private theorem source_raw : raw source = 4 :=
  (raw_scale (Certificate.linearInside root (by decide +kernel)) scalar (by decide +kernel)
    (Boundary.Substitutions.prepare (LinearFactor.linearFactor root)) source).trans
      (raw_linearInside root (by decide +kernel) _)

/-- The actual independently substituted conjugate has the same positive raw reading. -/
private theorem target_raw : raw target = 4 := (raw_conjugate clearance source target).trans source_raw

/-- Direct kernel evaluation independently checks both original Cauchy-index results. -/
private theorem actual_raw_values : raw source = 4 ∧ raw target = 4 := by decide +kernel

/-- The transformed complete-circle certificate retains the same original quantitative payment. -/
private theorem same_margin : clearance.conjugate.bound = clearance.bound := rfl

/-- The reversed nonreal linear factor has its own independently prepared paths. -/
private def reversedPaths := Boundary.Substitutions.prepare (Reciprocal.reversed polynomial)

/-- The independently computed reciprocal winding is the degree complement. -/
private theorem reversed_raw : raw reversedPaths = 0 := by
  have result := raw_reversed clearance source reversedPaths
  rewrite [source_raw] at result
  exact result.trans (by decide +kernel)

/-- Kernel evaluation checks the actual reciprocal chart events independently of the transport theorem. -/
private theorem actual_reversed_raw : raw reversedPaths = 0 := by decide +kernel

/-- The actual reciprocal margin retains the original quantitative payment unchanged. -/
private theorem reversed_margin : clearance.reversed.bound = clearance.bound := rfl

/-- A positive-support monomial retains its actual triple zero root in the source polynomial. -/
private def monomial := DensePolynomial.shift 3 (DensePolynomial.constant (1 : Canonical))

/-- The original coordinate shift supplies the monomial's same unit margin. -/
private def monomialClearance : Certificate monomial :=
  (Certificate.constant 1 (by decide +kernel)).shift 3

/-- The actual monomial and reciprocal chart results include the disappearing triple zero root. -/
private theorem actual_monomial_raw :
    raw (Boundary.Substitutions.prepare monomial) = 12 ∧
      raw (Boundary.Substitutions.prepare (Reciprocal.reversed monomial)) = 0 := by decide +kernel

/-- The general reversal law also accounts for the original degree-three zero-root block. -/
private theorem monomial_reversal :
    raw (Boundary.Substitutions.prepare (Reciprocal.reversed monomial)) =
      4 * (monomial.natDegree : Int) - raw (Boundary.Substitutions.prepare monomial) :=
  raw_reversed monomialClearance _ _

end TestPurelib.Polynomial.Winding.Circle.Transport
