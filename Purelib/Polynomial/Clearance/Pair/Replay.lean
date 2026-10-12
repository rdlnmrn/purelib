module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.AffineHorner
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

public section

/-!
# Checking saved finite witnesses for an unchanged clearance bound

The cofactors are untrusted executable data.  A coefficient-list identity
checks their Bézout equation, and a cross-product check certifies the exact
requested bound.  Rejection of a weak witness is not failure of the line or
of another clearance-construction method.  No Euclidean search is performed
by this checker, and no reciprocal is needed in its executable success data.
-/

namespace Purelib.Polynomial.Clearance.Pair.Replay

open Fraction.Order

set_option genInjectivity false in
/-- Two displayed rational-polynomial cofactors proposed for an exact Bezout identity.

The coefficient tables are untrusted input until checked against the original polynomial pair. -/
structure Witness where
  /-- The proposed cofactor multiplying the first polynomial. -/ left : Dense.Rational.Basic.CoordinatePolynomial
  /-- The proposed cofactor multiplying the second polynomial. -/ right : Dense.Rational.Basic.CoordinatePolynomial

constructive_injectivity Witness

/-- The positive affine-Horner bound on the sum of squared retained Bezout-cofactor values.

The exact affine-Horner bounds of the original two retained cofactors are summed and floored at one on the supplied
interval. -/
@[expose] def checkedMajorant {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime :
  Dense.Rational.Bezout.Basic.CoprimeCertificate p q)
    (interval : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  max 1 (Dense.Rational.Bounds.AffineHorner.coefficientSqBound coprime.left interval +
    Dense.Rational.Bounds.AffineHorner.coefficientSqBound coprime.right interval)

/-- The checked cofactor majorant is positive because it is at least one.

The original rational maximum retains one as its left input independently of either cofactor value. -/
theorem checkedMajorant_positive {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime :
  Dense.Rational.Bezout.Basic.CoprimeCertificate p q)
    (interval : Data.Rat.Interval.Bounds) : 0 < checkedMajorant coprime interval :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le (Basic.le_max_left _ _)

/-- The checked cofactor majorant is no larger than the original finite Horner majorant.

Each retained cofactor bound is no larger than its original Horner bound, and the same rational floor at one preserves
that comparison. -/
theorem checkedMajorant_le_previous {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime :
  Dense.Rational.Bezout.Basic.CoprimeCertificate p q)
    (interval : Data.Rat.Interval.Bounds) : checkedMajorant coprime interval ≤
      Clearance.Pair.Bezout.bezoutSqMajorant coprime interval :=
  Basic.max_le (Basic.le_max_left _ _)
    ((Fraction.Order.Arithmetic.add_le_add_direct
      (Dense.Rational.Bounds.AffineHorner.coefficientSqBound_le_previous coprime.left interval)
      (Dense.Rational.Bounds.AffineHorner.coefficientSqBound_le_previous coprime.right interval)).trans
        (Basic.le_max_right _ _))

/-- An exact Bezout identity and accepted bound-majorant cross product certify the requested pair clearance throughout
the interval.

The original exact Bezout evaluation identity and accepted majorant cross product bound the sum of squares at every
supplied point of the same interval. -/
public theorem bound_le_values {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime :
  Dense.Rational.Bezout.Basic.CoprimeCertificate p q)
    (interval : Data.Rat.Interval.Bounds) (bound : Fraction.Rational)
    (carries : bound * checkedMajorant coprime interval ≤ 1)
    {x : Fraction.Rational} (inside : interval.Contains x) :
    bound ≤ p.eval x ^ 2 + q.eval x ^ 2 := by
  have coefficientBound : coprime.left.eval x ^ 2 + coprime.right.eval x ^ 2 ≤
      checkedMajorant coprime interval :=
    (Fraction.Order.Arithmetic.add_le_add_direct (Dense.Rational.Bounds.AffineHorner.eval_sq_le_coefficientSqBound
      coprime.left interval inside)
      (Dense.Rational.Bounds.AffineHorner.eval_sq_le_coefficientSqBound coprime.right interval inside)).trans
        (Basic.le_max_right _ _)
  have oneBound : (1 : Fraction.Rational) ≤
      (coprime.left.eval x ^ 2 + coprime.right.eval x ^ 2) * (p.eval x ^ 2 + q.eval x ^ 2) := by
    calc
      1 = (coprime.left.eval x * p.eval x + coprime.right.eval x * q.eval x) ^ 2 := by
        rw [← coprime.identity x]; ring1
      _ ≤ _ := Data.Rat.Bounds.Square.dot_sq_le_product_sums _ _ _ _
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := checkedMajorant coprime interval) _ (checkedMajorant_positive coprime interval)
  calc
    _ ≤ 1 := carries
    _ ≤ _ := oneBound
    _ ≤ checkedMajorant coprime interval * (p.eval x ^ 2 + q.eval x ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientBound
        (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    _ = _ := mul_comm _ _

set_option genInjectivity false in
/-- Exact evidence explaining rejection of a proposed clearance witness or requested bound.

The alternatives retain a nonpositive request, a failed coefficient identity, or the checked cofactors and computed
majorant whose cross product is too large. -/
inductive Failure where
  /-- The requested bound is not positive, with the original pair and interval retained. -/ | nonpositive (p q :
    Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) (bound : Fraction.Rational)
      (failed : ¬ 0 < bound)
  /-- The exact computed normalized cofactor combination differs from the constant one polynomial. -/ | identity (p q :
    Dense.Rational.Basic.CoordinatePolynomial) (witness : Witness) (actual : Dense.Rational.Basic.CoordinatePolynomial)
      (actual_eq : actual = (witness.left * p + witness.right * q).normalize)
      (failed : actual ≠ Dense.Basic.DensePolynomial.constant (1 : Fraction.Rational))
  /-- The checked bound-majorant product exceeds one, retaining both computed quantities and their equalities. -/ |
    insufficient (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) (bound
    : Fraction.Rational)
      (coprime : Dense.Rational.Bezout.Basic.CoprimeCertificate p q) (majorant : Fraction.Rational)
      (majorant_eq : majorant = checkedMajorant coprime interval)
      (product : Fraction.Rational) (product_eq : product = bound * majorant)
      (failed : ¬ product ≤ 1)

constructive_injectivity Failure

set_option genInjectivity false in
/-- Retain checked cofactors and their computed bound for downstream use.

The same checked cofactors, computed majorant and original interval identify the reconstructed certificate and its exact
requested rational bound. -/
structure Checked (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) (bound
  : Fraction.Rational) where
  /-- The checked original cofactors with their exact Bezout evaluation identity. -/ coprime :
    Dense.Rational.Bezout.Basic.CoprimeCertificate p q
  /-- The computed cofactor majorant on the retained interval. -/ majorant : Fraction.Rational
  /-- The cached majorant is exactly the checked affine-Horner result. -/ majorant_eq : majorant = checkedMajorant
    coprime interval
  /-- The resulting quantitative clearance certificate for the original pair and interval. -/ certificate :
    Clearance.Pair.Basic.Certificate p q interval
  /-- The resulting certificate carries exactly the requested bound. -/ bound_eq : certificate.bound = bound

constructive_injectivity Checked

/-- Check the original normalized cofactor table for the exact Bezout identity.

The original two cofactor tables are retained on success with their evaluation
identity. Failure retains the computed normalized combination and the proof
that it differs from the exact constant-one table. -/
@[expose] def checkCoprime (p q : Dense.Rational.Basic.CoordinatePolynomial) (witness : Witness) :
    Except Failure (Dense.Rational.Bezout.Basic.CoprimeCertificate p q) :=
  let actual := (witness.left * p + witness.right * q).normalize
  if identity : actual = Dense.Basic.DensePolynomial.constant (1 : Fraction.Rational) then
    .ok ⟨witness.left, witness.right, by
      intro x
      have values := congrArg (fun polynomial : Dense.Rational.Basic.CoordinatePolynomial => polynomial.eval x) identity
      simpa only [actual, Dense.Basic.DensePolynomial.eval_normalize, Dense.Basic.DensePolynomial.eval_add,
        Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_constant]
        using values.symm⟩
  else .error (.identity p q witness actual rfl identity)

/-- Consume already checked cofactors without recalculating their identity.

The checked cofactor identity is reused once; the original computed majorant and cross product are retained with either
the certified bound or their precise failed comparison. -/
@[expose] def checkCertified {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime :
  Dense.Rational.Bezout.Basic.CoprimeCertificate p q)
    (interval : Data.Rat.Interval.Bounds) (bound : Fraction.Rational) : Except Failure (Checked p q interval
      bound) :=
  if positive : 0 < bound then
    let majorant := checkedMajorant coprime interval
    let product := bound * majorant
    if carries : product ≤ 1 then
      .ok
        { coprime := coprime, majorant := majorant, majorant_eq := rfl,
          certificate :=
            { bound := bound, positive := positive, lower := by
                intro x inside
                exact bound_le_values coprime interval bound carries inside },
          bound_eq := rfl }
    else .error (.insufficient p q interval bound coprime majorant rfl product rfl carries)
  else .error (.nonpositive p q interval bound positive)

/-- Check the saved cofactor identity and requested bound, returning the retained clearance certificate or exact
rejection evidence.

The original cofactor check runs once before the same certified majorant check, preserving the exact retained success
data and typed failure evidence. -/
@[expose] def check (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds)
  (bound : Fraction.Rational)
    (witness : Witness) : Except Failure (Checked p q interval bound) := do
  let coprime ← checkCoprime p q witness
  checkCertified coprime interval bound

end Purelib.Polynomial.Clearance.Pair.Replay

end
