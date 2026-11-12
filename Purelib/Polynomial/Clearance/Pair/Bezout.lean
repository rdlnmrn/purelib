module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational

/-!
# Retained coefficient square majorants

Finite coefficient readbacks retain their original polynomials and interval
data. Their exact rational majorants provide positive radius or clearance
bounds without changing the underlying coefficient computations.
-/

namespace Purelib.Polynomial.Clearance.Pair.Bezout

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Bounds
open Purelib.Data.Rat.Bounds
open Purelib.Polynomial

/-- Finite upper bound for the squared Bézout coefficients on an interval.

The two original Bézout cofactors are evaluated by their finite interval
Horner square bounds. The maximum of one and their bound sum retains
a strictly positive ceiling for the same two cofactors. -/
@[expose] public def bezoutSqMajorant {p q : Basic.CoordinatePolynomial}
    (certificate : Bezout.Basic.CoprimeCertificate p q) (interval : Interval.Bounds) :
      Rational :=
  max 1 (Bounds.Horner.evalSqBound certificate.left interval +
    Bounds.Horner.evalSqBound certificate.right interval)

/-- Refining the parameter interval can only decrease the squared Bezout-cofactor majorant.

The same retained Bézout cofactors are used on both intervals. Their
finite Horner bounds decrease under the supplied refinement, and the
original maximum with one transports that scalar comparison. -/
public theorem bezoutSqMajorant_le_of_refines {p q : Basic.CoordinatePolynomial}
    (certificate : Bezout.Basic.CoprimeCertificate p q) {interval root : Interval.Bounds}
    (refines : interval.Refines root) :
    bezoutSqMajorant certificate interval ≤
      bezoutSqMajorant certificate root := by
  apply Order.Basic.max_le
  · exact Order.Basic.le_max_left _ _
  · exact (add_le_add
      (Bounds.Horner.evalSqBound_le_of_refines certificate.left refines)
      (Bounds.Horner.evalSqBound_le_of_refines certificate.right refines)).trans
      (Order.Basic.le_max_right _ _)

/-- The computed squared-cofactor majorant is positive because it is at least one.

The original maximum retains one as a lower bound for the cofactor
majorant. Its strict positive comparison with zero proves positivity. -/
public theorem bezoutSqMajorant_pos {p q : Basic.CoordinatePolynomial}
    (certificate : Bezout.Basic.CoprimeCertificate p q) (interval : Interval.Bounds) :
    0 < bezoutSqMajorant certificate interval :=
  (show (0 : Rational) < 1 by decide).trans_le (Order.Basic.le_max_left _ _)

/-- The sum of squared Bezout-cofactor values lies below their interval majorant.

The supplied point belongs to the retained interval. Both original
cofactor evaluations have squares below their respective finite Horner
bounds, whose sum is bounded by the same majorant. -/
public theorem bezout_eval_sq_add_le_majorant {p q : Basic.CoordinatePolynomial}
    (certificate : Bezout.Basic.CoprimeCertificate p q) (interval : Interval.Bounds)
    {x : Rational} (inside : interval.Contains x) :
    certificate.left.eval x ^ 2 + certificate.right.eval x ^ 2 ≤
      bezoutSqMajorant certificate interval := by
  exact (add_le_add
    (Bounds.Horner.eval_sq_le_evalSqBound certificate.left interval inside)
    (Bounds.Horner.eval_sq_le_evalSqBound certificate.right interval inside)).trans
    (Order.Basic.le_max_right _ _)

/-- A finite Bézout certificate yields quantitative path clearance.

The original cofactor identity and sum-of-products square inequality
retain a positive reciprocal clearance bound. The returned certificate
uses those same polynomials, interval, cofactors and pointwise identity. -/
@[expose] public def certificateOfCoprime {p q : Basic.CoordinatePolynomial}
    (coprime : Bezout.Basic.CoprimeCertificate p q) (interval : Interval.Bounds) :
    Basic.Certificate p q interval where
  bound := 1 / bezoutSqMajorant coprime interval
  positive := by
    exact Order.Field.div_pos_direct (by decide)
      (bezoutSqMajorant_pos coprime interval)
  lower := by
    intro x inside
    let coefficientSq :=
      coprime.left.eval x ^ 2 + coprime.right.eval x ^ 2
    let valueSq := p.eval x ^ 2 + q.eval x ^ 2
    have coefficientNonnegative : 0 ≤ coefficientSq :=
      add_nonneg
        (Order.Arithmetic.sq_nonneg_direct _)
        (Order.Arithmetic.sq_nonneg_direct _)
    have valueNonnegative : 0 ≤ valueSq :=
      add_nonneg
        (Order.Arithmetic.sq_nonneg_direct _)
        (Order.Arithmetic.sq_nonneg_direct _)
    have coefficientBound : coefficientSq ≤
        bezoutSqMajorant coprime interval :=
      bezout_eval_sq_add_le_majorant coprime interval inside
    have identity := coprime.identity x
    have cauchy : 1 ≤ coefficientSq * valueSq := by
      calc
        1 = (coprime.left.eval x * p.eval x +
            coprime.right.eval x * q.eval x) ^ 2 := by rw [← identity]; ring1
        _ ≤ coefficientSq * valueSq := by
          exact Square.sum_product_sq_le_product_sums _ _ _ _
    have scaled : 1 ≤ bezoutSqMajorant coprime interval * valueSq :=
      cauchy.trans
        (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          coefficientBound valueNonnegative)
    apply (Order.Field.div_le_iff_pos
      (bezoutSqMajorant_pos coprime interval)).mpr
    dsimp only [valueSq] at scaled ⊢
    rw [Field.mul_comm]
    exact scaled

/-- Refining the interval can only improve the reciprocal Bezout clearance bound.

The original cofactor majorant decreases under the supplied interval
refinement. Both retained majorants are positive, so direct rational
division comparisons order their same reciprocal clearance bounds. -/
public theorem certificateOfCoprime_bound_le_of_refines {p q : Basic.CoordinatePolynomial}
    (coprime : Bezout.Basic.CoprimeCertificate p q) {interval root : Interval.Bounds}
    (refines : interval.Refines root) :
    (certificateOfCoprime coprime root).bound ≤
      (certificateOfCoprime coprime interval).bound := by
  have rootPositive := bezoutSqMajorant_pos coprime root
  have intervalPositive := bezoutSqMajorant_pos coprime interval
  have majorantLe := bezoutSqMajorant_le_of_refines coprime refines
  apply (Order.Field.le_div_iff_pos intervalPositive).2
  dsimp only [certificateOfCoprime]
  rw [Field.div_eq_mul_inv_direct,
    Field.one_mul, Field.mul_comm]
  change bezoutSqMajorant coprime interval /
      bezoutSqMajorant coprime root ≤ 1
  exact (Order.Field.div_le_iff_pos rootPositive).2 (by
    rw [Field.one_mul]
    exact majorantLe)

end Purelib.Polynomial.Clearance.Pair.Bezout
