module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Contraction
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.RootIsolation.Sturm.Track.Basic
public import Purelib.RootIsolation.Sturm.Track.Refinement
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.RootIsolation.Sturm.Track.Basic (State)

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

namespace Purelib.RootIsolation.Sturm.Track.Request

/-- Explicit finite depth sufficient for a requested positive width. -/
def requestDepth (current : State polynomial)
  (epsilon : Fraction.Rational) : Nat :=
  Approximation.Rational.Contraction.geometricDepth
    (Bounds.width current.cell.interval) epsilon

/-- Total finite nonzero-event width request. -/
def request
    (polynomial : CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Fraction.Rational) : State polynomial :=
  Sturm.Track.Refinement.refineN polynomial polynomialNonzero current (requestDepth current epsilon)

/-- The requested nonzero-event refinement stays within the original parameter interval. -/
theorem request_refines
    (polynomial : CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Fraction.Rational) :
    (request polynomial polynomialNonzero current epsilon).cell.interval.Refines
      current.cell.interval :=
  Sturm.Track.Refinement.refineN_refines polynomial polynomialNonzero current
    (requestDepth current epsilon)

/-- A positive width request returns an event interval no wider than that exact request. -/
theorem request_width_le
    (polynomial : CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Bounds.width (request polynomial polynomialNonzero current
      epsilon).cell.interval) ≤
      epsilon := by
  exact (Sturm.Track.Refinement.refineN_width_le polynomial polynomialNonzero current
    (requestDepth current epsilon)).trans
      (Approximation.Rational.Contraction.geometricDepth_sufficient
        (Bounds.width_nonneg current.cell.interval) positive)

end Purelib.RootIsolation.Sturm.Track.Request

end
