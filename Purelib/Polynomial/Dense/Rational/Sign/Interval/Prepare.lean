module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Retained endpoint sign preparation

A finite squared Lipschitz margin is checked at the interval's retained
lower endpoint. Successful preparation returns that exact endpoint and
its original mathematical certificate.
-/

namespace Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Executable left-endpoint sign classifier.  The successful branch returns
the proof-bearing certificate whose tested inequality is definitionally the
Boolean comparison just performed.

The original finite Lipschitz bound and endpoint radius are compared
with the squared value at the same retained lower endpoint. A successful
branch retains that endpoint, its containment proof and the tested margin. -/
@[expose] public def certificate? (p : Dense.Rational.Basic.CoordinatePolynomial) (interval :
  Data.Rat.Interval.Bounds) :
    Option (Dense.Rational.Sign.Interval.Basic.Certificate p interval) :=
  if margin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
      Interval.Radius.sampleRadiusSq interval interval.lower < p.eval interval.lower ^ 2 then
    some
      { sample := interval.lower
        sampleInside := ⟨le_rfl, interval.valid⟩
        margin := margin }
  else none

/-- The endpoint classifier succeeds exactly when its computed strict squared margin holds.

The original decidable margin chooses either the retained endpoint
certificate or none. The forward and reverse implications follow the same
chosen branch without changing the certificate or comparison. -/
public theorem certificate?_isSome_iff (p : Dense.Rational.Basic.CoordinatePolynomial) (interval :
  Data.Rat.Interval.Bounds) :
    (certificate? p interval).isSome = true ↔
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
          Interval.Radius.sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2 := by
  unfold certificate?
  by_cases margin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
      Interval.Radius.sampleRadiusSq interval interval.lower < p.eval interval.lower ^ 2
  · rw [dif_pos margin]
    exact ⟨fun _ => margin, fun _ => rfl⟩
  · rw [dif_neg margin]
    constructor
    · intro impossible
      cases impossible
    · intro strictMargin
      exact (margin strictMargin).elim

/-- A returned sign certificate entails the strict margin tested at the lower endpoint.

The returned original certificate can occur only in the successful
branch of the endpoint margin comparison. Its retained strict inequality
is exactly the displayed margin of the original classifier. -/
public theorem certificate?_some_margin {p : Dense.Rational.Basic.CoordinatePolynomial} {interval :
  Data.Rat.Interval.Bounds}
    {certificate : Dense.Rational.Sign.Interval.Basic.Certificate p interval}
    (found : certificate? p interval = some certificate) :
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
        Interval.Radius.sampleRadiusSq interval interval.lower <
      p.eval interval.lower ^ 2 := by
  unfold certificate? at found
  split at found
  · assumption
  · contradiction

end Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
