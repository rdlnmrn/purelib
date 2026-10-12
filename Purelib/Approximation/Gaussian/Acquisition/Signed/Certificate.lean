module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition (State)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate

/-- Negative evidence refers to candidates, so its bound persists even when future displayed balls are not contained in
the inspected ball. -/
structure Negative (tau : Coherent.CoherentNamed)
  (state : State tau) (delta : Fraction.Rational) : Type where
  /-- Every possible candidate at the retained source has imaginary coordinate at most minus one quarter of the
    displayed threshold. -/ upper : ∀ {value : Canonical}, tau.name.process.Possible
    state.retained.source value →
    value.im ≤ -(delta / 4)

/-- Persistent candidate evidence that a retained Gaussian name state lies within the displayed imaginary-coordinate
threshold.

Every possible candidate has imaginary coordinate strictly between minus delta and delta; no equality or zero verdict is
asserted. -/
structure Near (tau : Coherent.CoherentNamed)
  (state : State tau) (delta : Fraction.Rational) : Type where
  /-- Every possible candidate at the retained source has imaginary coordinate strictly between the two displayed
    thresholds. -/ bounds : ∀ {value : Canonical}, tau.name.process.Possible state.retained.source
    value →
    -delta < value.im ∧ value.im < delta

/-- Transport the retained negative candidate bound along an explicit source-persistence certificate. -/
def Negative.after {tau : Coherent.CoherentNamed}
  {first last : State tau} {delta : Fraction.Rational}
    (negative : Negative tau first delta)
    (persists : ∀ {value : Canonical}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) :
        Negative tau last delta :=
  ⟨fun possible => negative.upper (persists possible)⟩

/-- Transport the retained near-boundary candidate bounds along an explicit source-persistence certificate. -/
def Near.after {tau : Coherent.CoherentNamed}
  {first last : State tau} {delta : Fraction.Rational}
    (near : Near tau first delta)
    (persists : ∀ {value : Canonical}, tau.name.process.Possible last.retained.source value →
      tau.name.process.Possible first.retained.source value) :
        Near tau last delta :=
  ⟨fun possible => near.bounds (persists possible)⟩
end Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate

end
