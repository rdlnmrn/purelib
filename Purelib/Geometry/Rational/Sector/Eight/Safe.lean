module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Geometry.Rational.Sector.Eight

/-- The overlapping contraction predicate needed by a redundant sector choice. Unlike `Sector.Holds`, different
representatives may safely hold at the same displayed point. -/
def Safe (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
  Data.Gaussian.Basic.Canonical) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 1 / 2

namespace Safe

/-- Decide local sector safety by the exact rational residual-quadrance comparison. -/
instance safeDecidable
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
  Data.Gaussian.Basic.Canonical) :
    Decidable (Safe sector value) := by
  unfold Safe
  infer_instance

end Safe

end Purelib.Geometry.Rational.Sector.Eight

end
