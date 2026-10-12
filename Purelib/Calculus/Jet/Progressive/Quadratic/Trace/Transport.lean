module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Quadratic.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

/-! ## Pointwise semantic closure with explicit finite transport -/

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
set_option genInjectivity false in
/-- Geometric closeness and quadrance bounds for a fixed sequence of certificates.

The increment and certificate sequence are parameters, preserving their identity. The retained scale and center bound
control the increment, base, output, slope and remainder at all displayed indices. -/
structure Transport (increment : Nat →
  Canonical)
    (certificates : (index : Nat) → Certificate (increment index)) where
  /-- The common rational scale of the geometric closeness allowance. -/ errorScale : Rat.Fraction.Rational
  /-- The common geometric error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- The increment samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    increment_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Canonical.normSq (increment later - increment earlier) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The base samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    base_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Canonical.normSq ((certificates later).base - (certificates earlier).base) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The output samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    output_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Canonical.normSq ((certificates later).output - (certificates earlier).output) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The slope samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    slope_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Canonical.normSq ((certificates later).slope - (certificates earlier).slope) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The remainder samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    remainder_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Canonical.normSq ((certificates later).remainder -
      (certificates earlier).remainder) ≤
        Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The common rational upper bound for the five displayed quadrances. -/ centerBound : Rat.Fraction.Rational
  /-- The common quadrance bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every displayed increment sample has quadrance at most the common center bound. -/ increment_bounded : ∀ index,
    Canonical.normSq (increment index) ≤ centerBound
  /-- Every displayed base sample has quadrance at most the common center bound. -/ base_bounded : ∀ index,
    Canonical.normSq (certificates index).base ≤ centerBound
  /-- Every displayed output sample has quadrance at most the common center bound. -/ output_bounded : ∀ index,
    Canonical.normSq (certificates index).output ≤ centerBound
  /-- Every displayed slope sample has quadrance at most the common center bound. -/ slope_bounded : ∀ index,
    Canonical.normSq (certificates index).slope ≤ centerBound
  /-- Every displayed remainder sample has quadrance at most the common center bound. -/ remainder_bounded : ∀ index,
    Canonical.normSq (certificates index).remainder ≤ centerBound

constructive_injectivity Transport

namespace Transport.mk

end Transport.mk

namespace Transport.mk

end Transport.mk

open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Package a fixed certificate sequence with its retained transport evidence.

The resulting trace uses exactly the supplied sequence, scale, center bound and estimates; no samples or certificates
are recomputed. -/
def ofTransport {increment : Nat →
  Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (transport : Transport increment certificates) : Trace increment :=
  { certificate := certificates
    errorScale := transport.errorScale
    errorScale_nonneg := transport.errorScale_nonneg
    increment_later_close := transport.increment_later_close
    base_later_close := transport.base_later_close
    output_later_close := transport.output_later_close
    slope_later_close := transport.slope_later_close
    remainder_later_close := transport.remainder_later_close
    centerBound := transport.centerBound
    centerBound_nonneg := transport.centerBound_nonneg
    increment_bounded := transport.increment_bounded
    base_bounded := transport.base_bounded
    output_bounded := transport.output_bounded
    slope_bounded := transport.slope_bounded
    remainder_bounded := transport.remainder_bounded }
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
