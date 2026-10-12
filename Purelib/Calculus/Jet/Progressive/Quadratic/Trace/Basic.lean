module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Calculus.Jet.Quadratic.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
set_option genInjectivity false in
/-- A sequence of exact quadratic certificates sharing geometric closeness and quadrance bounds.

At each natural index, the certificate uses the indexed increment. The increment and four certificate fields share one
nonnegative error scale and center bound, with explicit estimates between every pair of ordered indices. -/
structure Trace (increment : Nat →
  Gaussian.Basic.Canonical) where
  /-- The exact quadratic certificate for each indexed increment. -/ certificate : (index : Nat) → Certificate
    (increment index)
  /-- The common rational scale of the geometric closeness allowance. -/ errorScale : Rat.Fraction.Rational
  /-- The common geometric error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- The increment samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    increment_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Gaussian.Basic.Canonical.normSq (increment later - increment earlier) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The base samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    base_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Gaussian.Basic.Canonical.normSq ((certificate later).base - (certificate earlier).base) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The output samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    output_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Gaussian.Basic.Canonical.normSq ((certificate later).output - (certificate earlier).output) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The slope samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    slope_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Gaussian.Basic.Canonical.normSq ((certificate later).slope - (certificate earlier).slope) ≤
      Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The remainder samples at any two ordered indices differ by quadrance at most the earlier geometric allowance. -/
    remainder_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    Gaussian.Basic.Canonical.normSq ((certificate later).remainder -
      (certificate earlier).remainder) ≤
        Rational.Geometric.Basic.quarterRadius errorScale earlier
  /-- The common rational upper bound for the five displayed quadrances. -/ centerBound : Rat.Fraction.Rational
  /-- The common quadrance bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every displayed increment sample has quadrance at most the common center bound. -/ increment_bounded : ∀ index,
    Gaussian.Basic.Canonical.normSq (increment index) ≤ centerBound
  /-- Every displayed base sample has quadrance at most the common center bound. -/ base_bounded : ∀ index,
    Gaussian.Basic.Canonical.normSq (certificate index).base ≤ centerBound
  /-- Every displayed output sample has quadrance at most the common center bound. -/ output_bounded : ∀ index,
    Gaussian.Basic.Canonical.normSq (certificate index).output ≤ centerBound
  /-- Every displayed slope sample has quadrance at most the common center bound. -/ slope_bounded : ∀ index,
    Gaussian.Basic.Canonical.normSq (certificate index).slope ≤ centerBound
  /-- Every displayed remainder sample has quadrance at most the common center bound. -/ remainder_bounded : ∀ index,
    Gaussian.Basic.Canonical.normSq (certificate index).remainder ≤ centerBound

constructive_injectivity Trace

namespace Trace.mk

end Trace.mk

namespace Trace.mk

end Trace.mk

end Purelib.Calculus.Jet.Progressive.Quadratic

end

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.CCL.Progressive.PartialCalculus
universe u
end Purelib.CCL.Progressive.PartialCalculus

end
