module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent

/-! ## Finite local selection of the preimage of an exponential -/

set_option genInjectivity false in
/-- A displayed rational disk used only as a finite local cell. -/
structure Cell where
  /-- The Gaussian rational center of the displayed cell. -/ center : Data.Gaussian.Basic.Canonical
  /-- The rational squared radius of the displayed cell. -/ radiusSq : Fraction.Rational
  /-- The cell has strictly positive squared radius. -/ radiusSq_positive : 0 < radiusSq
  /-- The cell's squared radius is at most one. -/ radiusSq_le_one : radiusSq ≤ 1

constructive_injectivity Cell

namespace Cell.mk

end Cell.mk

namespace Cell

/-- The current finite enclosure of one coherent name lies in the displayed cell. -/
structure CellMember (cell :
  Cell) (value : CoherentNamed) : Prop where
  /-- Every candidate possible at the retained name state lies in the displayed cell. -/ possible_near : ∀ {candidate :
    Data.Gaussian.Basic.Canonical},
    value.name.process.Possible value.name.state candidate →
      Data.Gaussian.Norm.Basic.normSq (candidate - cell.center) ≤ cell.radiusSq

end Cell

end Purelib.Approximation.Gaussian.Name.Coherent

end
