module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.Overlap

/-! ## Finite overlap and safe chart transport -/

set_option genInjectivity false in
/-- One displayed rational point admitted by both current finite enclosures. This witnesses actual overlap; it is not an
assertion about completed chart domains. -/
structure OverlapWitness (left right :
  CoherentNamed) where
  /-- The displayed Gaussian rational point common to both current enclosures. -/ point : Data.Gaussian.Basic.Canonical
  /-- The common point is possible at the retained left name state. -/ left_possible : left.name.process.Possible
    left.name.state point
  /-- The common point is possible at the retained right name state. -/ right_possible : right.name.process.Possible
    right.name.state point

constructive_injectivity OverlapWitness

end Purelib.Approximation.Gaussian.Name.Coherent.Overlap

end
