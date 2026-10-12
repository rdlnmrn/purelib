module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Rational.Geometric.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Rational

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Sequence.UnitDisk

set_option genInjectivity false in
/-- Gaussian rational samples with a unit-disk bound and explicit quarter-power movement certificate.

Every stage retains an actual finite sample, and later-stage movement is bounded using scale four at the earlier index.
-/
structure UnitDiskSamples where
  /-- The actual Gaussian rational sample at each finite stage. -/ value : Nat → Data.Gaussian.Basic.Canonical
  /-- Every displayed sample has squared norm at most one. -/ unit : ∀ index, Data.Gaussian.Norm.Basic.normSq
    (value index) ≤ 1
  /-- Later samples differ from the earlier sample by at most its scale-four quarter-radius allowance. -/ close : ∀
    {oldIndex newIndex : Nat}, oldIndex ≤ newIndex →
    Data.Gaussian.Norm.Basic.normSq (value newIndex - value oldIndex) ≤
      Geometric.Basic.quarterRadius 4 oldIndex

constructive_injectivity UnitDiskSamples

end Purelib.Approximation.Gaussian.Sequence.UnitDisk

end
