module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
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
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sequence

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

set_option genInjectivity false in
/-- A Gaussian sample sequence retained inside the local logarithm disk.

Each sample has squared norm at most one ninth, and every later sample remains within the earlier index's scale-four
quarter-radius allowance. -/
structure DiskSamples where
  /-- The Gaussian value retained at each finite sample index. -/ value : Nat → Data.Gaussian.Basic.Canonical
  /-- Every retained sample has squared norm at most one ninth. -/ bound : ∀ index,
    Data.Gaussian.Norm.Basic.normSq (value index) ≤ 1 / 9
  /-- Every later sample is within the earlier index's scale-four quarter-radius allowance. -/ close : ∀ {oldIndex
    newIndex : Nat}, oldIndex ≤ newIndex →
    Data.Gaussian.Norm.Basic.normSq (value newIndex - value oldIndex) ≤
      Geometric.Basic.quarterRadius 4 oldIndex

constructive_injectivity DiskSamples

end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sequence

end
