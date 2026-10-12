module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Geometry.Rational.Box.Bounds
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball
section Ball

/-- Convert an existing rational box to a centre-plus-squared-error sidecar using its fixed lower-left anchor. -/
def ofBox (box : Rational.Box) :
  Ball :=
  { center := box.anchor
    radiusSq := box.diagonalSq
    radiusSq_nonneg := box.diagonalSq_nonneg }

/-- The ball built from a rational box admits every reading admitted by that original box. -/
theorem contains_ofBox {box :
  Rational.Box} {value : Data.Gaussian.Basic.Canonical}
    (inside : box.Contains value) : (ofBox box).Contains value :=
  box.normSq_sub_anchor_le inside
end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
