module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Geometry.Rational.Box.Refinement

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Geometry.Rational.Box.Bounds

open Purelib.Approximation

open Purelib.Geometry

open Purelib.Geometry.Rational (Box)

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Representation.Box
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

/-- Closed axis-aligned rational boxes, measured from their fixed lower-left anchor by the squared diagonal. -/
def boxRepresentation :
  Approximation.Gaussian.Representation where
  Observation := Box
  Possible box value := box.Contains value
  witness box := box.anchor
  witness_possible box := box.contains_anchor
  Refines inner outer := inner.Refines outer
  refines_refl := Rational.Box.refines_refl
  refines_trans innerMiddle middleOuter := innerMiddle.trans middleOuter
  possible_persists refines possible := refines.contains possible
  precisionSq box := box.diagonalSq
  precisionSq_nonneg box := box.diagonalSq_nonneg
  boundary := .closed
end Purelib.Approximation.Gaussian.Representation.Box

end
