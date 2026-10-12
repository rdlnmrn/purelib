module
public import Purelib.Approximation.Gaussian.Representation.Basic

public import Purelib.Approximation.Gaussian.Sequence
import Init.Prelude
import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Sequence

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Representation.Sequence
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

/-- Finite indices of one fast-Cauchy approximation. Later indices refine earlier ones because their explicitly
witnessed tails are smaller. -/
def approximationRepresentation (approximation :
  ApproximationData) :
    Approximation.Gaussian.Representation where
  Observation := Nat
  Possible index value := approximation.Possible index value
  witness index := approximation.sample index
  witness_possible index := approximation.sample_possible index
  Refines inner outer := outer ≤ inner
  refines_refl _ := Nat.le_refl _
  refines_trans innerMiddle middleOuter := middleOuter.trans innerMiddle
  possible_persists refines possible :=
    approximation.possible_persists refines possible
  precisionSq index := approximation.radiusSq index
  precisionSq_nonneg index := approximation.radiusSq_nonneg index
  boundary := .closed
end Purelib.Approximation.Gaussian.Representation.Sequence

end
