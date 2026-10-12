module
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Approximation.Gaussian.Representation.Basic
public import Purelib.Approximation.Gaussian.Translation.Observation
public import Purelib.Data.CCL.Name.Boxed.Refinement

public import Purelib.Approximation.Gaussian.Representation.Ball
import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.Translation

open Purelib.Data.CCL.Name.Boxed

open Purelib.Data.CCL.Name.Boxed.Basic

open Purelib.Data.CCL.Name.Boxed.Refinement

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Translation.CCL.BoxedPrefix
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

/-- A boxed raw CCL prefix retains both its ordinary syntax and its finite nonzero enclosure sidecar. -/
def boxedPrefixRepresentation :
  Approximation.Gaussian.Representation where
  Observation := Certificate
  Possible certificate value := certificate.Possible value
  witness certificate := certificate.witness
  witness_possible certificate :=
    ⟨certificate.witness_nonzero, certificate.witness_represented⟩
  Refines inner outer := Refinement.Refines inner outer
  refines_refl := Refines.refl
  refines_trans innerMiddle middleOuter := innerMiddle.trans middleOuter
  possible_persists refines possible := refines.possible_persists possible
  precisionSq certificate := certificate.box.diagonalSq
  precisionSq_nonneg certificate := certificate.box.diagonalSq_nonneg
  boundary := .projective

open Purelib.Data.Rat in
/-- The direct boxed-prefix-to-ball observation map. It does not claim a reverse conversion of an arbitrary isolated
ball into one raw prefix. -/
def boxedPrefixToBall :
    Observation.ObservationMap boxedPrefixRepresentation
      Ball.ballRepresentation where
  map certificate := Approximation.Gaussian.Enclosure.Ball.ofBox certificate.box
  covers possible :=
    Approximation.Gaussian.Enclosure.Ball.contains_ofBox
      (Certificate.possible_inside possible)
  coherent := by
    intro inner outer refines
    refine ⟨inner.box.anchor, ?_, ?_⟩
    · exact Approximation.Gaussian.Enclosure.Ball.contains_ofBox
        inner.box.contains_anchor
    · exact Approximation.Gaussian.Enclosure.Ball.contains_ofBox
        (refines.box.contains inner.box.contains_anchor)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by
    simp only [boxedPrefixRepresentation, Ball.ballRepresentation,
      Approximation.Gaussian.Enclosure.Ball.ofBox, add_zero, -eq_self, -iff_self]
    exact Fraction.Order.Basic.le_refl _
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1
end Purelib.Approximation.Gaussian.Translation.CCL.BoxedPrefix

end
