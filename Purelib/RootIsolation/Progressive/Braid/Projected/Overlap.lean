module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Bijection.Transposition
public import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
public import Purelib.Topology.Knot.Braid.Event
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Topology.Knot.Braid (CrossingSign Generator)

section

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Certified projected crossings of finite root paths

An Artin generator acts on the left-to-right positions of a chosen planar
projection, whereas finite monodromy transports the persistent owner indices
of root boxes.  Those numberings need not coincide.  This file records their
finite relabelling explicitly and folds atomic projected chamber overlaps into
an executable braid word.

A crossing chart contains only rational root boxes, a signed adjacent
generator, an exact owner-matching law, and a strict height separation of the
two crossing strands.  It is therefore finite certificate data: no completed
root track or configuration space is introduced.  The extraction theorem
proves that evaluating the resulting word gives exactly the chamber-path
transport, expressed in the endpoint projection orders.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected.Overlap

/-- Rational geometry distinguishing the over/under choice at one adjacent
projection crossing.  In a positive chart the strand which starts in the
left position lies strictly below the other strand throughout their two
Rouché bridge boxes; a negative chart records the reverse height order.

Together with the adjacent endpoint swap stored by `ProjectedOverlap`, this
is finite signed-crossing data rather than an arbitrary sign annotation. -/
structure CrossingGeometry {strands : Nat}
    (start finish : ProjectedFrame strands)
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands) where
  /-- The two original bridge boxes have the strict vertical order specified by the retained crossing sign. -/
    heightSeparated :
    match generator.sign with
    | .positive =>
        (overlap.bridge (start.ownerIndex generator.left)).box.yUpper <
          (overlap.bridge (start.ownerIndex generator.right)).box.yLower
    | .negative =>
        (overlap.bridge (start.ownerIndex generator.right)).box.yUpper <
          (overlap.bridge (start.ownerIndex generator.left)).box.yLower

set_option genInjectivity false in
/-- One certified atomic overlap in projection order.  The matching equation
is the decisive link: it states that persistent owner transport is either the
identity on projection positions or exactly the displayed adjacent swap. -/
inductive ProjectedOverlap {strands : Nat}
    (start finish : ProjectedFrame strands) : Type 2
  /-- An original chamber overlap whose matching preserves every projected position. -/ | stationary
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex position)
  /-- An original chamber overlap whose matching is the displayed adjacent swap, with its retained signed height
    geometry. -/ | crossing
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (generator : Generator strands)
      (geometry : CrossingGeometry start finish overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex (generator.permutation.forward position))

constructive_injectivity ProjectedOverlap

namespace ProjectedOverlap

/-- Read the original chamber overlap retained by a projected step. -/
def chamberOverlap {strands : Nat} {start finish : ProjectedFrame strands} :
    Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish →
      ChamberOverlap start.chamber finish.chamber
  | .stationary overlap _ => overlap
  | .crossing overlap _ _ _ => overlap

/-- Read the stationary event or signed adjacent crossing retained by this projected overlap. -/
def event {strands : Nat} {start finish : ProjectedFrame strands} :
    Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish → Topology.Knot.Braid.Event strands
  | .stationary _ _ => .stationary
  | .crossing _ generator _ _ => .crossing generator

/-- Read the finite braid word of the original projected event. -/
def word {strands : Nat} {start finish : ProjectedFrame strands}
    (step : Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish) : Topology.Knot.Braid.Word strands :=
  step.event.word

/-- The original chamber-owner matching agrees with the retained projected event permutation. -/
theorem matching_order {strands : Nat}
    {start finish : ProjectedFrame strands}
    (step : Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish) (position : Fin strands) :
    step.chamberOverlap.matching.forward (start.ownerIndex position) =
      finish.ownerIndex (step.event.permutation.forward position) := by
  cases step with
  | stationary overlap law => exact law position
  | crossing overlap generator geometry law => exact law position

/-- The inverse crossing matching sends the finishing left position to the original right owner. -/
theorem crossing_backward_left {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    overlap.matching.backward (finish.ownerIndex generator.left) =
      start.ownerIndex generator.right := by
  have matched := congrArg overlap.matching.backward (law generator.right)
  rw [Generator.permutation, Data.Fin.Bijection.Transposition.transposition_forward,
    Data.Fin.Bijection.Transposition.swapIndices_right,
    overlap.matching.backward_forward] at matched
  exact matched.symm

/-- The inverse crossing matching sends the finishing right position to the original left owner. -/
theorem crossing_backward_right {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    overlap.matching.backward (finish.ownerIndex generator.right) =
      start.ownerIndex generator.left := by
  have matched := congrArg overlap.matching.backward (law generator.left)
  rw [Generator.permutation, Data.Fin.Bijection.Transposition.transposition_forward,
    Data.Fin.Bijection.Transposition.swapIndices_left,
    overlap.matching.backward_forward] at matched
  exact matched.symm

/-- Reverse the retained crossing geometry using the original inverse matching and opposite crossing sign. -/
theorem reverseCrossingGeometry {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (geometry : Progressive.Braid.Projected.Overlap.CrossingGeometry start finish overlap generator)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    Progressive.Braid.Projected.Overlap.CrossingGeometry finish start overlap.reverse generator.reverse := by
  constructor
  have backwardLeft := Progressive.Braid.Projected.Overlap.ProjectedOverlap.crossing_backward_left overlap generator law
  have backwardRight := Progressive.Braid.Projected.Overlap.ProjectedOverlap.crossing_backward_right overlap generator
    law
  cases generator with
  | mk index sign =>
      cases sign with
      | positive =>
          change
            (overlap.bridge
              (overlap.matching.backward
                (finish.ownerIndex
                  ({ index := index, sign := CrossingSign.positive } :
                    Generator strands).right))).box.yUpper <
              (overlap.bridge
                (overlap.matching.backward
                  (finish.ownerIndex
                    ({ index := index, sign := CrossingSign.positive } :
                      Generator strands).left))).box.yLower
          rw [backwardRight, backwardLeft]
          exact geometry.heightSeparated
      | negative =>
          change
            (overlap.bridge
              (overlap.matching.backward
                (finish.ownerIndex
                  ({ index := index, sign := CrossingSign.negative } :
                    Generator strands).left))).box.yUpper <
              (overlap.bridge
                (overlap.matching.backward
                  (finish.ownerIndex
                    ({ index := index, sign := CrossingSign.negative } :
                      Generator strands).right))).box.yLower
          rw [backwardLeft, backwardRight]
          exact geometry.heightSeparated

/-- Reverse a projected overlap, preserving its original common-owner bridges and reversing its crossing sign. -/
def reverse {strands : Nat} {start finish : ProjectedFrame strands} :
    Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish →
      Progressive.Braid.Projected.Overlap.ProjectedOverlap finish start
  | .stationary overlap law =>
      .stationary overlap.reverse (by
        intro position
        have matched := congrArg overlap.matching.backward (law position)
        rw [overlap.matching.backward_forward] at matched
        exact matched.symm)
  | .crossing overlap generator geometry law =>
      .crossing overlap.reverse generator.reverse
        (Progressive.Braid.Projected.Overlap.ProjectedOverlap.reverseCrossingGeometry overlap generator geometry law)
          (by
          intro position
          have matched := congrArg overlap.matching.backward
            (law (generator.permutation.forward position))
          rw [Generator.permutation_involutive,
            overlap.matching.backward_forward] at matched
          exact matched.symm)

/-- Reversing a projected overlap gives the inverse of its original braid word. -/
@[simp] theorem reverse_word {strands
  : Nat}
    {start finish : ProjectedFrame strands}
    (step : Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish) :
    step.reverse.word = step.word.inverse := by
  cases step with
  | stationary overlap law => rfl
  | crossing overlap generator geometry law => rfl

/-- Reversing a projected step retains the reversal of its exact original chamber overlap. -/
@[simp] theorem reverse_chamberOverlap
  {strands : Nat}
    {start finish : ProjectedFrame strands}
    (step : Progressive.Braid.Projected.Overlap.ProjectedOverlap start finish) :
    step.reverse.chamberOverlap = step.chamberOverlap.reverse := by
  cases step with
  | stationary overlap law => rfl
  | crossing overlap generator geometry law => rfl

end ProjectedOverlap

end Purelib.RootIsolation.Progressive.Braid.Projected.Overlap

end

end
