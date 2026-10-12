module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
public import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Separation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Mathlib.Algebra.GroupWithZero.Nat

public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.State.WindingOne.Family.Basic

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

set_option genInjectivity false in
/-- An explicitly finite family of numerical winding-one states.

The retained state list has pairwise positively separated boxes inside the
original ambient box; its winding certificates remain attached to those states. -/
structure WindingFamily (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient :
  Box) where
  /-- The actual finite list of retained winding-one states. -/ states : List (State.WindingOne.Basic.WindingOneState p
    ambient)
  /-- Distinct list occurrences have positively separated original state boxes. -/ pairwise : states.Pairwise fun left
    right =>
    left.box.Separated right.box

constructive_injectivity WindingFamily

namespace WindingFamily

/-- Read the aligned box list of a winding family.

Mapping the retained states preserves their order and reads each original
box without reconstructing a numerical state or its winding certificate. -/
@[expose] def boxes {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : List Box :=
  family.states.map fun state => state.box

/-- Reading the retained owner boxes preserves the original state-list length. -/
@[simp] theorem boxes_length
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) :
    family.boxes.length = family.states.length := by
  exact Data.List.Map.length_map (fun state => state.box) family.states

/-- The boxes of the original retained states are pairwise separated.

The map certificate specializes the original state-pair relation to their
boxes, retaining the same ordered list occurrences and separation witnesses. -/
theorem boxes_pairwise
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) :
    family.boxes.Pairwise fun left right => left.Separated right := by
  exact Data.List.Pairwise.pairwise_map.mpr family.pairwise

/-- Read the original state aligned with a bounded box-list index.

The mapped-list length transports the original index bound to the retained
state list. The natural coordinate and selected state remain unchanged. -/
@[expose] def stateAtBoxIndex
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) : State.WindingOne.Basic.WindingOneState p ambient :=
  family.states.get
    ⟨index.val, family.boxes_length ▸ index.isLt⟩

/-- Reading a box index selects the box of its exact retained original state.

Both list reads use the same natural coordinate. The mapped-list certificate
transports only the bound needed to read the original state. -/
theorem boxAt_eq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.boxes.get index = (family.stateAtBoxIndex index).box := by
  exact Data.List.Map.getElem_map (fun state => state.box) family.states index.val
    (family.boxes_length ▸ index.isLt) index.isLt

/-- Every indexed retained box refines the original ambient box. -/
theorem boxAt_refinesAmbient
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    (family.boxes.get index).Refines ambient := by
  rw [family.boxAt_eq index]
  exact (family.stateAtBoxIndex index).refinesAmbient

/-- One winding state as the complete local owner family for a controller
step on that track. -/
@[expose] def singleton
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient) : State.WindingOne.Family.Basic.WindingFamily p ambient
      :=
  { states := [state]
    pairwise := Data.List.Pairwise.pairwise_singleton _ _ }

/-- The singleton winding family retains exactly the original state's box. -/
@[simp] theorem singleton_boxes
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient) :
    (State.WindingOne.Family.Basic.WindingFamily.singleton state).boxes = [state.box] := rfl

/-- The unique box index of the singleton retained winding family. -/
@[expose] def singletonIndex
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient) :
    Fin (State.WindingOne.Family.Basic.WindingFamily.singleton state).boxes.length :=
  ⟨0, Nat.zero_lt_succ 0⟩

/-- Reading the singleton family at its unique index returns the original state. -/
@[simp] theorem singleton_stateAtBoxIndex
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.WindingOne.Basic.WindingOneState p ambient) :
    (State.WindingOne.Family.Basic.WindingFamily.singleton state).stateAtBoxIndex
      (State.WindingOne.Family.Basic.WindingFamily.singletonIndex state) = state := rfl

/-- The initial states of pairwise-separated tracks form a winding family.

The builder maps the original track list in order and transports its supplied
separation certificate to the retained initial states and their original boxes. -/
@[expose] def ofTracks
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (tracks : List (Track.Basic.WindingOneTrack p ambient))
    (pairwise : tracks.Pairwise
      Track.Separation.Basic.trackSeparated) :
    State.WindingOne.Family.Basic.WindingFamily p ambient :=
  { states := tracks.map fun track => track.initial
    pairwise := by
      change tracks.Pairwise (fun left right =>
        left.initial.box.Separated right.initial.box) at pairwise
      exact Data.List.Pairwise.pairwise_map.mpr pairwise }

/-- The exact-isolation output supplies its complete initial winding family. -/
@[expose] def ofIsolation
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) :
    State.WindingOne.Family.Basic.WindingFamily p ambient :=
  State.WindingOne.Family.Basic.WindingFamily.ofTracks output.tracks output.tracks_pairwise

end WindingFamily

end Purelib.RootIsolation.State.WindingOne.Family.Basic
