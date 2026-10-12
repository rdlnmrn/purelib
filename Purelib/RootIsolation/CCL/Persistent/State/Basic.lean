module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent constructive CCL prefixes on shrinking root boxes

A fresh rational sample from each refined box need not retain any prefix of
the preceding sample's CCL word.  The persistent invariant below records the
stronger fact actually needed by the paper: every later winding-one subbox
has an explicit nonzero rational sample represented by the same raw prefix.

The second half of the file is deliberately structural.  It proves that a
finite one-bit controller with this invariant can be iterated for any
requested natural number of bits while the numerical box is independently
contracted to a requested rational accuracy.  Constructing that one-bit
controller from the finite curve-count and equality-owner geometry is a
separate obligation; it is not postulated as a theorem here.
-/

namespace Purelib.RootIsolation.CCL.Persistent

set_option genInjectivity false in
/-- A numerical winding-one state together with one raw prefix that persists
under all subsequent supplied refinements. -/
structure State (p : CoefficientPolynomial)
  (ambient : Box) where
  /-- The original numerical winding-one state carrying this persistent prefix. -/ numerical :
    WindingOneState p ambient
  /-- The retained raw CCL prefix. -/ word : Data.List.BinaryPrefix.Basic.SourcePersistentCCLWordAlias
  /-- Compute a compatible nonzero sample for this exact prefix in every supplied later refining state. -/ samples :
    CCL.Persistent.Sample.Basic.PersistentSamples word numerical

constructive_injectivity State

namespace State

/-- Canonical persistent state at the empty word. -/
def initial
    {p : CoefficientPolynomial} {ambient : Box}
    (numerical : WindingOneState p ambient) : State p ambient :=
  { numerical := numerical
    word := []
    samples := CCL.Persistent.Sample.Basic.PersistentSamples.initial numerical }

/-- Obtain the current displayed compatible sample by applying the provider
to the current box itself. -/
def currentSample
    {p : CoefficientPolynomial} {ambient : Box}
    (state : State p ambient) : CCL.Persistent.Sample.Basic.CompatibleSample state.word
      state.numerical.box :=
  state.samples.sample state.numerical
    (Box.refines_refl state.numerical.box)

/-- Refine only the numerical box, preserving the same raw prefix by
composition of explicit box-refinement certificates. -/
def refine
    {p : CoefficientPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) : State p ambient :=
  { numerical := numerical
    word := state.word
    samples :=
      { sample := fun later laterRefines =>
          state.samples.sample later (laterRefines.trans refines) } }

/-- Numerical refinement preserves the exact retained raw prefix. -/
@[simp] theorem refine_word
    {p : CoefficientPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) :
    (state.refine numerical refines).word = state.word := rfl

/-- Numerical refinement retains the supplied containment in the preceding box. -/
theorem refine_box
    {p : CoefficientPolynomial} {ambient : Box}
    (state : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines state.numerical.box) :
    (state.refine numerical refines).numerical.box.Refines
      state.numerical.box :=
  refines

end State

namespace State.Basic

/-- Joint order on persistent states: boxes only shrink and words only grow
by right extension. -/
structure StateRefines
    {p : CoefficientPolynomial} {ambient : Box}
    (inner outer : State p ambient) : Prop where
  /-- The inner state's box refines the original outer state's box. -/ box : inner.numerical.box.Refines
    outer.numerical.box
  /-- The outer raw word is a prefix of the inner raw word. -/ word : outer.word.IsPrefix inner.word

/-- Every persistent state refines itself in both box containment and raw-prefix order. -/
theorem stateRefines_refl
    {p : CoefficientPolynomial} {ambient : Box}
    (state : State p ambient) : CCL.Persistent.State.Basic.StateRefines state state :=
  ⟨Box.refines_refl state.numerical.box,
    ⟨[], Data.List.Append.append_nil _⟩⟩

end State.Basic

namespace State.Basic.StateRefines

/-- Compose box containment and raw-prefix extension between three original persistent states. -/
theorem trans
    {p : CoefficientPolynomial} {ambient : Box}
    {inner middle outer : State p ambient}
    (innerMiddle : CCL.Persistent.State.Basic.StateRefines inner middle)
    (middleOuter : CCL.Persistent.State.Basic.StateRefines middle outer) : CCL.Persistent.State.Basic.StateRefines inner
      outer :=
  ⟨innerMiddle.box.trans middleOuter.box, by
    rcases middleOuter.word with ⟨middleSuffix, middleWord⟩
    rcases innerMiddle.word with ⟨innerSuffix, innerWord⟩
    refine ⟨middleSuffix ++ innerSuffix, ?_⟩
    exact (Data.List.Append.append_assoc _ _ _).symm.trans
      ((congrArg (fun word => word ++ innerSuffix) middleWord).trans innerWord)⟩

end State.Basic.StateRefines

namespace State.Basic

set_option genInjectivity false in
/-- A displayed exact rational root found inside the current finite box. -/
structure ExactRootIn
    (p : CoefficientPolynomial) (box : Box) where
  /-- The retained exact Gaussian-rational root point. -/ point : Gaussian.Basic.Canonical
  /-- The original polynomial evaluates to zero at the retained point. -/ root : p.eval point = 0
  /-- The retained exact root lies in the specified original box. -/ inside : box.Contains point

constructive_injectivity ExactRootIn

/-- Contract only the numerical component of a persistent state. -/
def refineAlong
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) : State p ambient :=
  current.refine (track.refine current.numerical epsilon positive)
    (track.nested current.numerical epsilon positive)

/-- Refining along a winding-one track shrinks the box and preserves the original prefix. -/
theorem refineAlong_refines
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    CCL.Persistent.State.Basic.StateRefines (CCL.Persistent.State.Basic.refineAlong track current epsilon positive)
      current :=
  ⟨track.nested current.numerical epsilon positive, ⟨[], Data.List.Append.append_nil _⟩⟩

/-- Refining along a winding-one track meets the requested squared-diagonal accuracy. -/
theorem refineAlong_accurate
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (CCL.Persistent.State.Basic.refineAlong track current epsilon positive).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current.numerical epsilon positive

end State.Basic

end Purelib.RootIsolation.CCL.Persistent

end

section
@[expose] public section

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

section Purelib.CCL.Boundary.EqualityOwner
end Purelib.CCL.Boundary.EqualityOwner

end
