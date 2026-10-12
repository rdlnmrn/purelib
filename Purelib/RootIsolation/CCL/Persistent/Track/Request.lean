module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Track.Basic
import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.CCL.Transducer (Mode)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Persistent.Track.Basic (State)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent CCL observations of one Paper-I winding track

This is the finite request object shared by the box and CCL sides.  Its
numerical component follows one Paper-I winding-one track, so returned boxes
are nested and meet every requested rational diagonal bound.  Its CCL
component is one running redundant arithmetic cursor: later requests append
to the same exposed raw word and refine its quantitative projective cylinder
without restarting the cursor.

Both components retain the same explicit track index and initial isolated
box.  Exact cursor semantics places every admitted projective candidate in
that initial site box.  This is finite site ownership, not an assertion that
an unnamed completed root has been selected.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Track
namespace Basic.State

/-- One joint request.  The numerical box is refined from the previous box;
the already-running cursor appends exactly `count` bits and then contracts its
live projective sidecar below the same displayed `epsilon^2`. -/
def request
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) : State track :=
  let numerical := track.refine current.numerical epsilon positive
  let epsilonSqPositive :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  { numerical := numerical
    numericalRefinesInitial :=
      (track.nested current.numerical epsilon positive).trans
        current.numericalRefinesInitial
    cursor := current.cursor.request (epsilon ^ 2) epsilonSqPositive count }

/-- A joint persistent request refines the original numerical box. -/
theorem request_box_refines
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).numerical.box.Refines
      current.numerical.box :=
  track.nested current.numerical epsilon positive

/-- A joint persistent request meets its original squared-diagonal budget. -/
theorem request_box_accurate
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current.numerical epsilon positive

/-- A joint request extends the existing emitted raw prefix. -/
theorem request_word_extends
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) :
    current.cursor.machine.emitted.IsPrefix
      (current.request epsilon positive count).cursor.machine.emitted := by
  exact current.cursor.request_extends (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count

/-- A joint request appends exactly the specified number of raw bits. -/
theorem request_word_length
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).cursor.machine.emitted.length =
      current.cursor.machine.emitted.length + count := by
  exact current.cursor.request_length (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count

/-- The same persistent prefix and its quantitative sidecar have the
requested projective diameter after every joint request. -/
theorem request_cylinder_accurate
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) {left right : Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (current.request epsilon positive count).cursor.machine.mode left)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (current.request epsilon positive count).cursor.machine.mode right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (current.request epsilon positive count).cursor.machine left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (current.request epsilon positive count).cursor.machine right) ≤
      epsilon ^ 2 := by
  exact current.cursor.request_pair_chordalSq_le (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count
      leftPossible rightPossible

/-- Finite site-ownership compatibility: every candidate in the live
projective cylinder reconstructs to a rational point admitted by this track's
displayed initial isolated box.  No completed point is asserted. -/
theorem candidate_in_initial_box
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (state : State track) {tail : Canonical}
    (possible : Mode.Semantics.SemanticMode.possible state.cursor.machine.mode tail) :
    ∃ value : Canonical,
      track.initial.box.Contains value ∧
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          state.cursor.machine tail).Equivalent (Geometry.Projective.Line.Proj.affine value) := by
  simpa only [Track.Approximation.Process.toProcess,
    Data.CCL.Progressive.Cursor.Image.Machine.image] using
      state.cursor.exact.exact possible

end Basic.State

/-- Joint refinement order used by request histories. -/
structure Request.Refines
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (inner outer : State track) : Prop where
  /-- The inner state's numerical box refines the original outer box. -/ box : inner.numerical.box.Refines
    outer.numerical.box
  /-- The original outer emitted word is a prefix of the inner emitted word. -/ word :
    outer.cursor.machine.emitted.IsPrefix inner.cursor.machine.emitted

/-- A joint request refines both the original numerical box and emitted prefix. -/
theorem Basic.State.request_refines
    {p : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (count : Nat) : Request.Refines (current.request epsilon positive count) current :=
  ⟨current.request_box_refines epsilon positive count,
    current.request_word_extends epsilon positive count⟩

end Purelib.RootIsolation.CCL.Persistent.Track

end
