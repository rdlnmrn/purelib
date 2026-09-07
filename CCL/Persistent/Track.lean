import CCL.Persistent.Progressive
import CCL.Bridge.TrackProcess

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

namespace CCL.PersistentTrack

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open CCL.ProgressiveMachineSemantics

/-- Joint finite state of one higher-degree site. -/
structure State
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) where
  numerical : WindingOneState p ambient
  numericalRefinesInitial : numerical.box.Refines track.initial.box
  cursor : CCL.PersistentProgressive.Cursor
    (CCL.TrackProcess.toProcess track) track.initial

namespace State

/-- Empty-word persistent state at the displayed initial winding box. -/
def initial
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) : State track :=
  { numerical := track.initial
    numericalRefinesInitial := RFAP.Boxes.Box.refines_refl track.initial.box
    cursor := CCL.PersistentProgressive.Cursor.initial
      (CCL.TrackProcess.toProcess track) track.initial }

/-- One joint request.  The numerical box is refined from the previous box;
the already-running cursor appends exactly `count` bits and then contracts its
live projective sidecar below the same displayed `epsilon^2`. -/
def request
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) : State track :=
  let numerical := track.refine current.numerical epsilon positive
  let epsilonSqPositive :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  { numerical := numerical
    numericalRefinesInitial :=
      (track.nested current.numerical epsilon positive).trans
        current.numericalRefinesInitial
    cursor := current.cursor.request (epsilon ^ 2) epsilonSqPositive count }

theorem request_box_refines
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).numerical.box.Refines
      current.numerical.box :=
  track.nested current.numerical epsilon positive

theorem request_box_accurate
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current.numerical epsilon positive

theorem request_word_extends
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) :
    current.cursor.machine.emitted.IsPrefix
      (current.request epsilon positive count).cursor.machine.emitted := by
  exact current.cursor.request_extends (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count

theorem request_word_length
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) :
    (current.request epsilon positive count).cursor.machine.emitted.length =
      current.cursor.machine.emitted.length + count := by
  exact current.cursor.request_length (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count

/-- The same persistent prefix and its quantitative sidecar have the
requested projective diameter after every joint request. -/
theorem request_cylinder_accurate
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) {left right : Gaussian}
    (leftPossible :
      SemanticMode.possible
        (current.request epsilon positive count).cursor.machine.mode left)
    (rightPossible :
      SemanticMode.possible
        (current.request epsilon positive count).cursor.machine.mode right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (current.request epsilon positive count).cursor.machine left)
        (CCL.PersistentProgressive.Machine.image
          (current.request epsilon positive count).cursor.machine right) ≤
      epsilon ^ 2 := by
  exact current.cursor.request_pair_chordalSq_le (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count
      leftPossible rightPossible

/-- Finite site-ownership compatibility: every candidate in the live
projective cylinder reconstructs to a rational point admitted by this track's
displayed initial isolated box.  No completed point is asserted. -/
theorem candidate_in_initial_box
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (state : State track) {tail : Gaussian}
    (possible : SemanticMode.possible state.cursor.machine.mode tail) :
    ∃ value : Gaussian,
      track.initial.box.Contains value ∧
        (CCL.PersistentProgressive.Machine.image
          state.cursor.machine tail).Equivalent (CCL.Proj.affine value) := by
  simpa only [CCL.TrackProcess.toProcess,
    CCL.PersistentProgressive.Machine.image] using
      state.cursor.exact.exact possible

end State

/-- Joint refinement order used by request histories. -/
structure Refines
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (inner outer : State track) : Prop where
  box : inner.numerical.box.Refines outer.numerical.box
  word : outer.cursor.machine.emitted.IsPrefix inner.cursor.machine.emitted

theorem State.request_refines
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    (current : State track) (epsilon : Coordinate) (positive : 0 < epsilon)
    (count : Nat) : Refines (current.request epsilon positive count) current :=
  ⟨current.request_box_refines epsilon positive count,
    current.request_word_extends epsilon positive count⟩

end CCL.PersistentTrack
