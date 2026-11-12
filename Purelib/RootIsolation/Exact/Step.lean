module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Region.Complement
public import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.Extraction
public import Purelib.RootIsolation.Exact.State
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.Track.Separation.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed step builder retains the original occurrence certificates.
public import Purelib.Data.List.Membership

open Purelib.Polynomial.Clearance.Box.Region

open Purelib.Polynomial.Winding.Box.Region

open Purelib.Data
open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-!
# Replacing one positive region in the retained partition

The first positive occurrence supplies an extracted track and eight
complementary cells. The original remaining occurrences and support persist.
-/

namespace Purelib.RootIsolation.Exact.Step

set_option genInjectivity false in
/-- Retain one positive-region replacement and its exact numeric changes.

The result refers to the original partition state. Its support is unchanged,
remaining raw winding decreases by four and the track list grows by one. -/
public structure StepResult
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.IsolationState p ambient) where
  /-- The actual state after replacing the selected positive region. -/ next : State.IsolationState p ambient
  /-- The replacement retains the original support box exactly. -/ support_next : next.support = state.support
  /-- The remaining regions' total raw winding is the original total minus four. -/ totalRaw_next :
    Sum.totalRaw next.regions = Sum.totalRaw state.regions - 4
  /-- The replacement adds exactly one track to the original track list. -/ tracks_length_next : next.tracks.length =
    state.tracks.length + 1

constructive_injectivity StepResult

/-- Replace one retained positive-winding region by its exact track and complementary regions.

The finite selection preserves the original support and all separation and coverage certificates; total raw winding
decreases by four while the track count increases by one. -/
@[expose] public def step
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalPositive : 0 < Sum.totalRaw state.regions)
    (request : Option Data.Rat.Fraction.Rational := none) : StepResult state := by
  let selection := Selection.selectPositive state.regions nonnegative totalPositive
  let selected := selection.selected
  let rest := selection.before ++ selection.after
  let extracted := Extraction.extractRegion degreeAtLeastTwo squarefree elimination
    selected selection.positive request
  let complements := Complement.complementRegions extracted.grid
    selected.refinesAmbient
  let regions := complements ++ rest
  let tracks := extracted.track :: state.tracks
  have selectedMember : selected ∈ state.regions := by
    rw [selection.decomposition]
    exact List.mem_append_right _ (List.mem_cons_self)
  have restMember : ∀ {region : Clearance.Box.Region.ClearRegion p ambient},
      region ∈ rest → region ∈ state.regions := by
    intro region member
    rw [selection.decomposition]
    rcases (Data.List.Membership.mem_append).mp member with beforeMember | afterMember
    · exact List.mem_append_left _ beforeMember
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ afterMember)
  have reordered : (selected :: rest).Pairwise Basic.regionInteriorSeparated := by
    have pairwise := state.regionsPairwise
    rw [selection.decomposition] at pairwise
    exact (Data.List.Pairwise.pairwise_middle
      (R := Basic.regionInteriorSeparated)
      (fun {_ _} separated => Basic.regionInteriorSeparated_symm separated)).mp
        pairwise
  have selectedRest : ∀ region ∈ rest,
      Basic.regionInteriorSeparated selected region :=
    (List.pairwise_cons.mp reordered).1
  have restPairwise : rest.Pairwise Basic.regionInteriorSeparated :=
    (List.pairwise_cons.mp reordered).2
  have regionsPairwise : regions.Pairwise Basic.regionInteriorSeparated := by
    apply Data.List.Pairwise.pairwise_append
      (Complement.complementRegions_pairwise extracted.grid selected.refinesAmbient)
      restPairwise
    intro complement complementMember region regionMember
    exact (selectedRest region regionMember).of_refines
      (Complement.complementRegions_refine_outer extracted.grid
        selected.refinesAmbient complementMember)
      (Box.refines_refl region.box)
  have tracksPairwise : tracks.Pairwise Track.Separation.Basic.trackSeparated := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, state.tracksPairwise⟩
    intro oldTrack oldMember
    exact Box.separated_symm
      (state.tracksAvoidRegions oldTrack oldMember selected selectedMember
        extracted.centerStrict)
  have tracksAvoidRegions : ∀ track ∈ tracks, ∀ region ∈ regions,
      ∀ {small : Box}, small.StrictInterior region.box →
        track.initial.box.Separated small := by
    intro track trackMember region regionMember small smallStrict
    rcases (Data.List.Membership.mem_cons).mp trackMember with newTrack | oldTrackMember
    · subst track
      rcases (Data.List.Membership.mem_append).mp regionMember with
        complementMember | restRegionMember
      · exact Complement.center_separated_from_complement_strictInterior
          extracted.grid selected.refinesAmbient complementMember smallStrict
      · exact (selectedRest region restRegionMember).strict_refinements
          extracted.centerStrict smallStrict
    · rcases (Data.List.Membership.mem_append).mp regionMember with
        complementMember | restRegionMember
      · have smallSelected := (Box.Refinement.StrictInterior.Boxes.trans_refines smallStrict)
          (Complement.complementRegions_refine_outer extracted.grid
            selected.refinesAmbient complementMember)
        exact state.tracksAvoidRegions track oldTrackMember selected
          selectedMember smallSelected
      · exact state.tracksAvoidRegions track oldTrackMember region
          (restMember restRegionMember) smallStrict
  have covers : ∀ {z : Gaussian.Basic.Canonical}, state.support.Contains z →
      (∃ track ∈ tracks, track.initial.box.Contains z) ∨
        ∃ region ∈ regions, region.box.Contains z := by
    intro z inside
    rcases state.covers inside with
      ⟨oldTrack, oldTrackMember, trackContains⟩ |
        ⟨oldRegion, oldRegionMember, regionContains⟩
    · exact Or.inl ⟨oldTrack, List.mem_cons_of_mem _ oldTrackMember,
        trackContains⟩
    · rw [selection.decomposition] at oldRegionMember
      rcases (Data.List.Membership.mem_append).mp oldRegionMember with
        beforeMember | selectedOrAfter
      · have oldRest : oldRegion ∈ rest :=
          List.mem_append_left _ beforeMember
        exact Or.inr ⟨oldRegion, List.mem_append_right _ oldRest,
          regionContains⟩
      · rcases (Data.List.Membership.mem_cons).mp selectedOrAfter with equal | afterMember
        · subst oldRegion
          rcases extracted.grid.covers regionContains with
            centerContains | ⟨cell, cellMember, cellContains⟩
          · exact Or.inl ⟨extracted.track, List.mem_cons_self,
              centerContains⟩
          · let region := Complement.cellToRegion cell selected.refinesAmbient
            have complementMember : region ∈ complements := by
              change region ∈ extracted.grid.complements.map (fun cell =>
                Complement.cellToRegion cell selected.refinesAmbient)
              exact Data.List.Map.mem_map.mpr ⟨cell, cellMember, rfl⟩
            exact Or.inr ⟨region,
              List.mem_append_left _ complementMember, cellContains⟩
        · have oldRest : oldRegion ∈ rest :=
            List.mem_append_right _ afterMember
          exact Or.inr ⟨oldRegion, List.mem_append_right _ oldRest,
            regionContains⟩
  let next : State.IsolationState p ambient :=
    { support := state.support
      supportRefinesAmbient := state.supportRefinesAmbient
      regions := regions
      regionsPairwise := regionsPairwise
      tracks := tracks
      tracksPairwise := tracksPairwise
      tracksAvoidRegions := tracksAvoidRegions
      covers := covers }
  have complementTotal : Sum.totalRaw complements =
      Winding.Box.Basic.quadrupledBoxWinding p selected.box - 4 := by
    have identity := Complement.totalRaw_complementRegions extracted.grid
      selected.refinesAmbient
    rw [extracted.track.initial.rawWindingFour] at identity
    exact identity
  have restTotal : Sum.totalRaw rest =
      Sum.totalRaw selection.before + Sum.totalRaw selection.after :=
    Sum.totalRaw_append selection.before selection.after
  have stateTotal : Sum.totalRaw state.regions =
      Sum.totalRaw selection.before + Winding.Box.Basic.quadrupledBoxWinding p selected.box +
        Sum.totalRaw selection.after := by
    calc
      Sum.totalRaw state.regions =
          Sum.totalRaw (selection.before ++ selected :: selection.after) :=
        congrArg (fun values => Sum.totalRaw (p := p) values)
          selection.decomposition
      _ = Sum.totalRaw selection.before +
          Winding.Box.Basic.quadrupledBoxWinding p selected.box +
            Sum.totalRaw selection.after := by
        rw [Sum.totalRaw_append, Sum.totalRaw_cons]
        ring1
  have nextTotal : Sum.totalRaw regions = Sum.totalRaw state.regions - 4 := by
    rw [Sum.totalRaw_append, complementTotal, restTotal, stateTotal]
    ring1
  exact
    { next := next
      support_next := rfl
      totalRaw_next := nextTotal
      tracks_length_next := rfl }

/-- An extraction step preserves the complete Newton origins of its ordered retained track list.

The new head uses its actual checked extraction state. Every previous track
retains the literal original constructor witness supplied for the same tail.
-/
public theorem step_tracks_origin
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalPositive : 0 < Sum.totalRaw state.regions)
    (request : Option Data.Rat.Fraction.Rational)
    (previous : ∀ track ∈ state.tracks, Track.Newton.Build.Origin degreeAtLeastTwo squarefree elimination track) :
    ∀ track ∈ (step degreeAtLeastTwo squarefree elimination state nonnegative totalPositive request).next.tracks,
      Track.Newton.Build.Origin degreeAtLeastTwo squarefree elimination track := by
  let selection := Selection.selectPositive state.regions nonnegative totalPositive
  let extracted := Extraction.extractRegion degreeAtLeastTwo squarefree elimination
    selection.selected selection.positive request
  intro track member
  change track ∈ extracted.track :: state.tracks at member
  cases member with
  | head =>
      exact Extraction.extractRegion_track_origin degreeAtLeastTwo squarefree elimination
        selection.selected selection.positive request
  | tail _ remaining => exact previous track remaining

/-- One original extraction step preserves the exact Newton refiner of every retained track. -/
public theorem step_refine
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalPositive : 0 < Sum.totalRaw state.regions)
    (prior : ∀ track ∈ state.tracks,
      track.refine = Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination)
    (request : Option Data.Rat.Fraction.Rational := none) :
    ∀ track ∈ (step degreeAtLeastTwo squarefree elimination state nonnegative totalPositive request).next.tracks,
      track.refine = Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination := by
  let selection := Selection.selectPositive state.regions nonnegative totalPositive
  intro track member
  change track ∈ (Extraction.extractRegion degreeAtLeastTwo squarefree elimination
    selection.selected selection.positive request).track :: state.tracks at member
  rcases (Data.List.Membership.mem_cons).mp member with equal | oldMember
  · subst track
    exact Extraction.extractRegion_refine degreeAtLeastTwo squarefree elimination
      selection.selected selection.positive request
  · exact prior track oldMember

end Purelib.RootIsolation.Exact.Step
