module

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
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : Exact.State.IsolationState p ambient) where
  /-- The actual state after replacing the selected positive region. -/ next : Exact.State.IsolationState p ambient
  /-- The replacement retains the original support box exactly. -/ support_next : next.support = state.support
  /-- The remaining regions' total raw winding is the original total minus four. -/ totalRaw_next :
    Winding.Box.Region.Sum.totalRaw next.regions = Winding.Box.Region.Sum.totalRaw state.regions - 4
  /-- The replacement adds exactly one track to the original track list. -/ tracks_length_next : next.tracks.length =
    state.tracks.length + 1

constructive_injectivity StepResult

/-- Replace one retained positive-winding region by its exact track and complementary regions.

The finite selection preserves the original support and all separation and coverage certificates; total raw winding
decreases by four while the track count increases by one. -/
@[expose] public def step
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : Exact.State.IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalPositive : 0 < Winding.Box.Region.Sum.totalRaw state.regions) : Exact.Step.StepResult state := by
  let selection := Winding.Box.Region.Selection.selectPositive state.regions nonnegative totalPositive
  let selected := selection.selected
  let rest := selection.before ++ selection.after
  let extracted := Exact.Extraction.extractRegion degreeAtLeastTwo squarefree elimination
    selected selection.positive
  let complements := Winding.Box.Region.Complement.complementRegions extracted.grid
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
  have reordered : (selected :: rest).Pairwise Clearance.Box.Region.Basic.regionInteriorSeparated := by
    have pairwise := state.regionsPairwise
    rw [selection.decomposition] at pairwise
    exact (Data.List.Pairwise.pairwise_middle
      (R := Clearance.Box.Region.Basic.regionInteriorSeparated)
      (fun {_ _} separated => Clearance.Box.Region.Basic.regionInteriorSeparated_symm separated)).mp
        pairwise
  have selectedRest : ∀ region ∈ rest,
      Clearance.Box.Region.Basic.regionInteriorSeparated selected region :=
    (List.pairwise_cons.mp reordered).1
  have restPairwise : rest.Pairwise Clearance.Box.Region.Basic.regionInteriorSeparated :=
    (List.pairwise_cons.mp reordered).2
  have regionsPairwise : regions.Pairwise Clearance.Box.Region.Basic.regionInteriorSeparated := by
    apply Data.List.Pairwise.pairwise_append
      (Winding.Box.Region.Complement.complementRegions_pairwise extracted.grid selected.refinesAmbient)
      restPairwise
    intro complement complementMember region regionMember
    exact (selectedRest region regionMember).of_refines
      (Winding.Box.Region.Complement.complementRegions_refine_outer extracted.grid
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
      · exact Winding.Box.Region.Complement.center_separated_from_complement_strictInterior
          extracted.grid selected.refinesAmbient complementMember smallStrict
      · exact (selectedRest region restRegionMember).strict_refinements
          extracted.centerStrict smallStrict
    · rcases (Data.List.Membership.mem_append).mp regionMember with
        complementMember | restRegionMember
      · have smallSelected := (Box.Refinement.StrictInterior.Boxes.trans_refines smallStrict)
          (Winding.Box.Region.Complement.complementRegions_refine_outer extracted.grid
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
          · let region := Winding.Box.Region.Complement.cellToRegion cell selected.refinesAmbient
            have complementMember : region ∈ complements := by
              change region ∈ extracted.grid.complements.map (fun cell =>
                Winding.Box.Region.Complement.cellToRegion cell selected.refinesAmbient)
              exact Data.List.Map.mem_map.mpr ⟨cell, cellMember, rfl⟩
            exact Or.inr ⟨region,
              List.mem_append_left _ complementMember, cellContains⟩
        · have oldRest : oldRegion ∈ rest :=
            List.mem_append_right _ afterMember
          exact Or.inr ⟨oldRegion, List.mem_append_right _ oldRest,
            regionContains⟩
  let next : Exact.State.IsolationState p ambient :=
    { support := state.support
      supportRefinesAmbient := state.supportRefinesAmbient
      regions := regions
      regionsPairwise := regionsPairwise
      tracks := tracks
      tracksPairwise := tracksPairwise
      tracksAvoidRegions := tracksAvoidRegions
      covers := covers }
  have complementTotal : Winding.Box.Region.Sum.totalRaw complements =
      Winding.Box.Basic.quadrupledBoxWinding p selected.box - 4 := by
    have identity := Winding.Box.Region.Complement.totalRaw_complementRegions extracted.grid
      selected.refinesAmbient
    rw [extracted.track.initial.rawWindingFour] at identity
    exact identity
  have restTotal : Winding.Box.Region.Sum.totalRaw rest =
      Winding.Box.Region.Sum.totalRaw selection.before + Winding.Box.Region.Sum.totalRaw selection.after :=
    Winding.Box.Region.Sum.totalRaw_append selection.before selection.after
  have stateTotal : Winding.Box.Region.Sum.totalRaw state.regions =
      Winding.Box.Region.Sum.totalRaw selection.before + Winding.Box.Basic.quadrupledBoxWinding p selected.box +
        Winding.Box.Region.Sum.totalRaw selection.after := by
    calc
      Winding.Box.Region.Sum.totalRaw state.regions =
          Winding.Box.Region.Sum.totalRaw (selection.before ++ selected :: selection.after) :=
        congrArg (fun values => Winding.Box.Region.Sum.totalRaw (p := p) values)
          selection.decomposition
      _ = Winding.Box.Region.Sum.totalRaw selection.before +
          Winding.Box.Basic.quadrupledBoxWinding p selected.box +
            Winding.Box.Region.Sum.totalRaw selection.after := by
        rw [Winding.Box.Region.Sum.totalRaw_append, Winding.Box.Region.Sum.totalRaw_cons]
        ring1
  have nextTotal : Winding.Box.Region.Sum.totalRaw regions = Winding.Box.Region.Sum.totalRaw state.regions - 4 := by
    rw [Winding.Box.Region.Sum.totalRaw_append, complementTotal, restTotal, stateTotal]
    ring1
  exact
    { next := next
      support_next := rfl
      totalRaw_next := nextTotal
      tracks_length_next := rfl }

end Purelib.RootIsolation.Exact.Step
