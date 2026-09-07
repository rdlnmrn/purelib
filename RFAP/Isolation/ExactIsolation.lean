import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.GlobalNonnegativity

/-!
# Choice-free exact finite isolation

A finite list of clear constructive-rational regions carries an exact raw
winding total.  Each step selects the first positive region, extracts one
strictly interior Newton band of raw winding four, and replaces the region by
the eight clear cells of its complement.  Global nonnegativity makes exactly
`count` such steps possible when the initial raw winding is `4 * count`.
-/

namespace RFAP.ExactIsolation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack
abbrev Grid := RFAP.CentralBandGrid.Grid
abbrev ClearCell := RFAP.CentralBandGrid.ClearCell

open RFAP.Winding
open RFAP.GlobalWinding
open RFAP.CentralBandGrid

/-- One clear region in a fixed finite ambient box. -/
structure ClearRegion (p : GaussianPolynomial) (ambient : Box) where
  box : Box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box

def regionInteriorSeparated
    {p : GaussianPolynomial} {ambient : Box}
    (left right : ClearRegion p ambient) : Prop :=
  left.box.InteriorSeparated right.box

theorem regionInteriorSeparated_symm
    {p : GaussianPolynomial} {ambient : Box}
    {left right : ClearRegion p ambient}
    (separated : regionInteriorSeparated left right) :
    regionInteriorSeparated right left :=
  RFAP.Boxes.Box.interiorSeparated_symm separated

def ClearRegion.raw
    {p : GaussianPolynomial} {ambient : Box}
    (region : ClearRegion p ambient)
    (windingNonzero : quadrupledBoxWinding p region.box ≠ 0) :
    RFAP.RawSubdivision.RawWindingState p ambient where
  box := region.box
  refinesAmbient := region.refinesAmbient
  proper := region.proper
  clearance := region.clearance
  rawWinding_ne := windingNonzero

def cellToRegion
    {p : GaussianPolynomial} {ambient outer center : Box}
    (cell : ClearCell p outer center) (outerRefines : outer.Refines ambient) :
    ClearRegion p ambient where
  box := cell.box
  refinesAmbient := cell.refines.trans outerRefines
  proper := cell.proper
  clearance := cell.clearance

def complementRegions
    {p : GaussianPolynomial} {ambient outer center : Box}
    (grid : Grid p outer center) (outerRefines : outer.Refines ambient) :
    List (ClearRegion p ambient) :=
  grid.complements.map fun cell => cellToRegion cell outerRefines

theorem complementRegions_pairwise
    {p : GaussianPolynomial} {ambient outer center : Box}
    (grid : Grid p outer center) (outerRefines : outer.Refines ambient) :
    (complementRegions grid outerRefines).Pairwise
      regionInteriorSeparated := by
  rw [complementRegions, QuotientFreeList.pairwise_map]
  simpa only [regionInteriorSeparated, cellToRegion] using
    grid.complements_pairwise

theorem complementRegions_refine_outer
    {p : GaussianPolynomial} {ambient outer center : Box}
    (grid : Grid p outer center) (outerRefines : outer.Refines ambient)
    {region : ClearRegion p ambient}
    (member : region ∈ complementRegions grid outerRefines) :
    region.box.Refines outer := by
  rw [complementRegions, QuotientFreeList.mem_map] at member
  rcases member with ⟨cell, _cellMember, rfl⟩
  exact cell.refines

theorem center_separated_from_complement_strictInterior
    {p : GaussianPolynomial} {ambient outer center : Box}
    (grid : Grid p outer center) (outerRefines : outer.Refines ambient)
    {region : ClearRegion p ambient}
    (member : region ∈ complementRegions grid outerRefines)
    {small : Box} (strict : small.StrictInterior region.box) :
    center.Separated small := by
  rw [complementRegions, QuotientFreeList.mem_map] at member
  rcases member with ⟨cell, _cellMember, rfl⟩
  exact cell.center_separated_from_strictInterior strict

/-- Exact sum of raw windings over one finite region list. -/
def totalRaw
    {p : GaussianPolynomial} {ambient : Box}
    (regions : List (ClearRegion p ambient)) : Int :=
  (regions.map fun region => quadrupledBoxWinding p region.box).sum

@[simp] theorem totalRaw_nil
    {p : GaussianPolynomial} {ambient : Box} :
    totalRaw ([] : List (ClearRegion p ambient)) = 0 := rfl

@[simp] theorem totalRaw_cons
    {p : GaussianPolynomial} {ambient : Box}
    (region : ClearRegion p ambient) (regions : List (ClearRegion p ambient)) :
    totalRaw (region :: regions) =
      quadrupledBoxWinding p region.box + totalRaw regions := rfl

theorem totalRaw_append
    {p : GaussianPolynomial} {ambient : Box}
    (left right : List (ClearRegion p ambient)) :
    totalRaw (left ++ right) = totalRaw left + totalRaw right := by
  simp [totalRaw, List.map_append, List.sum_append]

theorem totalRaw_complementRegions
    {p : GaussianPolynomial} {ambient outer center : Box}
    (grid : Grid p outer center) (outerRefines : outer.Refines ambient) :
    totalRaw (complementRegions grid outerRefines) =
      quadrupledBoxWinding p outer - quadrupledBoxWinding p center := by
  have additive := grid.additive
  simp only [complementRegions, Grid.complements, List.map, cellToRegion,
    totalRaw, List.sum_cons, List.sum_nil] at *
  rw [additive]
  ring1

/-- Proof-relevant decomposition at the first positive region. -/
structure PositiveSelection
    {p : GaussianPolynomial} {ambient : Box}
    (regions : List (ClearRegion p ambient)) where
  before : List (ClearRegion p ambient)
  selected : ClearRegion p ambient
  after : List (ClearRegion p ambient)
  decomposition : regions = before ++ selected :: after
  positive : 0 < quadrupledBoxWinding p selected.box

/-- The first positive member is found by finite list recursion. -/
def selectPositive
    {p : GaussianPolynomial} {ambient : Box}
    (regions : List (ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (totalPositive : 0 < totalRaw regions) : PositiveSelection regions := by
  induction regions with
  | nil =>
      simp only [totalRaw_nil] at totalPositive
      exact False.elim (lt_irrefl (0 : Int) totalPositive)
  | cons head tail inductionHypothesis =>
      by_cases headPositive : 0 < quadrupledBoxWinding p head.box
      · exact
          { before := []
            selected := head
            after := tail
            decomposition := rfl
            positive := headPositive }
      · have headNonnegative := nonnegative head (by simp)
        have headZero : quadrupledBoxWinding p head.box = 0 :=
          le_antisymm (le_of_not_gt headPositive) headNonnegative
        have tailPositive : 0 < totalRaw tail := by
          rw [totalRaw_cons, headZero] at totalPositive
          simpa using totalPositive
        have tailNonnegative : ∀ region ∈ tail,
            0 ≤ quadrupledBoxWinding p region.box := by
          intro region member
          exact nonnegative region (by simp [member])
        let selected := inductionHypothesis tailNonnegative tailPositive
        exact
          { before := head :: selected.before
            selected := selected.selected
            after := selected.after
            decomposition := by
              simpa only [List.cons_append] using
                congrArg (fun values => head :: values)
                  selected.decomposition
            positive := selected.positive }

def trackSeparated
    {p : GaussianPolynomial} {ambient : Box}
    (left right : WindingOneTrack p ambient) : Prop :=
  left.initial.box.Separated right.initial.box

theorem trackSeparated_symm
    {p : GaussianPolynomial} {ambient : Box}
    {left right : WindingOneTrack p ambient}
    (separated : trackSeparated left right) : trackSeparated right left :=
  RFAP.Boxes.Box.separated_symm separated

/-- Finite partition state during exact isolation. -/
structure IsolationState (p : GaussianPolynomial) (ambient : Box) where
  support : Box
  supportRefinesAmbient : support.Refines ambient
  regions : List (ClearRegion p ambient)
  regionsPairwise : regions.Pairwise regionInteriorSeparated
  tracks : List (WindingOneTrack p ambient)
  tracksPairwise : tracks.Pairwise trackSeparated
  tracksAvoidRegions : ∀ track ∈ tracks, ∀ region ∈ regions,
    ∀ {small : Box}, small.StrictInterior region.box →
      track.initial.box.Separated small
  covers : ∀ {z : Gaussian}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ regions, region.box.Contains z

def IsolationState.initial
    {p : GaussianPolynomial} {ambient : Box}
    (region : ClearRegion p ambient) : IsolationState p ambient where
  support := region.box
  supportRefinesAmbient := region.refinesAmbient
  regions := [region]
  regionsPairwise := QuotientFreeList.pairwise_singleton _ _
  tracks := []
  tracksPairwise := List.Pairwise.nil
  tracksAvoidRegions := by
    intro track member
    nomatch member
  covers := by
    intro z inside
    exact Or.inr ⟨region, List.mem_cons_self, inside⟩

/-- One selected positive region, its winding-one track, and its exact
eight-cell complement. -/
structure RegionExtraction
    (p : GaussianPolynomial) (ambient : Box)
    (selected : ClearRegion p ambient) where
  track : WindingOneTrack p ambient
  grid : Grid p selected.box track.initial.box
  centerStrict : track.initial.box.StrictInterior selected.box

def extractRegion
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (selected : ClearRegion p ambient)
    (positive : 0 < quadrupledBoxWinding p selected.box) :
    RegionExtraction p ambient selected := by
  let raw := selected.raw (ne_of_gt positive)
  let onePositive : (0 : Coordinate) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
  let extracted := RFAP.NewtonBand.extract degreeAtLeastTwo
    squarefree elimination raw onePositive
  let centerState : WindingOneState p ambient :=
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }
  let track := RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo
    squarefree elimination centerState
  let grid : Grid p selected.box extracted.box :=
    build selected.clearance extracted.proper extracted.strictCurrent
      extracted.leftLineClearance extracted.rightLineClearance
      extracted.bottomLineClearance extracted.topLineClearance
  exact
    { track := track
      grid := by
        simpa only [track, RFAP.ShrinkingTrack.ofInitial,
          centerState] using grid
      centerStrict := by
        simpa only [track, RFAP.ShrinkingTrack.ofInitial,
          centerState, RFAP.NewtonBand.Output.box, raw,
          ClearRegion.raw] using extracted.strictCurrent }

/-- One positive-region replacement and its exact numeric changes. -/
structure StepResult
    {p : GaussianPolynomial} {ambient : Box}
    (state : IsolationState p ambient) where
  next : IsolationState p ambient
  support_next : next.support = state.support
  totalRaw_next : totalRaw next.regions = totalRaw state.regions - 4
  tracks_length_next : next.tracks.length = state.tracks.length + 1

def step
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (totalPositive : 0 < totalRaw state.regions) : StepResult state := by
  let selection := selectPositive state.regions nonnegative totalPositive
  let selected := selection.selected
  let rest := selection.before ++ selection.after
  let extracted := extractRegion degreeAtLeastTwo squarefree elimination
    selected selection.positive
  let complements := complementRegions extracted.grid
    selected.refinesAmbient
  let regions := complements ++ rest
  let tracks := extracted.track :: state.tracks
  have selectedMember : selected ∈ state.regions := by
    rw [selection.decomposition]
    exact List.mem_append_right _ (List.mem_cons_self)
  have restMember : ∀ {region : ClearRegion p ambient},
      region ∈ rest → region ∈ state.regions := by
    intro region member
    rw [selection.decomposition]
    rcases List.mem_append.mp member with beforeMember | afterMember
    · exact List.mem_append_left _ beforeMember
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ afterMember)
  have reordered : (selected :: rest).Pairwise regionInteriorSeparated := by
    have pairwise := state.regionsPairwise
    rw [selection.decomposition] at pairwise
    exact (QuotientFreeList.pairwise_middle
      (R := regionInteriorSeparated)
      (fun {_ _} separated => regionInteriorSeparated_symm separated)).mp
        pairwise
  have selectedRest : ∀ region ∈ rest,
      regionInteriorSeparated selected region :=
    (List.pairwise_cons.mp reordered).1
  have restPairwise : rest.Pairwise regionInteriorSeparated :=
    (List.pairwise_cons.mp reordered).2
  have regionsPairwise : regions.Pairwise regionInteriorSeparated := by
    apply QuotientFreeList.pairwise_append
      (complementRegions_pairwise extracted.grid selected.refinesAmbient)
      restPairwise
    intro complement complementMember region regionMember
    exact (selectedRest region regionMember).of_refines
      (complementRegions_refine_outer extracted.grid
        selected.refinesAmbient complementMember)
      (RFAP.Boxes.Box.refines_refl region.box)
  have tracksPairwise : tracks.Pairwise trackSeparated := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, state.tracksPairwise⟩
    intro oldTrack oldMember
    exact RFAP.Boxes.Box.separated_symm
      (state.tracksAvoidRegions oldTrack oldMember selected selectedMember
        extracted.centerStrict)
  have tracksAvoidRegions : ∀ track ∈ tracks, ∀ region ∈ regions,
      ∀ {small : Box}, small.StrictInterior region.box →
        track.initial.box.Separated small := by
    intro track trackMember region regionMember small smallStrict
    rcases List.mem_cons.mp trackMember with newTrack | oldTrackMember
    · subst track
      rcases List.mem_append.mp regionMember with
        complementMember | restRegionMember
      · exact center_separated_from_complement_strictInterior
          extracted.grid selected.refinesAmbient complementMember smallStrict
      · exact (selectedRest region restRegionMember).strict_refinements
          extracted.centerStrict smallStrict
    · rcases List.mem_append.mp regionMember with
        complementMember | restRegionMember
      · have smallSelected := smallStrict.trans_refines
          (complementRegions_refine_outer extracted.grid
            selected.refinesAmbient complementMember)
        exact state.tracksAvoidRegions track oldTrackMember selected
          selectedMember smallSelected
      · exact state.tracksAvoidRegions track oldTrackMember region
          (restMember restRegionMember) smallStrict
  have covers : ∀ {z : Gaussian}, state.support.Contains z →
      (∃ track ∈ tracks, track.initial.box.Contains z) ∨
        ∃ region ∈ regions, region.box.Contains z := by
    intro z inside
    rcases state.covers inside with
      ⟨oldTrack, oldTrackMember, trackContains⟩ |
        ⟨oldRegion, oldRegionMember, regionContains⟩
    · exact Or.inl ⟨oldTrack, List.mem_cons_of_mem _ oldTrackMember,
        trackContains⟩
    · rw [selection.decomposition] at oldRegionMember
      rcases List.mem_append.mp oldRegionMember with
        beforeMember | selectedOrAfter
      · have oldRest : oldRegion ∈ rest :=
          List.mem_append_left _ beforeMember
        exact Or.inr ⟨oldRegion, List.mem_append_right _ oldRest,
          regionContains⟩
      · rcases List.mem_cons.mp selectedOrAfter with equal | afterMember
        · subst oldRegion
          rcases extracted.grid.covers regionContains with
            centerContains | ⟨cell, cellMember, cellContains⟩
          · exact Or.inl ⟨extracted.track, List.mem_cons_self,
              centerContains⟩
          · let region := cellToRegion cell selected.refinesAmbient
            have complementMember : region ∈ complements := by
              dsimp only [region, complements]
              rw [complementRegions, QuotientFreeList.mem_map]
              exact ⟨cell, cellMember, rfl⟩
            exact Or.inr ⟨region,
              List.mem_append_left _ complementMember, cellContains⟩
        · have oldRest : oldRegion ∈ rest :=
            List.mem_append_right _ afterMember
          exact Or.inr ⟨oldRegion, List.mem_append_right _ oldRest,
            regionContains⟩
  let next : IsolationState p ambient :=
    { support := state.support
      supportRefinesAmbient := state.supportRefinesAmbient
      regions := regions
      regionsPairwise := regionsPairwise
      tracks := tracks
      tracksPairwise := tracksPairwise
      tracksAvoidRegions := tracksAvoidRegions
      covers := covers }
  have complementTotal : totalRaw complements =
      quadrupledBoxWinding p selected.box - 4 := by
    have identity := totalRaw_complementRegions extracted.grid
      selected.refinesAmbient
    rw [extracted.track.initial.rawWindingFour] at identity
    exact identity
  have restTotal : totalRaw rest =
      totalRaw selection.before + totalRaw selection.after :=
    totalRaw_append selection.before selection.after
  have stateTotal : totalRaw state.regions =
      totalRaw selection.before + quadrupledBoxWinding p selected.box +
        totalRaw selection.after := by
    calc
      totalRaw state.regions =
          totalRaw (selection.before ++ selected :: selection.after) :=
        congrArg (fun values => totalRaw (p := p) values)
          selection.decomposition
      _ = totalRaw selection.before +
          quadrupledBoxWinding p selected.box +
            totalRaw selection.after := by
        rw [totalRaw_append, totalRaw_cons]
        ring1
  have nextTotal : totalRaw regions = totalRaw state.regions - 4 := by
    rw [totalRaw_append, complementTotal, restTotal, stateTotal]
    ring1
  exact
    { next := next
      support_next := rfl
      totalRaw_next := nextTotal
      tracks_length_next := rfl }

structure RunResult
    {p : GaussianPolynomial} {ambient : Box}
    (initial : IsolationState p ambient) (steps : Nat) where
  final : IsolationState p ambient
  support_final : final.support = initial.support
  totalRaw_final : totalRaw final.regions = 0
  tracks_length_final : final.tracks.length = initial.tracks.length + steps

/-- Recursion on the exact displayed remaining winding count. -/
def run
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    (steps : Nat) → (state : IsolationState p ambient) →
      totalRaw state.regions = (4 : Int) * steps → RunResult state steps
  | 0, state, total =>
      { final := state
        support_final := rfl
        totalRaw_final := by simpa using total
        tracks_length_final := by simp }
  | steps + 1, state, total => by
      have positive : 0 < totalRaw state.regions := by
        rw [total]
        exact Int.mul_pos (by decide)
          (Int.ofNat_lt.mpr (Nat.zero_lt_succ steps))
      have nonnegative : ∀ region ∈ state.regions,
          0 ≤ quadrupledBoxWinding p region.box := by
        intro region _member
        exact RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
          degreeAtLeastTwo squarefree elimination region.refinesAmbient
            region.proper region.clearance
      let first := step degreeAtLeastTwo squarefree elimination state
        nonnegative positive
      have nextTotal : totalRaw first.next.regions = (4 : Int) * steps := by
        rw [first.totalRaw_next, total, Nat.cast_succ]
        ring1
      let tail := run degreeAtLeastTwo squarefree elimination steps first.next
        nextTotal
      exact
        { final := tail.final
          support_final := tail.support_final.trans first.support_next
          totalRaw_final := tail.totalRaw_final
          tracks_length_final := by
            rw [tail.tracks_length_final, first.tracks_length_next]
            ring1 }

theorem totalRaw_nonnegative
    {p : GaussianPolynomial} {ambient : Box}
    (regions : List (ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box) :
    0 ≤ totalRaw regions := by
  induction regions with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [totalRaw_cons]
      apply add_nonneg (nonnegative head (by simp))
      exact inductionHypothesis fun region member =>
        nonnegative region (by simp [member])

theorem rawWinding_eq_zero_of_mem_totalRaw_eq_zero
    {p : GaussianPolynomial} {ambient : Box}
    (regions : List (ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (totalZero : totalRaw regions = 0)
    {region : ClearRegion p ambient} (member : region ∈ regions) :
    quadrupledBoxWinding p region.box = 0 := by
  induction regions with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      have headNonnegative := nonnegative head (by simp)
      have tailMembers : ∀ value ∈ tail,
          0 ≤ quadrupledBoxWinding p value.box := by
        intro value valueMember
        exact nonnegative value (by simp [valueMember])
      have tailNonnegative := totalRaw_nonnegative tail tailMembers
      rw [totalRaw_cons] at totalZero
      have headLeTotal : quadrupledBoxWinding p head.box ≤
          quadrupledBoxWinding p head.box + totalRaw tail := by
        have shifted := Int.add_le_add_left tailNonnegative
          (quadrupledBoxWinding p head.box)
        simpa only [add_zero] using shifted
      have headZero : quadrupledBoxWinding p head.box = 0 :=
        Int.le_antisymm (headLeTotal.trans_eq totalZero) headNonnegative
      have tailLeTotal : totalRaw tail ≤
          quadrupledBoxWinding p head.box + totalRaw tail := by
        have shifted := Int.add_le_add_right headNonnegative (totalRaw tail)
        simpa only [zero_add] using shifted
      have tailZero : totalRaw tail = 0 :=
        Int.le_antisymm (tailLeTotal.trans_eq totalZero) tailNonnegative
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact headZero
      · exact inductionHypothesis tailMembers tailZero tailMember

/-- Exact degree-many isolation result, retaining the finite zero-winding
remainder partition used by the maximality proof. -/
structure Output
    (p : GaussianPolynomial) (ambient : Box) (count : Nat) where
  support : Box
  support_refinesAmbient : support.Refines ambient
  tracks : List (WindingOneTrack p ambient)
  tracks_length : tracks.length = count
  tracks_pairwise : tracks.Pairwise trackSeparated
  remainder : List (ClearRegion p ambient)
  remainder_pairwise : remainder.Pairwise regionInteriorSeparated
  remainder_rawWinding_zero : ∀ region ∈ remainder,
    quadrupledBoxWinding p region.box = 0
  tracks_avoid_remainder : ∀ track ∈ tracks, ∀ region ∈ remainder,
    ∀ {small : Box}, small.StrictInterior region.box →
      track.initial.box.Separated small
  partition_covers : ∀ {z : Gaussian}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ remainder, region.box.Contains z

def Output.trackIndex
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (index : Fin count) :
    Fin output.tracks.length :=
  Fin.cast output.tracks_length.symm index

def Output.trackAt
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (index : Fin count) :
    WindingOneTrack p ambient :=
  output.tracks.get (output.trackIndex index)

@[simp] theorem Output.trackIndex_val
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (index : Fin count) :
    (output.trackIndex index).val = index.val := rfl

private theorem pairwise_get_of_val_lt
    {α : Type} {relation : α → α → Prop} {values : List α}
    (pairwise : values.Pairwise relation)
    (left right : Fin values.length) (ordered : left.val < right.val) :
    relation (values.get left) (values.get right) := by
  have direct := QuotientFreeList.pairwise_getElem pairwise left.val right.val
    left.isLt right.isLt ordered
  exact direct

theorem Output.trackAt_pairwiseSeparated
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (left right : Fin count)
    (different : left ≠ right) :
    (output.trackAt left).initial.box.Separated
      (output.trackAt right).initial.box := by
  have indexDifferent : output.trackIndex left ≠ output.trackIndex right :=
    fun equal => different (Fin.ext (by
      calc
        left.val = (output.trackIndex left).val :=
          (output.trackIndex_val left).symm
        _ = (output.trackIndex right).val := congrArg Fin.val equal
        _ = right.val := output.trackIndex_val right))
  by_cases ordered : (output.trackIndex left).val <
      (output.trackIndex right).val
  · exact pairwise_get_of_val_lt output.tracks_pairwise _ _ ordered
  · have reversed : (output.trackIndex right).val <
        (output.trackIndex left).val := by
      have unequalValues : (output.trackIndex left).val ≠
          (output.trackIndex right).val := by
        intro equal
        exact indexDifferent (Fin.ext equal)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered)
        (Ne.symm unequalValues)
    exact RFAP.Boxes.Box.separated_symm
      (pairwise_get_of_val_lt output.tracks_pairwise _ _ reversed)

/-- Exact isolation from any clear initial region with raw winding
`4 * count`. -/
def isolateFromRegion
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (initial : ClearRegion p ambient) (count : Nat)
    (raw : quadrupledBoxWinding p initial.box = (4 : Int) * count) :
    Output p ambient count := by
  let state := IsolationState.initial initial
  have total : totalRaw state.regions = (4 : Int) * count := by
    change quadrupledBoxWinding p initial.box + 0 = (4 : Int) * count
    rw [raw, add_zero]
  let result := run degreeAtLeastTwo squarefree elimination count state total
  have nonnegative : ∀ region ∈ result.final.regions,
      0 ≤ quadrupledBoxWinding p region.box := by
    intro region _member
    exact RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination region.refinesAmbient
        region.proper region.clearance
  exact
    { support := initial.box
      support_refinesAmbient := initial.refinesAmbient
      tracks := result.final.tracks
      tracks_length := by
        rw [result.tracks_length_final]
        simp [state, IsolationState.initial]
      tracks_pairwise := result.final.tracksPairwise
      remainder := result.final.regions
      remainder_pairwise := result.final.regionsPairwise
      remainder_rawWinding_zero := by
        intro region member
        exact rawWinding_eq_zero_of_mem_totalRaw_eq_zero
          result.final.regions nonnegative result.totalRaw_final member
      tracks_avoid_remainder := result.final.tracksAvoidRegions
      partition_covers := by
        intro z inside
        apply result.final.covers
        rw [result.support_final]
        exact inside }

/-- Exact isolation on the coefficient-computed constructive large square. -/
def isolateLargeSquare
    {p : GaussianPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    Output p (largeSquareBox p) p.natDegree := by
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  let initial : ClearRegion p (largeSquareBox p) :=
    { box := largeSquareBox p
      refinesAmbient := RFAP.Boxes.Box.refines_refl
        (largeSquareBox p)
      proper := largeSquareBox_proper p
      clearance := largeSquare_boundaryClearance degreePositive }
  have raw : quadrupledBoxWinding p initial.box =
      (4 : Int) * p.natDegree := by
    simpa only [initial] using
      quadrupledBoxWinding_largeSquare_eq_degree degreePositive
  exact isolateFromRegion degreeAtLeastTwo squarefree elimination initial
    p.natDegree raw

end RFAP.ExactIsolation
