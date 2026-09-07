import FTA.GlobalNonnegativity
import FTA.GlobalWinding

/-!
# Exact finite isolation of degree-many tracks

This module implements Theorem 9.2.  A finite list of clear rectangular
regions carries exact raw total winding.  At each positive-total stage the
first positive region is replaced by the eight clear complement cells of an
extracted winding-one band.  Global nonnegativity makes the total decrease
from `4(n+1)` to `4n`, and finite recursion therefore returns exactly the
degree-many pairwise separated tracks and a zero-winding remainder.
-/

namespace FTA.ExactIsolation

open scoped BigOperators

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.BoxClearance
open FTA.CentralBandGrid
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.ConstructiveTrack
open FTA.GlobalNonnegativity
open FTA.GlobalWinding
open FTA.LocalExtraction
open FTA.PathClearance
open FTA.RawLocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootTrackSeparation
open FTA.Winding
open FTA.WindingHomotopy

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI
abbrev RatPolynomial := FTA.ComputablePolynomial.DensePolynomial ℚ
abbrev RatInterval := FTA.SturmTransducer.RationalInterval

/-- Executable upper bound for the squared norm of the dominant coordinate
pair on one rational edge interval. -/
def dominantNormMajorant
    (A B : RatPolynomial) (interval : RatInterval) : ℚ :=
  let radius := intervalMagnitude interval.lower interval.upper
  max 1 (denseEvalAbsBound A radius ^ 2 + denseEvalAbsBound B radius ^ 2)

theorem dominantNormMajorant_pos
    (A B : RatPolynomial) (interval : RatInterval) :
    0 < dominantNormMajorant A B interval :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem dominant_eval_norm_le_majorant
    (A B : RatPolynomial) (interval : RatInterval)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper) :
    A.eval t ^ 2 + B.eval t ^ 2 ≤ dominantNormMajorant A B interval := by
  let radius := intervalMagnitude interval.lower interval.upper
  have hradius : 0 ≤ radius := (intervalMagnitude_pos _ _).le
  have ht : |t| ≤ radius := abs_le_intervalMagnitude hLower hUpper
  have hA := abs_dense_eval_le_denseEvalAbsBound A hradius ht
  have hB := abs_dense_eval_le_denseEvalAbsBound B hradius ht
  have hASq : A.eval t ^ 2 ≤ denseEvalAbsBound A radius ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (A.eval t)) hA 2
    simpa only [sq_abs] using this
  have hBSq : B.eval t ^ 2 ≤ denseEvalAbsBound B radius ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (B.eval t)) hB 2
    simpa only [sq_abs] using this
  exact (add_le_add hASq hBSq).trans (le_max_right _ _)

/-- A norm-dominance edge certificate supplies an explicit positive lower
bound for the squared norm of the sum `F+G`. -/
def sumClearanceOfDominance
    {A B C D : RatPolynomial} {interval : RatInterval}
    (certificate : NormDominanceCertificate A B C D interval) :
    Certificate (A + C) (B + D) interval := by
  let M := dominantNormMajorant A B interval
  let halfMargin := certificate.margin / 2
  exact
    { bound := halfMargin ^ 2 / M
      positive := div_pos (sq_pos_of_pos
        (div_pos certificate.positive (by norm_num)))
        (dominantNormMajorant_pos A B interval)
      lower := by
        intro t hLower hUpper
        let sumNorm := (A.eval t + C.eval t) ^ 2 +
          (B.eval t + D.eval t) ^ 2
        let realPair := A.eval t * (A.eval t + C.eval t) +
          B.eval t * (B.eval t + D.eval t)
        have hdominance := certificate.lower t hLower hUpper
        have hsumNonneg : 0 ≤ sumNorm := by
          dsimp only [sumNorm]
          positivity
        have hreal : halfMargin ≤ realPair := by
          dsimp only [halfMargin, realPair]
          nlinarith
        have hhalfPositive : 0 < halfMargin :=
          div_pos certificate.positive (by norm_num)
        have hrealSq : halfMargin ^ 2 ≤ realPair ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hreal)
            (by linarith : 0 ≤ realPair + halfMargin)]
        have hcauchy : realPair ^ 2 ≤
            (A.eval t ^ 2 + B.eval t ^ 2) * sumNorm := by
          dsimp only [realPair, sumNorm]
          nlinarith [sq_nonneg
            (A.eval t * (B.eval t + D.eval t) -
              B.eval t * (A.eval t + C.eval t))]
        have hmajorant := dominant_eval_norm_le_majorant
          A B interval hLower hUpper
        have hscaled :
            (A.eval t ^ 2 + B.eval t ^ 2) * sumNorm ≤ M * sumNorm :=
          mul_le_mul_of_nonneg_right hmajorant hsumNonneg
        apply (div_le_iff₀ (dominantNormMajorant_pos A B interval)).2
        calc
          halfMargin ^ 2 ≤ realPair ^ 2 := hrealSq
          _ ≤ (A.eval t ^ 2 + B.eval t ^ 2) * sumNorm := hcauchy
          _ ≤ dominantNormMajorant A B interval * sumNorm := hscaled
          _ = ((A + C).eval t ^ 2 + (B + D).eval t ^ 2) *
              dominantNormMajorant A B interval := by
            simp only [eval_add]
            dsimp only [sumNorm]
            ring }

def horizontalLineClearanceOfDominance
    (p dominant remainder : GaussianPolynomial) (B : CCL.RatBox) (y : ℚ)
    (certificate : NormDominanceCertificate
      (horizontalRealCoordinate dominant y)
      (horizontalImagCoordinate dominant y)
      (horizontalRealCoordinate remainder y)
      (horizontalImagCoordinate remainder y)
      ⟨B.xLower, B.xUpper⟩)
    (hsplit : ∀ z : QI, (dominant + remainder).eval z = p.eval z) :
    HorizontalLineClearance p B y := by
  let clearance := sumClearanceOfDominance certificate
  exact
    { bound := clearance.bound
      positive := clearance.positive
      lower := by
        intro x hLower hUpper
        have h := clearance.lower x hLower hUpper
        calc
          clearance.bound ≤
              ((horizontalRealCoordinate dominant y +
                horizontalRealCoordinate remainder y).eval x) ^ 2 +
              ((horizontalImagCoordinate dominant y +
                horizontalImagCoordinate remainder y).eval x) ^ 2 := h
          _ = normSq (p.eval (CCL.GaussianRat.mk x y)) := by
            simp only [eval_add, horizontalRealCoordinate_eval,
              horizontalImagCoordinate_eval]
            change normSq
              (dominant.eval (CCL.GaussianRat.mk x y) +
                remainder.eval (CCL.GaussianRat.mk x y)) = _
            rw [← eval_add, hsplit] }

def verticalLineClearanceOfDominance
    (p dominant remainder : GaussianPolynomial) (B : CCL.RatBox) (x : ℚ)
    (certificate : NormDominanceCertificate
      (verticalRealCoordinate dominant x)
      (verticalImagCoordinate dominant x)
      (verticalRealCoordinate remainder x)
      (verticalImagCoordinate remainder x)
      ⟨B.yLower, B.yUpper⟩)
    (hsplit : ∀ z : QI, (dominant + remainder).eval z = p.eval z) :
    VerticalLineClearance p B x := by
  let clearance := sumClearanceOfDominance certificate
  exact
    { bound := clearance.bound
      positive := clearance.positive
      lower := by
        intro y hLower hUpper
        have h := clearance.lower y hLower hUpper
        calc
          clearance.bound ≤
              ((verticalRealCoordinate dominant x +
                verticalRealCoordinate remainder x).eval y) ^ 2 +
              ((verticalImagCoordinate dominant x +
                verticalImagCoordinate remainder x).eval y) ^ 2 := h
          _ = normSq (p.eval (CCL.GaussianRat.mk x y)) := by
            simp only [eval_add, verticalRealCoordinate_eval,
              verticalImagCoordinate_eval]
            change normSq
              (dominant.eval (CCL.GaussianRat.mk x y) +
                remainder.eval (CCL.GaussianRat.mk x y)) = _
            rw [← eval_add, hsplit] }

/-- Coefficient-computed positive clearance on the complete boundary of the
Section 6 large square. -/
def largeSquareBoundaryClearance
    {p : GaussianPolynomial} (hdegree : 0 < p.natDegree) :
    BoxBoundaryClearanceCertificate p (largeSquareBox p) := by
  let bottom := horizontalLineClearanceOfDominance p
    (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
    (largeSquareBox p).yLower
    (largeSquareBottomDominanceCertificate hdegree)
    (leadingMonomial_add_lowerTermsPolynomial_eval p)
  let top := horizontalLineClearanceOfDominance p
    (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
    (largeSquareBox p).yUpper
    (largeSquareTopDominanceCertificate hdegree)
    (leadingMonomial_add_lowerTermsPolynomial_eval p)
  let left := verticalLineClearanceOfDominance p
    (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
    (largeSquareBox p).xLower
    (largeSquareLeftDominanceCertificate hdegree)
    (leadingMonomial_add_lowerTermsPolynomial_eval p)
  let right := verticalLineClearanceOfDominance p
    (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
    (largeSquareBox p).xUpper
    (largeSquareRightDominanceCertificate hdegree)
    (leadingMonomial_add_lowerTermsPolynomial_eval p)
  exact boundaryOfLines left right bottom top

/-- One clear region in the fixed global ambient square. -/
structure ClearRegion
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  box : CCL.RatBox
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoxBoundaryClearanceCertificate p box

def regionInteriorSeparated
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (left right : ClearRegion p ambient) : Prop :=
  InteriorSeparated left.box right.box

theorem regionInteriorSeparated_symm
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {left right : ClearRegion p ambient}
    (h : regionInteriorSeparated left right) :
    regionInteriorSeparated right left := interiorSeparated_symm h

def cellToRegion
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (cell : ClearCell p outer center) (houter : outer.Refines ambient) :
    ClearRegion p ambient where
  box := cell.box
  refinesAmbient := cell.refines.trans houter
  proper := cell.proper
  clearance := cell.clearance

def complementRegions
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (grid : Grid p outer center) (houter : outer.Refines ambient) :
    List (ClearRegion p ambient) :=
  grid.complements.map fun cell => cellToRegion cell houter

theorem complementRegions_pairwise
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (grid : Grid p outer center) (houter : outer.Refines ambient) :
    (complementRegions grid houter).Pairwise regionInteriorSeparated := by
  rw [complementRegions, List.pairwise_map]
  simpa only [regionInteriorSeparated, cellToRegion] using
    grid.complements_pairwise

theorem complementRegions_refine_outer
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (grid : Grid p outer center) (houter : outer.Refines ambient)
    {region : ClearRegion p ambient}
    (hregion : region ∈ complementRegions grid houter) :
    region.box.Refines outer := by
  rw [complementRegions, List.mem_map] at hregion
  rcases hregion with ⟨cell, hcell, rfl⟩
  exact cell.refines

theorem center_separated_from_complement_strictInterior
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (grid : Grid p outer center) (houter : outer.Refines ambient)
    {region : ClearRegion p ambient}
    (hregion : region ∈ complementRegions grid houter)
    {small : CCL.RatBox} (hsmall : StrictInterior small region.box) :
    center.Separated small := by
  rw [complementRegions, List.mem_map] at hregion
  rcases hregion with ⟨cell, hcell, rfl⟩
  exact cell.center_separated_from_strictInterior hsmall

/-- Exact sum of raw windings of a finite region list. -/
def totalRaw
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (regions : List (ClearRegion p ambient)) : ℤ :=
  (regions.map fun region => quadrupledBoxWinding p region.box).sum

@[simp] theorem totalRaw_nil
    {p : GaussianPolynomial} {ambient : CCL.RatBox} :
    totalRaw ([] : List (ClearRegion p ambient)) = 0 := rfl

@[simp] theorem totalRaw_cons
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (region : ClearRegion p ambient) (regions : List (ClearRegion p ambient)) :
    totalRaw (region :: regions) =
      quadrupledBoxWinding p region.box + totalRaw regions := rfl

theorem totalRaw_append
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (left right : List (ClearRegion p ambient)) :
    totalRaw (left ++ right) = totalRaw left + totalRaw right := by
  simp [totalRaw, List.map_append, List.sum_append]

theorem totalRaw_complementRegions
    {p : GaussianPolynomial} {ambient outer center : CCL.RatBox}
    (grid : Grid p outer center) (houter : outer.Refines ambient) :
    totalRaw (complementRegions grid houter) =
      quadrupledBoxWinding p outer - quadrupledBoxWinding p center := by
  have hadditive := grid.additive
  simp only [complementRegions, Grid.complements, List.map,
    cellToRegion, totalRaw, List.sum_cons, List.sum_nil] at *
  omega

/-- Proof-relevant decomposition selecting the first positive raw-winding
region from a positive finite total. -/
structure PositiveSelection
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (regions : List (ClearRegion p ambient)) where
  before : List (ClearRegion p ambient)
  selected : ClearRegion p ambient
  after : List (ClearRegion p ambient)
  decomposition : regions = before ++ selected :: after
  positive : 0 < quadrupledBoxWinding p selected.box

/-- The first positive region is found by an ordinary finite list recursion.
The nonnegativity premise is supplied by Theorem 9.1. -/
def selectPositive
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (regions : List (ClearRegion p ambient))
    (hnonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (htotal : 0 < totalRaw regions) : PositiveSelection regions := by
  induction regions with
  | nil => simp only [totalRaw_nil] at htotal; omega
  | cons head tail ih =>
      by_cases hhead : 0 < quadrupledBoxWinding p head.box
      · exact
          { before := []
            selected := head
            after := tail
            decomposition := rfl
            positive := hhead }
      · have hheadNonnegative := hnonnegative head (by simp)
        have hheadZero : quadrupledBoxWinding p head.box = 0 := by omega
        have htailTotal : 0 < totalRaw tail := by
          rw [totalRaw_cons, hheadZero] at htotal
          simpa using htotal
        have htailNonnegative : ∀ region ∈ tail,
            0 ≤ quadrupledBoxWinding p region.box := by
          intro region hmem
          exact hnonnegative region (by simp [hmem])
        let choice := ih htailNonnegative htailTotal
        exact
          { before := head :: choice.before
            selected := choice.selected
            after := choice.after
            decomposition := by
              simpa only [List.cons_append] using
                congrArg (fun xs => head :: xs) choice.decomposition
            positive := choice.positive }

def trackSeparated
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (left right : WindingOneTrack p ambient) : Prop :=
  left.initial.box.Separated right.initial.box

theorem trackSeparated_symm
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    {left right : WindingOneTrack p ambient}
    (h : trackSeparated left right) : trackSeparated right left :=
  CCL.RatBox.separated_symm h

/-- Finite isolation state: pairwise interior-disjoint clear regions, already
extracted pairwise separated tracks, and the invariant that every old track
avoids the strict interior of every remaining region. -/
structure IsolationState
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  support : CCL.RatBox
  supportRefinesAmbient : support.Refines ambient
  regions : List (ClearRegion p ambient)
  regionsPairwise : regions.Pairwise regionInteriorSeparated
  tracks : List (WindingOneTrack p ambient)
  tracksPairwise : tracks.Pairwise trackSeparated
  tracksAvoidRegions : ∀ track ∈ tracks, ∀ region ∈ regions,
    ∀ {small : CCL.RatBox}, StrictInterior small region.box →
      track.initial.box.Separated small
  covers : ∀ {z : QI}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ regions, region.box.Contains z

def IsolationState.initial
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (region : ClearRegion p ambient) : IsolationState p ambient where
  support := region.box
  supportRefinesAmbient := region.refinesAmbient
  regions := [region]
  regionsPairwise := by simp
  tracks := []
  tracksPairwise := by simp
  tracksAvoidRegions := by simp
  covers := by
    intro z hz
    exact Or.inr ⟨region, by simp, hz⟩

/-- Local extraction of one selected positive region, including the exact
eight-cell grid around the new track. -/
structure RegionExtraction
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (selected : ClearRegion p ambient) where
  track : WindingOneTrack p ambient
  grid : Grid p selected.box track.initial.box
  centerStrict : StrictInterior track.initial.box selected.box

def extractRegion
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (selected : ClearRegion p ambient)
    (hpositive : 0 < quadrupledBoxWinding p selected.box) :
    RegionExtraction p ambient selected := by
  let extracted := RawLocalExtraction.extract squarefree selected.clearance
    selected.proper (ne_of_gt hpositive) (by norm_num : (0 : ℚ) < 1)
    elimination
  let center := extracted.band.band.box
  let centerState : WindingOneState p ambient :=
    { box := center
      refinesAmbient := extracted.band.refines.trans selected.refinesAmbient
      proper := extracted.band.band.proper extracted.band.radius_positive
      rawWindingFour := extracted.band.raw_winding_four
      clearance := extracted.band.boundaryClearance
      ambientLeftClearance := extracted.band.leftLineClearanceIn ambient
      ambientRightClearance := extracted.band.rightLineClearanceIn ambient
      ambientBottomClearance := extracted.band.bottomLineClearanceIn ambient
      ambientTopClearance := extracted.band.topLineClearanceIn ambient }
  let track := ConstructiveTrack.ofInitial squarefree elimination centerState
  let interior : StrictInterior center selected.box :=
    { left := extracted.band_strictly_inside.1
      right := extracted.band_strictly_inside.2.1
      bottom := extracted.band_strictly_inside.2.2.1
      top := extracted.band_strictly_inside.2.2.2 }
  let grid : Grid p selected.box center := build selected.clearance
    centerState.proper interior
    extracted.band.leftLineClearance extracted.band.rightLineClearance
    extracted.band.bottomLineClearance extracted.band.topLineClearance
  exact
    { track := track
      grid := by simpa only [track, ConstructiveTrack.ofInitial, centerState] using grid
      centerStrict := by
        simpa only [track, ConstructiveTrack.ofInitial, centerState] using interior }

/-- One positive-region replacement together with the exact changes in raw
total and extracted-track count. -/
structure StepResult
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (state : IsolationState p ambient) where
  next : IsolationState p ambient
  support_next : next.support = state.support
  totalRaw_next : totalRaw next.regions = totalRaw state.regions - 4
  tracks_length_next : next.tracks.length = state.tracks.length + 1

def step
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : IsolationState p ambient)
    (hnonnegative : ∀ region ∈ state.regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (htotal : 0 < totalRaw state.regions) : StepResult state := by
  let selection := selectPositive state.regions hnonnegative htotal
  let selected := selection.selected
  let rest := selection.before ++ selection.after
  let extracted := extractRegion squarefree elimination selected selection.positive
  let complements := complementRegions extracted.grid selected.refinesAmbient
  let regions := complements ++ rest
  let tracks := extracted.track :: state.tracks
  have hselectedMem : selected ∈ state.regions := by
    rw [selection.decomposition]
    exact List.mem_append_right _ (List.mem_cons_self)
  have hrestMem : ∀ {region : ClearRegion p ambient},
      region ∈ rest → region ∈ state.regions := by
    intro region hregion
    rw [selection.decomposition]
    rcases List.mem_append.mp hregion with hbefore | hafter
    · exact List.mem_append_left _ hbefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hafter)
  have hreordered : (selected :: rest).Pairwise regionInteriorSeparated := by
    have hpairwise := state.regionsPairwise
    rw [selection.decomposition] at hpairwise
    exact (List.pairwise_middle
      (R := regionInteriorSeparated)
      (fun {_ _} h => regionInteriorSeparated_symm h)).mp hpairwise
  have hselectedRest : ∀ region ∈ rest,
      regionInteriorSeparated selected region :=
    (List.pairwise_cons.mp hreordered).1
  have hrestPairwise : rest.Pairwise regionInteriorSeparated :=
    (List.pairwise_cons.mp hreordered).2
  have hregionsPairwise : regions.Pairwise regionInteriorSeparated := by
    apply List.pairwise_append.mpr
    refine ⟨complementRegions_pairwise extracted.grid selected.refinesAmbient,
      hrestPairwise, ?_⟩
    intro complement hcomplement region hregion smallComplement smallRegion
      hsmallComplement hsmallRegion
    have hsmallSelected := strictInterior_trans_refines hsmallComplement
      (complementRegions_refine_outer extracted.grid
        selected.refinesAmbient hcomplement)
    exact hselectedRest region hregion hsmallSelected hsmallRegion
  have htracksPairwise : tracks.Pairwise trackSeparated := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, state.tracksPairwise⟩
    intro oldTrack holdTrack
    exact CCL.RatBox.separated_symm
      (state.tracksAvoidRegions oldTrack holdTrack selected hselectedMem
        extracted.centerStrict)
  have htracksAvoidRegions : ∀ track ∈ tracks, ∀ region ∈ regions,
      ∀ {small : CCL.RatBox}, StrictInterior small region.box →
        track.initial.box.Separated small := by
    intro track htrack region hregion small hsmall
    rcases List.mem_cons.mp htrack with hnew | hold
    · subst track
      rcases List.mem_append.mp hregion with hcomplement | hrest
      · exact center_separated_from_complement_strictInterior
          extracted.grid selected.refinesAmbient hcomplement hsmall
      · exact hselectedRest region hrest extracted.centerStrict hsmall
    · rcases List.mem_append.mp hregion with hcomplement | hrest
      · have hsmallSelected := strictInterior_trans_refines hsmall
          (complementRegions_refine_outer extracted.grid
            selected.refinesAmbient hcomplement)
        exact state.tracksAvoidRegions track hold selected hselectedMem
          hsmallSelected
      · exact state.tracksAvoidRegions track hold region (hrestMem hrest) hsmall
  have hcovers : ∀ {z : QI}, state.support.Contains z →
      (∃ track ∈ tracks, track.initial.box.Contains z) ∨
        ∃ region ∈ regions, region.box.Contains z := by
    intro z hz
    rcases state.covers hz with
      ⟨oldTrack, holdTrack, hcontains⟩ |
        ⟨oldRegion, holdRegion, hcontains⟩
    · exact Or.inl ⟨oldTrack, List.mem_cons_of_mem _ holdTrack, hcontains⟩
    · by_cases hselected : oldRegion = selected
      · subst oldRegion
        rcases extracted.grid.covers hcontains with
          hcenter | ⟨cell, hcell, hcellContains⟩
        · exact Or.inl ⟨extracted.track, List.mem_cons_self, hcenter⟩
        · have hcellComplement :
              cellToRegion cell selected.refinesAmbient ∈ complements := by
            dsimp only [complements]
            rw [complementRegions, List.mem_map]
            exact ⟨cell, by simpa only [Grid.complements] using hcell, rfl⟩
          exact Or.inr ⟨cellToRegion cell selected.refinesAmbient,
            List.mem_append_left _ hcellComplement, hcellContains⟩
      · have holdRest : oldRegion ∈ rest := by
          rw [selection.decomposition] at holdRegion
          rcases List.mem_append.mp holdRegion with hbefore | hselectedAfter
          · exact List.mem_append_left _ hbefore
          · rcases List.mem_cons.mp hselectedAfter with heq | hafter
            · exact False.elim (hselected heq)
            · exact List.mem_append_right _ hafter
        exact Or.inr ⟨oldRegion, List.mem_append_right _ holdRest, hcontains⟩
  let next : IsolationState p ambient :=
    { support := state.support
      supportRefinesAmbient := state.supportRefinesAmbient
      regions := regions
      regionsPairwise := hregionsPairwise
      tracks := tracks
      tracksPairwise := htracksPairwise
      tracksAvoidRegions := htracksAvoidRegions
      covers := hcovers }
  have hcomplementTotal : totalRaw complements =
      quadrupledBoxWinding p selected.box - 4 := by
    have h := totalRaw_complementRegions extracted.grid selected.refinesAmbient
    rw [extracted.track.initial.rawWindingFour] at h
    exact h
  have hrestTotal : totalRaw rest =
      totalRaw selection.before + totalRaw selection.after :=
    totalRaw_append selection.before selection.after
  have hstateTotal : totalRaw state.regions =
      totalRaw selection.before +
        quadrupledBoxWinding p selected.box + totalRaw selection.after := by
    calc
      totalRaw state.regions =
          totalRaw (selection.before ++ selected :: selection.after) :=
        congrArg (fun regions => totalRaw (p := p) regions)
          selection.decomposition
      _ = totalRaw selection.before +
          quadrupledBoxWinding p selected.box + totalRaw selection.after := by
        rw [totalRaw_append, totalRaw_cons]
        ring
  have hnextTotal : totalRaw regions = totalRaw state.regions - 4 := by
    rw [totalRaw_append, hcomplementTotal, hrestTotal, hstateTotal]
    ring
  exact
    { next := next
      support_next := rfl
      totalRaw_next := hnextTotal
      tracks_length_next := rfl }

structure RunResult
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (initial : IsolationState p ambient) (steps : ℕ) where
  final : IsolationState p ambient
  support_final : final.support = initial.support
  totalRaw_final : totalRaw final.regions = 0
  tracks_length_final : final.tracks.length = initial.tracks.length + steps

/-- Recursion on the displayed remaining winding count.  The equality
`totalRaw = 4 * steps` makes every successor call visibly positive. -/
def run
    {p : GaussianPolynomial} (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (steps : ℕ) →
    (state : IsolationState p (CCL.RatBox.symmetric R hR)) →
    totalRaw state.regions = (4 : ℤ) * steps → RunResult state steps
  | 0, state, htotal =>
      { final := state
        support_final := rfl
        totalRaw_final := by simpa using htotal
        tracks_length_final := by simp }
  | steps + 1, state, htotal => by
      have hpositive : 0 < totalRaw state.regions := by
        rw [htotal]
        positivity
      have hnonnegative : ∀ region ∈ state.regions,
          0 ≤ quadrupledBoxWinding p region.box := by
        intro region _hregion
        exact quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
          elimination region.refinesAmbient region.proper region.clearance
      let first := step squarefree elimination state hnonnegative hpositive
      have hnextTotal : totalRaw first.next.regions = (4 : ℤ) * steps := by
        rw [first.totalRaw_next, htotal]
        push_cast
        ring
      let tail := run R hR squarefree hdegree elimination steps first.next hnextTotal
      exact
        { final := tail.final
          support_final := tail.support_final.trans first.support_next
          totalRaw_final := tail.totalRaw_final
          tracks_length_final := by
            rw [tail.tracks_length_final, first.tracks_length_next]
            omega }

theorem totalRaw_nonnegative
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (regions : List (ClearRegion p ambient))
    (hnonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box) :
    0 ≤ totalRaw regions := by
  induction regions with
  | nil => simp
  | cons head tail ih =>
      rw [totalRaw_cons]
      apply add_nonneg (hnonnegative head (by simp))
      exact ih fun region hregion => hnonnegative region (by simp [hregion])

theorem rawWinding_eq_zero_of_mem_totalRaw_eq_zero
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (regions : List (ClearRegion p ambient))
    (hnonnegative : ∀ region ∈ regions,
      0 ≤ quadrupledBoxWinding p region.box)
    (htotal : totalRaw regions = 0)
    {region : ClearRegion p ambient} (hregion : region ∈ regions) :
    quadrupledBoxWinding p region.box = 0 := by
  induction regions with
  | nil => simp at hregion
  | cons head tail ih =>
      have hhead : 0 ≤ quadrupledBoxWinding p head.box :=
        hnonnegative head (by simp)
      have htailMembers : ∀ member ∈ tail,
          0 ≤ quadrupledBoxWinding p member.box := by
        intro member hmember
        exact hnonnegative member (by simp [hmember])
      have htail : 0 ≤ totalRaw tail :=
        totalRaw_nonnegative tail htailMembers
      rw [totalRaw_cons] at htotal
      have hheadZero : quadrupledBoxWinding p head.box = 0 := by omega
      have htailZero : totalRaw tail = 0 := by omega
      rcases List.mem_cons.mp hregion with rfl | hmember
      · exact hheadZero
      · exact ih htailMembers htailZero hmember

/-- Proof-bearing result of exact finite isolation from one initial clear
region of raw winding `4d`. -/
structure Output
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (count : ℕ) where
  support : CCL.RatBox
  support_refinesAmbient : support.Refines ambient
  tracks : List (WindingOneTrack p ambient)
  tracks_length : tracks.length = count
  tracks_pairwise : tracks.Pairwise trackSeparated
  remainder : List (ClearRegion p ambient)
  remainder_pairwise : remainder.Pairwise regionInteriorSeparated
  remainder_rawWinding_zero : ∀ region ∈ remainder,
    quadrupledBoxWinding p region.box = 0
  tracks_avoid_remainder : ∀ track ∈ tracks, ∀ region ∈ remainder,
    ∀ {small : CCL.RatBox}, StrictInterior small region.box →
      track.initial.box.Separated small
  partition_covers : ∀ {z : QI}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ remainder, region.box.Contains z

def Output.trackIndex
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) (i : Fin count) : Fin output.tracks.length :=
  Fin.cast output.tracks_length.symm i

def Output.trackAt
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) (i : Fin count) :
    WindingOneTrack p ambient :=
  output.tracks.get (output.trackIndex i)

theorem Output.trackAt_pairwiseSeparated
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) (i j : Fin count) (hij : i ≠ j) :
    (output.trackAt i).initial.box.Separated
      (output.trackAt j).initial.box := by
  have hindex : output.trackIndex i ≠ output.trackIndex j :=
    fun hEq => hij (Fin.cast_injective output.tracks_length.symm hEq)
  rcases lt_or_gt_of_ne hindex with hlt | hgt
  · exact output.tracks_pairwise.rel_get_of_lt hlt
  · exact CCL.RatBox.separated_symm
      (output.tracks_pairwise.rel_get_of_lt hgt)

/-- Theorem 9.2 from an arbitrary clear initial region whose exact raw
winding is four times the requested natural count. -/
def isolateFromRegion
    {p : GaussianPolynomial} (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (initial : ClearRegion p (CCL.RatBox.symmetric R hR))
    (count : ℕ)
    (hraw : quadrupledBoxWinding p initial.box = (4 : ℤ) * count) :
    Output p (CCL.RatBox.symmetric R hR) count := by
  let state := IsolationState.initial initial
  have htotal : totalRaw state.regions = (4 : ℤ) * count := by
    change quadrupledBoxWinding p initial.box + 0 = (4 : ℤ) * count
    omega
  let result := run R hR squarefree hdegree elimination count state htotal
  have hnonnegative : ∀ region ∈ result.final.regions,
      0 ≤ quadrupledBoxWinding p region.box := by
    intro region _hregion
    exact quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
      elimination region.refinesAmbient region.proper region.clearance
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
        intro region hregion
        exact rawWinding_eq_zero_of_mem_totalRaw_eq_zero
          result.final.regions hnonnegative result.totalRaw_final hregion
      tracks_avoid_remainder := result.final.tracksAvoidRegions
      partition_covers := by
        intro z hz
        apply result.final.covers
        rw [result.support_final]
        exact hz }

theorem Output.remainder_boxWinding_zero
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) {region : ClearRegion p ambient}
    (hregion : region ∈ output.remainder) : boxWinding p region.box = 0 := by
  rw [boxWinding, output.remainder_rawWinding_zero region hregion]
  norm_num

/-- Theorem 9.2 on the coefficient-computed Section 6 large square. -/
def isolateLargeSquare
    {p : GaussianPolynomial}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : 0 < p.natDegree)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Output p (largeSquareBox p) p.natDegree := by
  let R := denseLargeSquareRadius p
  let hR : 0 ≤ R := (denseLargeSquareRadius_pos p).le
  have hsparseDegree : p.toPolynomial.natDegree ≠ 0 := by
    have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
    rw [natDegree_toPolynomial hp]
    exact Nat.ne_of_gt hdegree
  let initial : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := largeSquareBox p
      refinesAmbient := by
        simpa only [largeSquareBox, R, hR] using
          CCL.RatBox.refines_refl (largeSquareBox p)
      proper := largeSquareBox_strict p
      clearance := largeSquareBoundaryClearance hdegree }
  have hraw : quadrupledBoxWinding p initial.box =
      (4 : ℤ) * p.natDegree := by
    simpa only [initial] using quadrupledBoxWinding_largeSquare_eq_degree hdegree
  have output := isolateFromRegion R hR squarefree hsparseDegree elimination
    initial p.natDegree hraw
  simpa only [largeSquareBox, R, hR] using output

end FTA.ExactIsolation
