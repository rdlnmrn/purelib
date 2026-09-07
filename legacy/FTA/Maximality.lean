import FTA.ExactIsolation
import FTA.UniqueChildRefinement

/-!
# Finite maximality of the degree-many isolation

This module formalizes the maximality paragraph following Theorem 9.2.  The
exact-isolation output is treated as a finite safe partition.  A uniform
positive minimum of its edge clearances lets any additional track refine away
from every partition edge, so its small box lies strictly inside one member.
Globally clear track sides then make winding monotone under this strict
containment by a finite `3 × 3` additivity calculation and Theorem 9.1.
-/

namespace FTA.Maximality

open scoped BigOperators

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.BoxClearance
open FTA.CentralBandGrid
open FTA.ComputablePolynomial.DensePolynomial
open FTA.ExactIsolation
open FTA.GaussianPolynomialBounds
open FTA.GlobalNonnegativity
open FTA.GlobalWinding
open FTA.LocalExtraction
open FTA.PathClearance
open FTA.RootTrackSeparation
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

abbrev PartitionIndex
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) :=
  Sum (Fin output.tracks.length) (Fin output.remainder.length)

def cellBox
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) : PartitionIndex output → CCL.RatBox
  | Sum.inl i => (output.tracks.get i).initial.box
  | Sum.inr i => (output.remainder.get i).box

theorem cellProper
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) :
    (i : PartitionIndex output) → (cellBox output i).Proper
  | Sum.inl i => (output.tracks.get i).initial.proper
  | Sum.inr i => (output.remainder.get i).proper

def cellClearance
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) :
    (i : PartitionIndex output) →
      BoxBoundaryClearanceCertificate p (cellBox output i)
  | Sum.inl i => (output.tracks.get i).initial.clearance
  | Sum.inr i => (output.remainder.get i).clearance

theorem cellRefinesAmbient
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) :
    (i : PartitionIndex output) → (cellBox output i).Refines ambient
  | Sum.inl i => (output.tracks.get i).initial.refinesAmbient
  | Sum.inr i => (output.remainder.get i).refinesAmbient

theorem cell_rawWinding
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) (i : PartitionIndex output) :
    quadrupledBoxWinding p (cellBox output i) =
      match i with
      | Sum.inl _ => 4
      | Sum.inr _ => 0 := by
  cases i with
  | inl i => exact (output.tracks.get i).initial.rawWindingFour
  | inr i =>
      exact output.remainder_rawWinding_zero
        (output.remainder.get i) (List.get_mem output.remainder i)

/-- Positive minimum with a positive default, suitable for finite certificate
lists that need not be known nonempty at their definition site. -/
def positiveMinimum (values : List ℚ) : ℚ := values.foldr min 1

theorem positiveMinimum_pos (values : List ℚ)
    (hpositive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => norm_num [positiveMinimum]
  | cons head tail ih =>
      rw [positiveMinimum, List.foldr_cons]
      exact lt_min (hpositive head (by simp))
        (ih fun value hvalue => hpositive value (by simp [hvalue]))

theorem positiveMinimum_le_of_mem {values : List ℚ} {value : ℚ}
    (hvalue : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      rw [positiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp hvalue with rfl | htail
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih htail)

/-- A common lower bound for the positive default and every displayed entry
is a lower bound for the executable finite minimum. -/
theorem le_positiveMinimum {values : List ℚ} {lower : ℚ}
    (lowerLeOne : lower ≤ 1)
    (lowerLe : ∀ value ∈ values, lower ≤ value) :
    lower ≤ positiveMinimum values := by
  induction values with
  | nil => exact lowerLeOne
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact le_min (lowerLe head (by simp))
        (inductionHypothesis fun value member =>
          lowerLe value (by simp [member]))

theorem positiveMinimum_le_one (values : List ℚ) :
    positiveMinimum values ≤ 1 := by
  induction values with
  | nil => exact le_rfl
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact (min_le_right _ _).trans inductionHypothesis

def partitionBounds
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) : List ℚ :=
  (output.tracks.map fun track => track.initial.clearance.bound) ++
    (output.remainder.map fun region => region.clearance.bound)

def partitionMargin
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) : ℚ :=
  positiveMinimum (partitionBounds output)

theorem partitionMargin_pos
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) : 0 < partitionMargin output := by
  apply positiveMinimum_pos
  intro value hvalue
  rw [partitionBounds, List.mem_append] at hvalue
  rcases hvalue with htrack | hregion
  · rw [List.mem_map] at htrack
    rcases htrack with ⟨track, _htrack, rfl⟩
    exact track.initial.clearance.positive
  · rw [List.mem_map] at hregion
    rcases hregion with ⟨region, _hregion, rfl⟩
    exact region.clearance.positive

theorem partitionMargin_le_cellClearance
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) (i : PartitionIndex output) :
    partitionMargin output ≤ (cellClearance output i).bound := by
  apply positiveMinimum_le_of_mem
  cases i with
  | inl i =>
      apply List.mem_append_left
      exact List.mem_map_of_mem (List.get_mem output.tracks i)
  | inr i =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (List.get_mem output.remainder i)

theorem exists_cell_containing
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {count : ℕ}
    (output : Output p ambient count) {z : QI}
    (hz : output.support.Contains z) :
    ∃ i : PartitionIndex output, (cellBox output i).Contains z := by
  rcases output.partition_covers hz with
    ⟨track, htrack, hcontains⟩ | ⟨region, hregion, hcontains⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp htrack
    exact ⟨Sum.inl i, by simpa only [cellBox, hi] using hcontains⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hregion
    exact ⟨Sum.inr i, by simpa only [cellBox, hi] using hcontains⟩

/-- If the center of `inner` lies in `outer` but `inner` is not strictly
inside, an explicit point of `inner` lies on one of the four outer edges. -/
theorem exists_boundary_point_of_not_strictInterior
    {inner outer : CCL.RatBox}
    (hcenter : outer.Contains inner.center)
    (hnot : ¬ StrictInterior inner outer) :
    ∃ point : QI, OnBoxBoundary outer point ∧ inner.Contains point := by
  by_cases hleft : outer.xLower < inner.xLower
  · by_cases hright : inner.xUpper < outer.xUpper
    · by_cases hbottom : outer.yLower < inner.yLower
      · by_cases htop : inner.yUpper < outer.yUpper
        · exact False.elim (hnot ⟨hleft, hright, hbottom, htop⟩)
        · let point := CCL.GaussianRat.mk inner.center.re outer.yUpper
          refine ⟨point, ?_, ?_⟩
          · exact ⟨⟨hcenter.1, hcenter.2.1, outer.y_valid, le_rfl⟩,
              Or.inr (Or.inr (Or.inr rfl))⟩
          · dsimp only [point]
            change inner.xLower ≤ inner.center.re ∧
              inner.center.re ≤ inner.xUpper ∧
              inner.yLower ≤ outer.yUpper ∧ outer.yUpper ≤ inner.yUpper
            exact ⟨inner.contains_center.1, inner.contains_center.2.1,
              inner.contains_center.2.2.1.trans hcenter.2.2.2,
              le_of_not_gt htop⟩
      · let point := CCL.GaussianRat.mk inner.center.re outer.yLower
        refine ⟨point, ?_, ?_⟩
        · exact ⟨⟨hcenter.1, hcenter.2.1, le_rfl, outer.y_valid⟩,
            Or.inr (Or.inr (Or.inl rfl))⟩
        · dsimp only [point]
          change inner.xLower ≤ inner.center.re ∧
            inner.center.re ≤ inner.xUpper ∧
            inner.yLower ≤ outer.yLower ∧ outer.yLower ≤ inner.yUpper
          exact ⟨inner.contains_center.1, inner.contains_center.2.1,
            le_of_not_gt hbottom,
            hcenter.2.2.1.trans inner.contains_center.2.2.2⟩
    · let point := CCL.GaussianRat.mk outer.xUpper inner.center.im
      refine ⟨point, ?_, ?_⟩
      · exact ⟨⟨outer.x_valid, le_rfl, hcenter.2.2.1, hcenter.2.2.2⟩,
          Or.inr (Or.inl rfl)⟩
      · dsimp only [point]
        change inner.xLower ≤ outer.xUpper ∧ outer.xUpper ≤ inner.xUpper ∧
          inner.yLower ≤ inner.center.im ∧ inner.center.im ≤ inner.yUpper
        exact ⟨inner.contains_center.1.trans hcenter.2.1,
          le_of_not_gt hright,
          inner.contains_center.2.2.1, inner.contains_center.2.2.2⟩
  · let point := CCL.GaussianRat.mk outer.xLower inner.center.im
    refine ⟨point, ?_, ?_⟩
    · exact ⟨⟨le_rfl, outer.x_valid, hcenter.2.2.1, hcenter.2.2.2⟩,
        Or.inl rfl⟩
    · dsimp only [point]
      change inner.xLower ≤ outer.xLower ∧ outer.xLower ≤ inner.xUpper ∧
        inner.yLower ≤ inner.center.im ∧ inner.center.im ≤ inner.yUpper
      exact ⟨le_of_not_gt hleft,
        hcenter.1.trans inner.contains_center.2.1,
        inner.contains_center.2.2.1, inner.contains_center.2.2.2⟩

/-- Quantitative edge avoidance: a winding-one state whose displayed
dominance inequality holds must be strictly inside the cell containing its
center. -/
theorem strictInterior_of_center_mem_of_dominates
    (p : GaussianPolynomial) {ambient cell : CCL.RatBox}
    (state : WindingOneState p ambient)
    (cellRefines : cell.Refines ambient)
    (clearance : BoxBoundaryClearanceCertificate p cell)
    (hcenter : cell.Contains state.box.center)
    (hdominates : centerResidualBound p ambient state.box +
        denseLipschitzBound p ambient * state.box.diagonalSq <
      clearance.bound / 2) :
    StrictInterior state.box cell := by
  by_contra hnot
  obtain ⟨point, hboundary, hpointState⟩ :=
    exists_boundary_point_of_not_strictInterior hcenter hnot
  have hdistance : normSq (point + -state.box.center) ≤
      state.box.diagonalSq := by
    simpa only [GaussianRat.sub_eq_add_neg] using
      CCL.RatBox.normSq_sub_le_diagonalSq hpointState state.box.contains_center
  let nearby : NearbyClearPointCertificate p ambient state.box :=
    { point := point
      point_mem := cellRefines.contains hboundary.1
      clearance := clearance.bound
      radiusSq := state.box.diagonalSq
      clearance_lower := clearance.lower point hboundary
      center_distance := hdistance
      dominates := hdominates }
  have hzero := quadrupledBoxWinding_eq_zero_of_nearby_clear_point
    p state.refinesAmbient state.proper nearby
  rw [state.rawWindingFour] at hzero
  norm_num at hzero

/-- A globally line-clear winding-one state strictly inside a clear region
forces that region's raw winding to be at least four. -/
theorem region_rawWinding_ge_four_of_strictInterior
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p (CCL.RatBox.symmetric R hR))
    (region : ClearRegion p (CCL.RatBox.symmetric R hR))
    (hstrict : StrictInterior state.box region.box) :
    4 ≤ quadrupledBoxWinding p region.box := by
  let grid := CentralBandGrid.build region.clearance state.proper hstrict
    (state.ambientLeftClearance.restrict region.refinesAmbient)
    (state.ambientRightClearance.restrict region.refinesAmbient)
    (state.ambientBottomClearance.restrict region.refinesAmbient)
    (state.ambientTopClearance.restrict region.refinesAmbient)
  have hsw := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.southwest.refines.trans region.refinesAmbient)
      grid.southwest.proper grid.southwest.clearance
  have hw := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.west.refines.trans region.refinesAmbient)
      grid.west.proper grid.west.clearance
  have hnw := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.northwest.refines.trans region.refinesAmbient)
      grid.northwest.proper grid.northwest.clearance
  have hs := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.south.refines.trans region.refinesAmbient)
      grid.south.proper grid.south.clearance
  have hn := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.north.refines.trans region.refinesAmbient)
      grid.north.proper grid.north.clearance
  have hse := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.southeast.refines.trans region.refinesAmbient)
      grid.southeast.proper grid.southeast.clearance
  have he := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.east.refines.trans region.refinesAmbient)
      grid.east.proper grid.east.clearance
  have hne := quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
    elimination (grid.northeast.refines.trans region.refinesAmbient)
      grid.northeast.proper grid.northeast.clearance
  have hadditive := grid.additive
  rw [state.rawWindingFour] at hadditive
  omega

/-- Uniform positive refinement radius which resolves every edge of the
finite isolation partition simultaneously. -/
def assignmentRadius
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    {count : ℕ} (output : Output p ambient count) : ℚ :=
  min 1 (partitionMargin output / (8 * denseLipschitzBound p ambient))

theorem assignmentRadius_pos
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    {count : ℕ} (output : Output p ambient count) :
    0 < assignmentRadius p ambient output := by
  apply lt_min
  · norm_num
  · exact div_pos (partitionMargin_pos output)
      (mul_pos (by norm_num) (denseLipschitzBound_pos p ambient))

theorem assignmentRadius_sq_le
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    {count : ℕ} (output : Output p ambient count) :
    assignmentRadius p ambient output ^ 2 ≤
      assignmentRadius p ambient output := by
  have hpositive := assignmentRadius_pos p ambient output
  have hone : assignmentRadius p ambient output ≤ 1 := min_le_left _ _
  nlinarith [mul_nonneg hpositive.le (sub_nonneg.mpr hone)]

theorem assignment_dominates
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    {count : ℕ} (output : Output p ambient count)
    (state : WindingOneState p ambient)
    (hdiagonal : state.box.diagonalSq ≤
      assignmentRadius p ambient output ^ 2)
    (i : PartitionIndex output) :
    centerResidualBound p ambient state.box +
        denseLipschitzBound p ambient * state.box.diagonalSq <
      (cellClearance output i).bound / 2 := by
  let radius := assignmentRadius p ambient output
  let margin := partitionMargin output
  let L := denseLipschitzBound p ambient
  have hradiusPos : 0 < radius := assignmentRadius_pos p ambient output
  have hL : 0 < L := denseLipschitzBound_pos p ambient
  have hradiusRatio : radius ≤ margin / (8 * L) := min_le_right _ _
  have hscaled : 8 * L * radius ≤ margin := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hL)] at hradiusRatio
    nlinarith
  have hdiagonalRadius : state.box.diagonalSq ≤ radius :=
    hdiagonal.trans (assignmentRadius_sq_le p ambient output)
  have hmarginCell := partitionMargin_le_cellClearance output i
  dsimp only [centerResidualBound]
  dsimp only [radius, margin, L] at *
  nlinarith [state.box.diagonalSq_nonneg]

/-- Every track supported in the isolation support has a finite refinement
strictly owned by one of the `count` winding-one output cells; zero-winding
remainder cells are excluded by monotonicity. -/
theorem exists_output_owner
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {count : ℕ}
    (output : Output p (CCL.RatBox.symmetric R hR) count)
    (track : WindingOneTrack p (CCL.RatBox.symmetric R hR))
    (hsupport : track.initial.box.Refines output.support) :
    ∃ owner : Fin output.tracks.length,
      StrictInterior
        (track.refine track.initial
          (assignmentRadius p (CCL.RatBox.symmetric R hR) output)
          (assignmentRadius_pos p (CCL.RatBox.symmetric R hR) output)).box
        (output.tracks.get owner).initial.box := by
  let radius := assignmentRadius p (CCL.RatBox.symmetric R hR) output
  let hradius := assignmentRadius_pos p (CCL.RatBox.symmetric R hR) output
  let refined := track.refine track.initial radius hradius
  have hrefinedSupport : refined.box.Refines output.support :=
    (track.nested track.initial radius hradius).trans hsupport
  have hcenterSupport : output.support.Contains refined.box.center :=
    hrefinedSupport.contains refined.box.contains_center
  obtain ⟨cell, hcenterCell⟩ := exists_cell_containing output hcenterSupport
  have hdiagonal : refined.box.diagonalSq ≤ radius ^ 2 :=
    track.accurate track.initial radius hradius
  have hstrict : StrictInterior refined.box (cellBox output cell) :=
    strictInterior_of_center_mem_of_dominates p refined
      (cellRefinesAmbient output cell) (cellClearance output cell) hcenterCell
      (assignment_dominates p (CCL.RatBox.symmetric R hR) output
        refined hdiagonal cell)
  cases cell with
  | inl owner =>
      exact ⟨owner, by simpa only [refined, radius, hradius, cellBox] using hstrict⟩
  | inr remainderIndex =>
      let region := output.remainder.get remainderIndex
      have hge := region_rawWinding_ge_four_of_strictInterior p R hR
        squarefree hdegree elimination refined region hstrict
      have hzero := output.remainder_rawWinding_zero region
        (List.get_mem output.remainder remainderIndex)
      omega

def verticalGapClearance
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    {a b : ℚ} (hab : a < b) (ambient : CCL.RatBox) :
    VerticalLineClearance p ambient (verticalSafeCoordinate elimination hab) :=
  verticalOfPathCertificate p ambient (verticalSafeCoordinate elimination hab)
    (certificateOfCoprime
      (elimination.vertical_coprime _
        (verticalSafeCoordinate_spec elimination hab).1)
      (verticalInterval ambient))

def horizontalGapClearance
    {p : GaussianPolynomial} {D : ℕ}
    (elimination : AxisEliminationCertificate p D)
    {a b : ℚ} (hab : a < b) (ambient : CCL.RatBox) :
    HorizontalLineClearance p ambient (horizontalSafeCoordinate elimination hab) :=
  horizontalOfPathCertificate p ambient (horizontalSafeCoordinate elimination hab)
    (certificateOfCoprime
      (elimination.horizontal_coprime _
        (horizontalSafeCoordinate_spec elimination hab).1)
      (horizontalInterval ambient))

theorem region_rawWinding_ge_eight_of_x_ordered
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (region : ClearRegion p (CCL.RatBox.symmetric R hR))
    (left right : WindingOneState p (CCL.RatBox.symmetric R hR))
    (hleft : StrictInterior left.box region.box)
    (hright : StrictInterior right.box region.box)
    (hgap : left.box.xUpper < right.box.xLower) :
    8 ≤ quadrupledBoxWinding p region.box := by
  let cut := verticalSafeCoordinate elimination hgap
  have hcutSpec := verticalSafeCoordinate_spec elimination hgap
  have hcut : region.box.xLower ≤ cut ∧ cut ≤ region.box.xUpper := by
    exact ⟨hleft.left.le.trans (left.box.x_valid.trans hcutSpec.2.1.le),
      hcutSpec.2.2.le.trans (right.box.x_valid.trans hright.right.le)⟩
  let leftBox := region.box.verticalLeft cut hcut
  let rightBox := region.box.verticalRight cut hcut
  have hleftRefines : leftBox.Refines region.box :=
    CCL.RatBox.verticalLeft_refines region.box cut hcut
  have hrightRefines : rightBox.Refines region.box :=
    CCL.RatBox.verticalRight_refines region.box cut hcut
  let cutClearance := verticalGapClearance elimination hgap region.box
  let leftClearance : BoxBoundaryClearanceCertificate p leftBox := by
    apply boundaryOfLines
    · simpa [leftBox, CCL.RatBox.verticalLeft] using
        (leftOfBoundary region.clearance).restrict hleftRefines
    · simpa [leftBox, CCL.RatBox.verticalLeft] using
        cutClearance.restrict hleftRefines
    · simpa [leftBox, CCL.RatBox.verticalLeft] using
        (bottomOfBoundary region.clearance).restrict hleftRefines
    · simpa [leftBox, CCL.RatBox.verticalLeft] using
        (topOfBoundary region.clearance).restrict hleftRefines
  let rightClearance : BoxBoundaryClearanceCertificate p rightBox := by
    apply boundaryOfLines
    · simpa [rightBox, CCL.RatBox.verticalRight] using
        cutClearance.restrict hrightRefines
    · simpa [rightBox, CCL.RatBox.verticalRight] using
        (rightOfBoundary region.clearance).restrict hrightRefines
    · simpa [rightBox, CCL.RatBox.verticalRight] using
        (bottomOfBoundary region.clearance).restrict hrightRefines
    · simpa [rightBox, CCL.RatBox.verticalRight] using
        (topOfBoundary region.clearance).restrict hrightRefines
  let leftRegion : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := leftBox
      refinesAmbient := hleftRefines.trans region.refinesAmbient
      proper := by
        constructor
        · dsimp only [leftBox, CCL.RatBox.verticalLeft]
          linarith [hleft.left, left.box.x_valid, hcutSpec.2.1]
        · simpa only [leftBox, CCL.RatBox.verticalLeft] using region.proper.2
      clearance := leftClearance }
  let rightRegion : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := rightBox
      refinesAmbient := hrightRefines.trans region.refinesAmbient
      proper := by
        constructor
        · dsimp only [rightBox, CCL.RatBox.verticalRight]
          linarith [hcutSpec.2.2, right.box.x_valid, hright.right]
        · simpa only [rightBox, CCL.RatBox.verticalRight] using region.proper.2
      clearance := rightClearance }
  have hleftInside : StrictInterior left.box leftRegion.box := by
    exact
      { left := by simpa only [leftRegion, leftBox,
          CCL.RatBox.verticalLeft] using hleft.left
        right := by
          dsimp only [leftRegion, leftBox, CCL.RatBox.verticalLeft, cut]
          exact hcutSpec.2.1
        bottom := by simpa only [leftRegion, leftBox,
          CCL.RatBox.verticalLeft] using hleft.bottom
        top := by simpa only [leftRegion, leftBox,
          CCL.RatBox.verticalLeft] using hleft.top }
  have hrightInside : StrictInterior right.box rightRegion.box := by
    exact
      { left := by
          dsimp only [rightRegion, rightBox, CCL.RatBox.verticalRight, cut]
          exact hcutSpec.2.2
        right := by simpa only [rightRegion, rightBox,
          CCL.RatBox.verticalRight] using hright.right
        bottom := by simpa only [rightRegion, rightBox,
          CCL.RatBox.verticalRight] using hright.bottom
        top := by simpa only [rightRegion, rightBox,
          CCL.RatBox.verticalRight] using hright.top }
  have hleftFour := region_rawWinding_ge_four_of_strictInterior p R hR
    squarefree hdegree elimination left leftRegion hleftInside
  have hrightFour := region_rawWinding_ge_four_of_strictInterior p R hR
    squarefree hdegree elimination right rightRegion hrightInside
  have hadditive := quadrupledBoxWinding_vertical_split p region.box cut hcut
  simp only [leftRegion, leftBox] at hleftFour
  simp only [rightRegion, rightBox] at hrightFour
  omega

theorem region_rawWinding_ge_eight_of_y_ordered
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (region : ClearRegion p (CCL.RatBox.symmetric R hR))
    (bottom top : WindingOneState p (CCL.RatBox.symmetric R hR))
    (hbottom : StrictInterior bottom.box region.box)
    (htop : StrictInterior top.box region.box)
    (hgap : bottom.box.yUpper < top.box.yLower) :
    8 ≤ quadrupledBoxWinding p region.box := by
  let cut := horizontalSafeCoordinate elimination hgap
  have hcutSpec := horizontalSafeCoordinate_spec elimination hgap
  have hcut : region.box.yLower ≤ cut ∧ cut ≤ region.box.yUpper := by
    exact ⟨hbottom.bottom.le.trans (bottom.box.y_valid.trans hcutSpec.2.1.le),
      hcutSpec.2.2.le.trans (top.box.y_valid.trans htop.top.le)⟩
  let lowerBox := region.box.horizontalLower cut hcut
  let upperBox := region.box.horizontalUpper cut hcut
  have hlowerRefines : lowerBox.Refines region.box :=
    CCL.RatBox.horizontalLower_refines region.box cut hcut
  have hupperRefines : upperBox.Refines region.box :=
    CCL.RatBox.horizontalUpper_refines region.box cut hcut
  let cutClearance := horizontalGapClearance elimination hgap region.box
  let lowerClearance : BoxBoundaryClearanceCertificate p lowerBox := by
    apply boundaryOfLines
    · simpa [lowerBox, CCL.RatBox.horizontalLower] using
        (leftOfBoundary region.clearance).restrict hlowerRefines
    · simpa [lowerBox, CCL.RatBox.horizontalLower] using
        (rightOfBoundary region.clearance).restrict hlowerRefines
    · simpa [lowerBox, CCL.RatBox.horizontalLower] using
        (bottomOfBoundary region.clearance).restrict hlowerRefines
    · simpa [lowerBox, CCL.RatBox.horizontalLower] using
        cutClearance.restrict hlowerRefines
  let upperClearance : BoxBoundaryClearanceCertificate p upperBox := by
    apply boundaryOfLines
    · simpa [upperBox, CCL.RatBox.horizontalUpper] using
        (leftOfBoundary region.clearance).restrict hupperRefines
    · simpa [upperBox, CCL.RatBox.horizontalUpper] using
        (rightOfBoundary region.clearance).restrict hupperRefines
    · simpa [upperBox, CCL.RatBox.horizontalUpper] using
        cutClearance.restrict hupperRefines
    · simpa [upperBox, CCL.RatBox.horizontalUpper] using
        (topOfBoundary region.clearance).restrict hupperRefines
  let lowerRegion : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := lowerBox
      refinesAmbient := hlowerRefines.trans region.refinesAmbient
      proper := by
        constructor
        · simpa only [lowerBox, CCL.RatBox.horizontalLower] using region.proper.1
        · dsimp only [lowerBox, CCL.RatBox.horizontalLower]
          linarith [hbottom.bottom, bottom.box.y_valid, hcutSpec.2.1]
      clearance := lowerClearance }
  let upperRegion : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := upperBox
      refinesAmbient := hupperRefines.trans region.refinesAmbient
      proper := by
        constructor
        · simpa only [upperBox, CCL.RatBox.horizontalUpper] using region.proper.1
        · dsimp only [upperBox, CCL.RatBox.horizontalUpper]
          linarith [hcutSpec.2.2, top.box.y_valid, htop.top]
      clearance := upperClearance }
  have hbottomInside : StrictInterior bottom.box lowerRegion.box := by
    exact
      { left := by simpa only [lowerRegion, lowerBox,
          CCL.RatBox.horizontalLower] using hbottom.left
        right := by simpa only [lowerRegion, lowerBox,
          CCL.RatBox.horizontalLower] using hbottom.right
        bottom := by simpa only [lowerRegion, lowerBox,
          CCL.RatBox.horizontalLower] using hbottom.bottom
        top := by
          dsimp only [lowerRegion, lowerBox, CCL.RatBox.horizontalLower, cut]
          exact hcutSpec.2.1 }
  have htopInside : StrictInterior top.box upperRegion.box := by
    exact
      { left := by simpa only [upperRegion, upperBox,
          CCL.RatBox.horizontalUpper] using htop.left
        right := by simpa only [upperRegion, upperBox,
          CCL.RatBox.horizontalUpper] using htop.right
        bottom := by
          dsimp only [upperRegion, upperBox, CCL.RatBox.horizontalUpper, cut]
          exact hcutSpec.2.2
        top := by simpa only [upperRegion, upperBox,
          CCL.RatBox.horizontalUpper] using htop.top }
  have hlowerFour := region_rawWinding_ge_four_of_strictInterior p R hR
    squarefree hdegree elimination bottom lowerRegion hbottomInside
  have hupperFour := region_rawWinding_ge_four_of_strictInterior p R hR
    squarefree hdegree elimination top upperRegion htopInside
  have hadditive := quadrupledBoxWinding_horizontal_split p region.box cut hcut
  simp only [lowerRegion, lowerBox] at hlowerFour
  simp only [upperRegion, upperBox] at hupperFour
  omega

theorem region_rawWinding_ge_eight_of_separated
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (region : ClearRegion p (CCL.RatBox.symmetric R hR))
    (left right : WindingOneState p (CCL.RatBox.symmetric R hR))
    (hleft : StrictInterior left.box region.box)
    (hright : StrictInterior right.box region.box)
    (hseparated : left.box.Separated right.box) :
    8 ≤ quadrupledBoxWinding p region.box := by
  rcases hseparated with ⟨gap, hgapPositive, hgap⟩
  rcases hgap with h | h | h | h
  · exact region_rawWinding_ge_eight_of_x_ordered p R hR squarefree hdegree
      elimination region left right hleft hright (by linarith)
  · exact region_rawWinding_ge_eight_of_x_ordered p R hR squarefree hdegree
      elimination region right left hright hleft (by linarith)
  · exact region_rawWinding_ge_eight_of_y_ordered p R hR squarefree hdegree
      elimination region left right hleft hright (by linarith)
  · exact region_rawWinding_ge_eight_of_y_ordered p R hR squarefree hdegree
      elimination region right left hright hleft (by linarith)

/-- Direct uniqueness form of the maximality argument: two separated
winding-one states cannot both be strictly supported in a single
raw-winding-four state.  This is the identification principle used by the
positive-curve branch of Theorem 10.2. -/
theorem separated_states_not_both_inside_windingOne
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (owner left right :
      WindingOneState p (CCL.RatBox.symmetric R hR))
    (leftInside : StrictInterior left.box owner.box)
    (rightInside : StrictInterior right.box owner.box)
    (separated : left.box.Separated right.box) : False := by
  let region : ClearRegion p (CCL.RatBox.symmetric R hR) :=
    { box := owner.box
      refinesAmbient := owner.refinesAmbient
      proper := owner.proper
      clearance := owner.clearance }
  have atLeastEight := region_rawWinding_ge_eight_of_separated
    p R hR squarefree hdegree elimination region left right
      leftInside rightInside separated
  have exactlyFour := owner.rawWindingFour
  dsimp only [region] at atLeastEight
  omega

/-- Maximality paragraph after Theorem 9.2: every finite pairwise separated
family supported in the isolation square injects into the returned output
tracks, and therefore has cardinality at most `count`. -/
theorem finite_family_card_le_output_count
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {count familyCount : ℕ}
    (output : Output p (CCL.RatBox.symmetric R hR) count)
    (family : Fin familyCount →
      WindingOneTrack p (CCL.RatBox.symmetric R hR))
    (hsupported : ∀ i, (family i).initial.box.Refines output.support)
    (hpairwise : ∀ i j, i ≠ j →
      (family i).initial.box.Separated (family j).initial.box) :
    familyCount ≤ count := by
  let radius := assignmentRadius p (CCL.RatBox.symmetric R hR) output
  let hradius := assignmentRadius_pos p (CCL.RatBox.symmetric R hR) output
  let refined : (i : Fin familyCount) →
      WindingOneState p (CCL.RatBox.symmetric R hR) :=
    fun i => (family i).refine (family i).initial radius hradius
  have hownerExists (i : Fin familyCount) :
      ∃ owner : Fin output.tracks.length,
        StrictInterior (refined i).box (output.tracks.get owner).initial.box := by
    simpa only [refined, radius, hradius] using
      exists_output_owner p R hR squarefree hdegree elimination output
        (family i) (hsupported i)
  let owner : Fin familyCount → Fin output.tracks.length :=
    fun i => Fin.find
      (fun candidate =>
        StrictInterior (refined i).box
          (output.tracks.get candidate).initial.box)
      (hownerExists i)
  have hownerSpec (i : Fin familyCount) :
      StrictInterior (refined i).box
        (output.tracks.get (owner i)).initial.box := by
    exact Fin.find_spec (hownerExists i)
  have hownerInjective : Function.Injective owner := by
    intro i j howner
    by_contra hij
    have hseparated := (hpairwise i j hij).of_refines
      ((family i).nested (family i).initial radius hradius)
      ((family j).nested (family j).initial radius hradius)
    have hiInside := hownerSpec i
    have hjInside := hownerSpec j
    rw [← howner] at hjInside
    let region : ClearRegion p (CCL.RatBox.symmetric R hR) :=
      { box := (output.tracks.get (owner i)).initial.box
        refinesAmbient := (output.tracks.get (owner i)).initial.refinesAmbient
        proper := (output.tracks.get (owner i)).initial.proper
        clearance := (output.tracks.get (owner i)).initial.clearance }
    have hge := region_rawWinding_ge_eight_of_separated p R hR squarefree
      hdegree elimination region (refined i) (refined j) hiInside hjInside
        hseparated
    have hfour := (output.tracks.get (owner i)).initial.rawWindingFour
    simp only [region] at hge
    omega
  have hcard := Fintype.card_le_of_injective owner hownerInjective
  simpa only [Fintype.card_fin, output.tracks_length] using hcard

theorem isolateLargeSquare_support
    {p : GaussianPolynomial}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : 0 < p.natDegree)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (isolateLargeSquare squarefree hdegree elimination).support =
      largeSquareBox p := by
  rfl

/-- Degree-sharp maximality on the coefficient-computed large square. -/
theorem finite_family_card_le_natDegree
    {p : GaussianPolynomial}
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : 0 < p.natDegree)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {familyCount : ℕ}
    (family : Fin familyCount → WindingOneTrack p (largeSquareBox p))
    (hpairwise : ∀ i j, i ≠ j →
      (family i).initial.box.Separated (family j).initial.box) :
    familyCount ≤ p.natDegree := by
  have hsparseDegree : p.toPolynomial.natDegree ≠ 0 := by
    have hp : p.isZero = false := isZero_false_of_natDegree_pos hdegree
    rw [natDegree_toPolynomial hp]
    exact Nat.ne_of_gt hdegree
  apply finite_family_card_le_output_count p (denseLargeSquareRadius p)
    (denseLargeSquareRadius_pos p).le squarefree hsparseDegree elimination
    (isolateLargeSquare squarefree hdegree elimination) family
  · intro i
    rw [isolateLargeSquare_support squarefree hdegree elimination]
    exact (family i).initial.refinesAmbient
  · exact hpairwise

end FTA.Maximality
