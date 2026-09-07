import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ExactIsolation

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace RFAP.Maximality

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
abbrev ClearRegion := RFAP.ExactIsolation.ClearRegion
abbrev Output := RFAP.ExactIsolation.Output

open RFAP.Winding
open RFAP.PolynomialBounds
open RFAP.LocalExtraction
open RFAP.BoxClearance
open RFAP.CentralBandGrid
open RFAP.ExactIsolation

/-! ## Finite partition margins -/

def positiveMinimum (values : List Coordinate) : Coordinate :=
  values.foldr min 1

theorem positiveMinimum_pos (values : List Coordinate)
    (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      exact lt_min (positive head (by simp))
        (inductionHypothesis fun value member =>
          positive value (by simp [member]))

theorem positiveMinimum_le_of_mem
    {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : positiveMinimum values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [positiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

def partitionBounds
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) : List Coordinate :=
  (output.tracks.map fun track => track.initial.clearance.bound) ++
    (output.remainder.map fun region => region.clearance.bound)

def partitionMargin
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) : Coordinate :=
  positiveMinimum (partitionBounds output)

theorem partitionMargin_pos
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) : 0 < partitionMargin output := by
  apply positiveMinimum_pos
  intro value member
  rw [partitionBounds, List.mem_append] at member
  rcases member with trackMember | regionMember
  · rw [QuotientFreeList.mem_map] at trackMember
    rcases trackMember with ⟨track, _member, rfl⟩
    exact track.initial.clearance.positive
  · rw [QuotientFreeList.mem_map] at regionMember
    rcases regionMember with ⟨region, _member, rfl⟩
    exact region.clearance.positive

theorem partitionMargin_le_track
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (index : Fin output.tracks.length) :
    partitionMargin output ≤
      (output.tracks.get index).initial.clearance.bound := by
  apply positiveMinimum_le_of_mem
  apply List.mem_append_left
  exact QuotientFreeList.mem_map_of_mem (List.get_mem output.tracks index)

theorem partitionMargin_le_remainder
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (index : Fin output.remainder.length) :
    partitionMargin output ≤
      (output.remainder.get index).clearance.bound := by
  apply positiveMinimum_le_of_mem
  apply List.mem_append_right
  exact QuotientFreeList.mem_map_of_mem (List.get_mem output.remainder index)

/-! ## A total finite partition lookup -/

def findContainingIndex
    {α : Type} (boxOf : α → Box) (point : Gaussian) :
    (values : List α) → Option (Fin values.length)
  | [] => none
  | head :: tail =>
      if (boxOf head).Contains point then some 0
      else
        match findContainingIndex boxOf point tail with
        | none => none
        | some index => some index.succ

theorem findContainingIndex_sound
    {α : Type} (boxOf : α → Box) (point : Gaussian) :
    ∀ (values : List α) (index : Fin values.length),
      findContainingIndex boxOf point values = some index →
        (boxOf (values.get index)).Contains point
  | [], index, _ => Fin.elim0 index
  | head :: tail, index, found => by
      by_cases headContains : (boxOf head).Contains point
      · rw [findContainingIndex, if_pos headContains] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headContains
      · rw [findContainingIndex, if_neg headContains] at found
        cases recursive : findContainingIndex boxOf point tail with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact findContainingIndex_sound boxOf point tail tailIndex
              recursive

theorem findContainingIndex_ne_none_of_exists
    {α : Type} (boxOf : α → Box) (point : Gaussian) :
    ∀ (values : List α),
      (∃ value ∈ values, (boxOf value).Contains point) →
        findContainingIndex boxOf point values ≠ none := by
  intro values witness
  induction values with
  | nil =>
      rcases witness with ⟨value, member, _⟩
      exact (List.not_mem_nil member).elim
  | cons head tail inductionHypothesis =>
      by_cases headContains : (boxOf head).Contains point
      · intro foundNone
        rw [findContainingIndex, if_pos headContains] at foundNone
        exact Option.some_ne_none 0 foundNone
      · have tailExists : ∃ value ∈ tail,
            (boxOf value).Contains point := by
          rcases witness with ⟨value, member, contains⟩
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact (headContains contains).elim
          · exact ⟨value, tailMember, contains⟩
        have recursive := inductionHypothesis tailExists
        intro foundNone
        rw [findContainingIndex, if_neg headContains] at foundNone
        cases found : findContainingIndex boxOf point tail with
        | none => exact (recursive found).elim
        | some index =>
            rw [found] at foundNone
            exact Option.some_ne_none index.succ foundNone

inductive PartitionLocation
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) : Type
  | track (index : Fin output.tracks.length)
  | remainder (index : Fin output.remainder.length)

def PartitionLocation.box
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Output p ambient count} : PartitionLocation output → Box
  | .track index => (output.tracks.get index).initial.box
  | .remainder index => (output.remainder.get index).box

def findPartitionLocation?
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (point : Gaussian) :
    Option (PartitionLocation output) :=
  match findContainingIndex (fun track => track.initial.box) point
      output.tracks with
  | some index => some (.track index)
  | none =>
      match findContainingIndex (fun region => region.box) point
          output.remainder with
      | some index => some (.remainder index)
      | none => none

theorem findPartitionLocation_sound
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (point : Gaussian)
    (location : PartitionLocation output)
    (found : findPartitionLocation? output point = some location) :
    location.box.Contains point := by
  unfold findPartitionLocation? at found
  cases trackFound : findContainingIndex
      (fun track : WindingOneTrack p ambient => track.initial.box)
      point output.tracks with
  | some trackIndex =>
      rw [trackFound] at found
      have locationEq : location = .track trackIndex :=
        Option.some.inj found.symm
      subst location
      exact findContainingIndex_sound _ _ _ _ trackFound
  | none =>
      rw [trackFound] at found
      cases regionFound : findContainingIndex
          (fun region : ClearRegion p ambient => region.box)
          point output.remainder with
      | none => rw [regionFound] at found; contradiction
      | some regionIndex =>
          rw [regionFound] at found
          have locationEq : location = .remainder regionIndex :=
            Option.some.inj found.symm
          subst location
          exact findContainingIndex_sound _ _ _ _ regionFound

theorem findPartitionLocation_ne_none
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) {point : Gaussian}
    (inside : output.support.Contains point) :
    findPartitionLocation? output point ≠ none := by
  rcases output.partition_covers inside with
    ⟨track, trackMember, trackContains⟩ |
      ⟨region, regionMember, regionContains⟩
  · have trackExists : ∃ value ∈ output.tracks,
        value.initial.box.Contains point :=
      ⟨track, trackMember, trackContains⟩
    have trackFound := findContainingIndex_ne_none_of_exists
      (fun value : WindingOneTrack p ambient => value.initial.box)
      point output.tracks trackExists
    unfold findPartitionLocation?
    cases found : findContainingIndex
        (fun value : WindingOneTrack p ambient => value.initial.box)
        point output.tracks with
    | none => exact (trackFound found).elim
    | some index => simp
  · have regionExists : ∃ value ∈ output.remainder,
        value.box.Contains point :=
      ⟨region, regionMember, regionContains⟩
    have regionFound := findContainingIndex_ne_none_of_exists
      (fun value : ClearRegion p ambient => value.box)
      point output.remainder regionExists
    unfold findPartitionLocation?
    cases trackFound : findContainingIndex
        (fun value : WindingOneTrack p ambient => value.initial.box)
        point output.tracks with
    | some index => simp
    | none =>
        simp only
        cases found : findContainingIndex
            (fun value : ClearRegion p ambient => value.box)
            point output.remainder with
        | none => exact (regionFound found).elim
        | some index => simp

def locatePartition
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (point : Gaussian)
    (inside : output.support.Contains point) : PartitionLocation output :=
  match found : findPartitionLocation? output point with
  | some location => location
  | none => False.elim (findPartitionLocation_ne_none output inside found)

theorem locatePartition_contains
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (point : Gaussian)
    (inside : output.support.Contains point) :
    (locatePartition output point inside).box.Contains point := by
  unfold locatePartition
  split
  next location found =>
    exact findPartitionLocation_sound output point location found
  next found =>
    exact (findPartitionLocation_ne_none output inside found).elim

/-! ## Strict ownership of a sufficiently refined state -/

def assignmentRadius
    (p : GaussianPolynomial) (ambient : Box)
    {count : Nat} (output : Output p ambient count) : Coordinate :=
  min 1 (partitionMargin output /
    (8 * denseLipschitzBound p ambient))

theorem assignmentRadius_pos
    (p : GaussianPolynomial) (ambient : Box)
    {count : Nat} (output : Output p ambient count) :
    0 < assignmentRadius p ambient output := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct
      (partitionMargin_pos output)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p ambient)))

theorem assignmentRadius_sq_le
    (p : GaussianPolynomial) (ambient : Box)
    {count : Nat} (output : Output p ambient count) :
    assignmentRadius p ambient output ^ 2 ≤
      assignmentRadius p ambient output := by
  let radius := assignmentRadius p ambient output
  have radiusPositive := assignmentRadius_pos p ambient output
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  rw [pow_two]
  calc
    radius * radius ≤ 1 * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le
    _ = radius := by ring1

theorem assignment_dominates
    (p : GaussianPolynomial) (ambient : Box)
    {count : Nat} (output : Output p ambient count)
    (state : WindingOneState p ambient)
    (diagonal : state.box.diagonalSq ≤
      assignmentRadius p ambient output ^ 2)
    {clearance : Coordinate}
    (marginLe : partitionMargin output ≤ clearance) :
    2 * (anchorResidualBound p ambient state.box +
      denseLipschitzBound p ambient * state.box.diagonalSq) < clearance := by
  let radius := assignmentRadius p ambient output
  let lipschitz := denseLipschitzBound p ambient
  let margin := partitionMargin output
  have radiusPositive := assignmentRadius_pos p ambient output
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  have radiusSquareLe := assignmentRadius_sq_le p ambient output
  have radiusRatio : radius ≤ margin / (8 * lipschitz) :=
    min_le_right _ _
  have eightLipschitzPositive : 0 < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have scaled : radius * (8 * lipschitz) ≤ margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      eightLipschitzPositive).mp radiusRatio
  have fourLipschitzNonnegative : 0 ≤ 4 * lipschitz :=
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      lipschitzPositive).le
  have productPositive : 0 < lipschitz * radius :=
    RFAP.ConstructiveFraction.mul_pos_direct lipschitzPositive radiusPositive
  calc
    2 * (anchorResidualBound p ambient state.box +
        lipschitz * state.box.diagonalSq) =
        4 * lipschitz * state.box.diagonalSq := by
      dsimp only [anchorResidualBound, lipschitz]
      ring1
    _ ≤ 4 * lipschitz * radius ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
        fourLipschitzNonnegative
    _ ≤ 4 * lipschitz * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusSquareLe
        fourLipschitzNonnegative
    _ = 4 * (lipschitz * radius) := by ring1
    _ < 8 * (lipschitz * radius) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (show (4 : Coordinate) < 8 by decide) productPositive
    _ = radius * (8 * lipschitz) := by ring1
    _ ≤ margin := scaled
    _ ≤ clearance := marginLe

theorem exists_boundary_point_of_anchor_mem_of_not_strictInterior
    {inner outer : Box} (anchorInside : outer.Contains inner.anchor)
    (notStrict : ¬inner.StrictInterior outer) :
    ∃ point : Gaussian,
      OnBoxBoundary outer point ∧ inner.Contains point := by
  by_cases left : outer.xLower < inner.xLower
  · by_cases right : inner.xUpper < outer.xUpper
    · by_cases bottom : outer.yLower < inner.yLower
      · by_cases top : inner.yUpper < outer.yUpper
        · exact (notStrict ⟨left, right, bottom, top⟩).elim
        · let point : Gaussian := ⟨inner.xLower, outer.yUpper⟩
          refine ⟨point, ?_, ?_⟩
          · change OnBoxBoundary outer
              ⟨inner.xLower, outer.yUpper⟩
            exact ⟨⟨anchorInside.1, anchorInside.2.1,
                outer.y_valid, le_rfl⟩,
              Or.inr (Or.inr (Or.inr rfl))⟩
          · change inner.Contains ⟨inner.xLower, outer.yUpper⟩
            exact ⟨le_rfl, inner.x_valid,
              anchorInside.2.2.2,
              le_of_not_gt top⟩
      · refine ⟨inner.anchor, ?_, inner.contains_anchor⟩
        have bottomEqual : inner.yLower = outer.yLower :=
          le_antisymm (le_of_not_gt bottom) anchorInside.2.2.1
        exact ⟨anchorInside,
          Or.inr (Or.inr (Or.inl bottomEqual))⟩
    · let point : Gaussian := ⟨outer.xUpper, inner.yLower⟩
      refine ⟨point, ?_, ?_⟩
      · change OnBoxBoundary outer ⟨outer.xUpper, inner.yLower⟩
        exact ⟨⟨outer.x_valid, le_rfl,
            anchorInside.2.2.1, anchorInside.2.2.2⟩,
          Or.inr (Or.inl rfl)⟩
      · change inner.Contains ⟨outer.xUpper, inner.yLower⟩
        exact ⟨anchorInside.2.1,
          le_of_not_gt right, le_rfl, inner.y_valid⟩
  · refine ⟨inner.anchor, ?_, inner.contains_anchor⟩
    have leftEqual : inner.xLower = outer.xLower :=
      le_antisymm (le_of_not_gt left) anchorInside.1
    exact ⟨anchorInside, Or.inl leftEqual⟩

theorem strictInterior_of_anchor_mem_of_dominates
    (p : GaussianPolynomial) {ambient cell : Box}
    (state : WindingOneState p ambient)
    (degreePositive : 0 < p.natDegree)
    (cellRefines : cell.Refines ambient)
    (clearance : BoundaryClearance p cell)
    (anchorInside : cell.Contains state.box.anchor)
    (dominates : 2 * (anchorResidualBound p ambient state.box +
        denseLipschitzBound p ambient * state.box.diagonalSq) <
      clearance.bound) :
    state.box.StrictInterior cell := by
  cases RFAP.Boxes.Box.strictInteriorDecidable state.box cell with
  | isTrue strict => exact strict
  | isFalse notStrict =>
    obtain ⟨point, boundary, pointInside⟩ :=
      exists_boundary_point_of_anchor_mem_of_not_strictInterior
        anchorInside notStrict
    let nearby : NearbyClearPointCertificate p ambient state.box :=
      { point := point
        point_mem := cellRefines.contains boundary.1
        clearance := clearance.bound
        radiusSq := state.box.diagonalSq
        clearance_lower := clearance.lower point boundary
        anchor_distance := state.box.normSq_sub_anchor_le pointInside
        dominates := dominates }
    have zero := quadrupledBoxWinding_eq_zero_of_nearby_clear_point
      p degreePositive state.refinesAmbient state.proper nearby
    rw [state.rawWindingFour] at zero
    exact ((by decide : (4 : Int) ≠ 0) zero).elim

/-! ## Winding monotonicity inside a clear region -/

theorem region_rawWinding_ge_four_of_strictInterior
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : WindingOneState p ambient)
    (region : ClearRegion p ambient)
    (strict : state.box.StrictInterior region.box) :
    4 ≤ quadrupledBoxWinding p region.box := by
  let grid := build region.clearance state.proper strict
    (state.ambientLeftClearance.restrict region.refinesAmbient)
    (state.ambientRightClearance.restrict region.refinesAmbient)
    (state.ambientBottomClearance.restrict region.refinesAmbient)
    (state.ambientTopClearance.restrict region.refinesAmbient)
  have southwestNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.southwest.refines.trans region.refinesAmbient)
      grid.southwest.proper grid.southwest.clearance
  have westNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.west.refines.trans region.refinesAmbient)
      grid.west.proper grid.west.clearance
  have northwestNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.northwest.refines.trans region.refinesAmbient)
      grid.northwest.proper grid.northwest.clearance
  have southNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.south.refines.trans region.refinesAmbient)
      grid.south.proper grid.south.clearance
  have northNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.north.refines.trans region.refinesAmbient)
      grid.north.proper grid.north.clearance
  have southeastNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.southeast.refines.trans region.refinesAmbient)
      grid.southeast.proper grid.southeast.clearance
  have eastNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.east.refines.trans region.refinesAmbient)
      grid.east.proper grid.east.clearance
  have northeastNonnegative :=
    RFAP.GlobalNonnegativity.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.northeast.refines.trans region.refinesAmbient)
      grid.northeast.proper grid.northeast.clearance
  have additive := grid.additive
  rw [state.rawWindingFour] at additive
  omega

/-! ## One safe cut between two ordered states -/

def verticalGapCoordinate
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) : Coordinate :=
  RFAP.SafeCandidates.centralSearchValue elimination.vertical
    degreeBound less elimination.vertical_nonzero elimination.vertical_degree

theorem verticalGapCoordinate_spec
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) :
    elimination.vertical.eval (verticalGapCoordinate elimination less) ≠ 0 ∧
      a < verticalGapCoordinate elimination less ∧
      verticalGapCoordinate elimination less < b :=
  RFAP.SafeCandidates.centralSearchValue_spec elimination.vertical
    degreeBound less elimination.vertical_nonzero elimination.vertical_degree

def horizontalGapCoordinate
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) : Coordinate :=
  RFAP.SafeCandidates.centralSearchValue elimination.horizontal
    degreeBound less elimination.horizontal_nonzero
      elimination.horizontal_degree

theorem horizontalGapCoordinate_spec
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) :
    elimination.horizontal.eval (horizontalGapCoordinate elimination less) ≠
        0 ∧
      a < horizontalGapCoordinate elimination less ∧
      horizontalGapCoordinate elimination less < b :=
  RFAP.SafeCandidates.centralSearchValue_spec
    elimination.horizontal degreeBound less elimination.horizontal_nonzero
      elimination.horizontal_degree

def verticalGapClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) (ambient : Box) :
    RFAP.BoxClearance.VerticalLineClearance p ambient
      (verticalGapCoordinate elimination less) :=
  verticalOfCoprime p ambient _ (by
    simpa only [RFAP.AxisSafeCuts.verticalPathReal,
      RFAP.AxisSafeCuts.verticalPathImag] using
      elimination.vertical_coprime _
        (verticalGapCoordinate_spec elimination less).1)

def horizontalGapClearance
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {a b : Coordinate} (less : a < b) (ambient : Box) :
    RFAP.BoxClearance.HorizontalLineClearance p ambient
      (horizontalGapCoordinate elimination less) :=
  horizontalOfCoprime p ambient _ (by
    simpa only [RFAP.AxisSafeCuts.horizontalPathReal,
      RFAP.AxisSafeCuts.horizontalPathImag] using
      elimination.horizontal_coprime _
        (horizontalGapCoordinate_spec elimination less).1)

theorem region_rawWinding_ge_eight_of_x_ordered
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (region : ClearRegion p ambient) (left right : WindingOneState p ambient)
    (leftInside : left.box.StrictInterior region.box)
    (rightInside : right.box.StrictInterior region.box)
    (gap : left.box.xUpper < right.box.xLower) :
    8 ≤ quadrupledBoxWinding p region.box := by
  let cut := verticalGapCoordinate elimination gap
  have cutSpec := verticalGapCoordinate_spec elimination gap
  have cutInside : region.box.xLower ≤ cut ∧ cut ≤ region.box.xUpper :=
    ⟨((leftInside.left.trans_le left.box.x_valid).trans
        cutSpec.2.1).le,
      cutSpec.2.2.le.trans
        (right.box.x_valid.trans_lt rightInside.right).le⟩
  let leftBox := region.box.verticalLeft cut cutInside
  let rightBox := region.box.verticalRight cut cutInside
  have leftRefines : leftBox.Refines region.box :=
    region.box.verticalLeft_refines cut cutInside
  have rightRefines : rightBox.Refines region.box :=
    region.box.verticalRight_refines cut cutInside
  let cutClearance := verticalGapClearance elimination gap region.box
  let leftClearance : BoundaryClearance p leftBox := boundaryOfLines
    ((leftOfBoundary region.clearance).restrict leftRefines)
    (cutClearance.restrict leftRefines)
    ((bottomOfBoundary region.clearance).restrict leftRefines)
    ((topOfBoundary region.clearance).restrict leftRefines)
  let rightClearance : BoundaryClearance p rightBox := boundaryOfLines
    (cutClearance.restrict rightRefines)
    ((rightOfBoundary region.clearance).restrict rightRefines)
    ((bottomOfBoundary region.clearance).restrict rightRefines)
    ((topOfBoundary region.clearance).restrict rightRefines)
  let leftRegion : ClearRegion p ambient :=
    { box := leftBox
      refinesAmbient := leftRefines.trans region.refinesAmbient
      proper :=
        ⟨(leftInside.left.trans_le left.box.x_valid).trans cutSpec.2.1,
          region.proper.2⟩
      clearance := leftClearance }
  let rightRegion : ClearRegion p ambient :=
    { box := rightBox
      refinesAmbient := rightRefines.trans region.refinesAmbient
      proper :=
        ⟨cutSpec.2.2.trans
            (right.box.x_valid.trans_lt rightInside.right),
          region.proper.2⟩
      clearance := rightClearance }
  have leftStrict : left.box.StrictInterior leftRegion.box :=
    { left := leftInside.left
      right := cutSpec.2.1
      bottom := leftInside.bottom
      top := leftInside.top }
  have rightStrict : right.box.StrictInterior rightRegion.box :=
    { left := cutSpec.2.2
      right := rightInside.right
      bottom := rightInside.bottom
      top := rightInside.top }
  have leftFour := region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination left leftRegion leftStrict
  have rightFour := region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination right rightRegion rightStrict
  have additive := quadrupledBoxWinding_vertical_split
    p region.box cut cutInside
  rw [additive]
  simp only [leftRegion, leftBox] at leftFour
  simp only [rightRegion, rightBox] at rightFour
  omega

theorem region_rawWinding_ge_eight_of_y_ordered
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (region : ClearRegion p ambient) (bottom top : WindingOneState p ambient)
    (bottomInside : bottom.box.StrictInterior region.box)
    (topInside : top.box.StrictInterior region.box)
    (gap : bottom.box.yUpper < top.box.yLower) :
    8 ≤ quadrupledBoxWinding p region.box := by
  let cut := horizontalGapCoordinate elimination gap
  have cutSpec := horizontalGapCoordinate_spec elimination gap
  have cutInside : region.box.yLower ≤ cut ∧ cut ≤ region.box.yUpper :=
    ⟨((bottomInside.bottom.trans_le bottom.box.y_valid).trans
        cutSpec.2.1).le,
      cutSpec.2.2.le.trans
        (top.box.y_valid.trans_lt topInside.top).le⟩
  let lowerBox := region.box.horizontalLower cut cutInside
  let upperBox := region.box.horizontalUpper cut cutInside
  have lowerRefines : lowerBox.Refines region.box :=
    region.box.horizontalLower_refines cut cutInside
  have upperRefines : upperBox.Refines region.box :=
    region.box.horizontalUpper_refines cut cutInside
  let cutClearance := horizontalGapClearance elimination gap region.box
  let lowerClearance : BoundaryClearance p lowerBox := boundaryOfLines
    ((leftOfBoundary region.clearance).restrict lowerRefines)
    ((rightOfBoundary region.clearance).restrict lowerRefines)
    ((bottomOfBoundary region.clearance).restrict lowerRefines)
    (cutClearance.restrict lowerRefines)
  let upperClearance : BoundaryClearance p upperBox := boundaryOfLines
    ((leftOfBoundary region.clearance).restrict upperRefines)
    ((rightOfBoundary region.clearance).restrict upperRefines)
    (cutClearance.restrict upperRefines)
    ((topOfBoundary region.clearance).restrict upperRefines)
  let lowerRegion : ClearRegion p ambient :=
    { box := lowerBox
      refinesAmbient := lowerRefines.trans region.refinesAmbient
      proper :=
        ⟨region.proper.1,
          (bottomInside.bottom.trans_le bottom.box.y_valid).trans cutSpec.2.1⟩
      clearance := lowerClearance }
  let upperRegion : ClearRegion p ambient :=
    { box := upperBox
      refinesAmbient := upperRefines.trans region.refinesAmbient
      proper :=
        ⟨region.proper.1,
          cutSpec.2.2.trans (top.box.y_valid.trans_lt topInside.top)⟩
      clearance := upperClearance }
  have bottomStrict : bottom.box.StrictInterior lowerRegion.box :=
    { left := bottomInside.left
      right := bottomInside.right
      bottom := bottomInside.bottom
      top := cutSpec.2.1 }
  have topStrict : top.box.StrictInterior upperRegion.box :=
    { left := topInside.left
      right := topInside.right
      bottom := cutSpec.2.2
      top := topInside.top }
  have lowerFour := region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination bottom lowerRegion bottomStrict
  have upperFour := region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination top upperRegion topStrict
  have additive := quadrupledBoxWinding_horizontal_split
    p region.box cut cutInside
  rw [additive]
  simp only [lowerRegion, lowerBox] at lowerFour
  simp only [upperRegion, upperBox] at upperFour
  omega

theorem region_rawWinding_ge_eight_of_separated
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (region : ClearRegion p ambient) (left right : WindingOneState p ambient)
    (leftInside : left.box.StrictInterior region.box)
    (rightInside : right.box.StrictInterior region.box)
    (separated : left.box.Separated right.box) :
    8 ≤ quadrupledBoxWinding p region.box := by
  rcases separated with leftOf | rightOf | below | above
  · exact region_rawWinding_ge_eight_of_x_ordered degreeAtLeastTwo
      squarefree elimination region left right leftInside rightInside leftOf
  · exact region_rawWinding_ge_eight_of_x_ordered degreeAtLeastTwo
      squarefree elimination region right left rightInside leftInside rightOf
  · exact region_rawWinding_ge_eight_of_y_ordered degreeAtLeastTwo
      squarefree elimination region left right leftInside rightInside below
  · exact region_rawWinding_ge_eight_of_y_ordered degreeAtLeastTwo
      squarefree elimination region right left rightInside leftInside above

/-! ## Deterministic ownership and the degree bound -/

structure OwnerSelection
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Output p ambient count) (track : WindingOneTrack p ambient) where
  owner : Fin output.tracks.length
  strict :
    let radius := assignmentRadius p ambient output
    let refined := track.refine track.initial radius
      (assignmentRadius_pos p ambient output)
    refined.box.StrictInterior (output.tracks.get owner).initial.box

def selectOutputOwner
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Output p ambient count)
    (track : WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support) :
    OwnerSelection output track := by
  let radius := assignmentRadius p ambient output
  let radiusPositive := assignmentRadius_pos p ambient output
  let refined := track.refine track.initial radius radiusPositive
  have refinedSupport : refined.box.Refines output.support :=
    (track.nested track.initial radius radiusPositive).trans supported
  have anchorSupport : output.support.Contains refined.box.anchor :=
    refinedSupport.contains refined.box.contains_anchor
  let location := locatePartition output refined.box.anchor anchorSupport
  have anchorCell : location.box.Contains refined.box.anchor :=
    locatePartition_contains output refined.box.anchor anchorSupport
  have diagonal : refined.box.diagonalSq ≤ radius ^ 2 :=
    track.accurate track.initial radius radiusPositive
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  cases locationEq : location with
  | track index =>
      have anchorTrack : (output.tracks.get index).initial.box.Contains
          refined.box.anchor := by
        simpa only [locationEq, PartitionLocation.box] using anchorCell
      have strict : refined.box.StrictInterior
          (output.tracks.get index).initial.box :=
        strictInterior_of_anchor_mem_of_dominates p refined degreePositive
          (output.tracks.get index).initial.refinesAmbient
          (output.tracks.get index).initial.clearance anchorTrack
          (assignment_dominates p ambient output refined diagonal
            (partitionMargin_le_track output index))
      exact ⟨index, by simpa only [refined, radius, radiusPositive] using strict⟩
  | remainder index =>
      let region := output.remainder.get index
      have anchorRegion : region.box.Contains refined.box.anchor := by
        simpa only [region, locationEq, PartitionLocation.box] using anchorCell
      have strict : refined.box.StrictInterior region.box :=
        strictInterior_of_anchor_mem_of_dominates p refined degreePositive
          region.refinesAmbient region.clearance anchorRegion
          (assignment_dominates p ambient output refined diagonal
            (partitionMargin_le_remainder output index))
      have atLeastFour := region_rawWinding_ge_four_of_strictInterior
        degreeAtLeastTwo squarefree elimination refined region strict
      have zero := output.remainder_rawWinding_zero region
        (List.get_mem output.remainder index)
      exact (by omega : False).elim

/-- Deterministic ownership is injective on every displayed separated
family.  If two refined states selected the same output track, that
winding-one output box would contain two separated winding-one boxes and
would therefore have raw winding at least eight, contradicting its displayed
raw winding four. -/
theorem selectedOwner_injective
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count familyCount : Nat} (output : Output p ambient count)
    (family : Fin familyCount → WindingOneTrack p ambient)
    (supported : ∀ index, (family index).initial.box.Refines output.support)
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    Function.Injective (fun index =>
      (selectOutputOwner degreeAtLeastTwo squarefree elimination output
        (family index) (supported index)).owner) := by
  let radius := assignmentRadius p ambient output
  let radiusPositive := assignmentRadius_pos p ambient output
  let refined : Fin familyCount → WindingOneState p ambient := fun index =>
    (family index).refine (family index).initial radius radiusPositive
  let selection : (index : Fin familyCount) →
      OwnerSelection output (family index) := fun index =>
    selectOutputOwner degreeAtLeastTwo squarefree elimination output
      (family index) (supported index)
  let owner : Fin familyCount → Fin output.tracks.length :=
    fun index => (selection index).owner
  have ownerStrict (index : Fin familyCount) :
      (refined index).box.StrictInterior
        (output.tracks.get (owner index)).initial.box := by
    exact (selection index).strict
  intro left right ownerEqual
  change owner left = owner right at ownerEqual
  by_cases indicesEqual : left = right
  · exact indicesEqual
  · have initialSeparated := pairwise left right indicesEqual
    have refinedSeparated := initialSeparated.of_refines
      ((family left).nested (family left).initial radius radiusPositive)
      ((family right).nested (family right).initial radius radiusPositive)
    have leftInside := ownerStrict left
    have rightInside := ownerStrict right
    rw [← ownerEqual] at rightInside
    let region : ClearRegion p ambient :=
      { box := (output.tracks.get (owner left)).initial.box
        refinesAmbient :=
          (output.tracks.get (owner left)).initial.refinesAmbient
        proper := (output.tracks.get (owner left)).initial.proper
        clearance := (output.tracks.get (owner left)).initial.clearance }
    have atLeastEight := region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination region (refined left)
        (refined right) leftInside rightInside refinedSeparated
    have exactlyFour :=
      (output.tracks.get (owner left)).initial.rawWindingFour
    dsimp only [region] at atLeastEight
    exact (by omega : False).elim

theorem finite_family_card_le_output_count
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count familyCount : Nat} (output : Output p ambient count)
    (family : Fin familyCount → WindingOneTrack p ambient)
    (supported : ∀ index, (family index).initial.box.Refines output.support)
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    familyCount ≤ count := by
  let owner : Fin familyCount → Fin output.tracks.length := fun index =>
    (selectOutputOwner degreeAtLeastTwo squarefree elimination output
      (family index) (supported index)).owner
  have ownerInjective : Function.Injective owner :=
    selectedOwner_injective degreeAtLeastTwo squarefree elimination output
      family supported pairwise
  have cardinality :=
    RFAP.FinitePacking.fin_card_le_of_injective_direct
      owner ownerInjective
  rw [output.tracks_length] at cardinality
  exact cardinality

theorem isolateLargeSquare_support
    {p : GaussianPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    (RFAP.ExactIsolation.isolateLargeSquare degreeAtLeastTwo
      squarefree elimination).support =
        RFAP.GlobalWinding.largeSquareBox p := rfl

theorem finite_family_card_le_natDegree
    {p : GaussianPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {familyCount : Nat}
    (family : Fin familyCount → WindingOneTrack p
      (RFAP.GlobalWinding.largeSquareBox p))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    familyCount ≤ p.natDegree := by
  let output := RFAP.ExactIsolation.isolateLargeSquare
    degreeAtLeastTwo squarefree elimination
  apply finite_family_card_le_output_count degreeAtLeastTwo squarefree
    elimination output family
  · intro index
    rw [isolateLargeSquare_support degreeAtLeastTwo squarefree elimination]
    exact (family index).initial.refinesAmbient
  · exact pairwise

end RFAP.Maximality
