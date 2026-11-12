module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
public import Purelib.Riemann.RootContinuation.RootContinuationCongruence.Advance
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Tactic.Ring

/-! # Unique signed advances on the paid strip grid

Each horizontal or vertical edge binds one actual Owner.advance result and
one original comparison to its SAME shared finishing vertex Owner. Both
initial-box identities and the movement payment are derived from the
retained vertex factories and joint grid. Cell readers reuse those actual
edge caches; they do not assert whole Chain equality or a realized cylinder.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.RootContinuation.RootContinuationCongruence (Advance advanceTo)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

/-- Each nonnegative summand is bounded by twice their actual sum. -/
private theorem le_twice_sum (first last : Rational) (firstNonnegative : 0 ≤ first)
    (lastNonnegative : 0 ≤ last) : first ≤ 2 * (first + last) := by
  have added : first ≤ first + last := by
    calc
      first = first + 0 := by ring1
      _ ≤ _ := Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl first) lastNonnegative
  have nonnegative : 0 ≤ first + last := by
    calc
      0 = 0 + 0 := by ring1
      _ ≤ _ := Order.Arithmetic.add_le_add_direct firstNonnegative lastNonnegative
  calc
    first ≤ first + last := added
    _ = 1 * (first + last) := by ring1
    _ ≤ 2 * (first + last) := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (1 : Rational) ≤ 2) nonnegative

/-- Scale one retained unit quarter-radius without changing its finite stage. -/
private theorem scaled_quarter (scale : Rational) (stage : Nat) :
    scale * Geometric.Basic.quarterRadius 1 stage = Geometric.Basic.quarterRadius scale stage := by
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- One eighth of a positive original clearance is strictly below that clearance. -/
private theorem eighth_lt {clearance : Rational} (positive : 0 < clearance) : clearance / 8 < clearance := by
  apply (Order.Field.div_lt_iff_pos (by decide +kernel : (0 : Rational) < 8)).mpr
  calc
    clearance = clearance * 1 := by ring1
    _ < clearance * 8 := Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by decide +kernel)

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {range : Range patch} {budget : FixedRootBoxBudget.Budget patch.base.seed.owner}
    {factory : budget = range.seedBudget}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish}
    {firstInside : patch.box.Contains start} {lastInside : patch.box.Contains finish}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ range.stripBound}
    {firstPath lastPath : PathData budget budget}
    {firstDepth lastDepth : Nat} {left right : Endpoint}
    {grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right}
    (cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid)

namespace Vertices

/-- Both actual time-edge vertex factories give equality of their complete original initial boxes. -/
theorem time_boxes (timeIndex : Fin cached.times.length) (spaceIndex : Fin (left :: cached.spaces).length) :
    (cached.owner timeIndex.castSucc spaceIndex).track.initial.box =
      (cached.owner timeIndex.succ spaceIndex).track.initial.box :=
  (cached.owner_box timeIndex.castSucc spaceIndex).trans (cached.owner_box timeIndex.succ spaceIndex).symm

/-- Both actual spatial-edge vertex factories give equality of their complete original initial boxes. -/
theorem space_boxes (timeIndex : Fin (left :: cached.times).length) (spaceIndex : Fin cached.spaces.length) :
    (cached.owner timeIndex spaceIndex.castSucc).track.initial.box =
      (cached.owner timeIndex spaceIndex.succ).track.initial.box :=
  (cached.owner_box timeIndex spaceIndex.castSucc).trans (cached.owner_box timeIndex spaceIndex.succ).symm

variable (ordered : left.parameter ≤ right.parameter)
    (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

include ordered in
/-- The SAME retained temporal target word pays its full squared-Lipschitz edge scale before new observations.

Only the actual time occurrence and original selected quarter-radius are
used. No spatial occurrence or endpoint spatial-path factory is needed.
-/
theorem time_scale_lt (timeIndex : Fin cached.times.length) :
    (Norm.Basic.normSq increment * range.coefficient) *
      (((left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt).parameter -
        ((left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt).parameter) ^ 2 <
      budget.clearance / 8 := by
  let selected := cached.original.selection
  let source := (left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt
  let target := (left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt
  let original := dyadicIndexOf selected.stage left right cached.times cached.times_eq timeIndex
  let edge := (dyadicEdges selected.stage left right)[original.val]'original.isLt
  have sourceEq := dyadic_source_of_eq selected.stage left right cached.times cached.times_eq timeIndex
  have targetEq := dyadic_target_of_eq selected.stage left right cached.times cached.times_eq timeIndex
  have widths : (target.parameter - source.parameter) ^ 2 =
      (edge.right.parameter - edge.left.parameter) ^ 2 :=
    congrArg₂ (fun first last : Endpoint => (last.parameter - first.parameter) ^ 2) sourceEq targetEq
  have widthBound := widths.trans_le (dyadicEdges_width_le selected.stage selected.stage (Nat.le_refl _)
    left right ordered edge (List.getElem_mem original.isLt))
  have temporalNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative
  have scaleBound := le_twice_sum (Norm.Basic.normSq increment * range.coefficient)
    (spatialScale (budget := budget) firstPath lastPath) temporalNonnegative
    (spatialScale_nonnegative (budget := budget) firstPath lastPath)
  have paid := (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthBound temporalNonnegative).trans_eq
    (scaled_quarter _ selected.stage)
  exact (paid.trans (Geometric.Basic.quarterRadius_scale_mono scaleBound selected.stage)).trans_lt
    (selected.later_accurate (Nat.le_refl selected.stage))

include ordered in
/-- The SAME retained spatial target word pays its full squared-Lipschitz edge scale before new observations.

The actual common spatial depth and both original path scales determine the
payment. No temporal occurrence or endpoint spatial-path factory is needed.
-/
theorem space_scale_lt (spaceIndex : Fin cached.spaces.length) :
    spatialScale (budget := budget) firstPath lastPath *
      (((left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt).parameter -
        ((left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt).parameter) ^ 2 <
      budget.clearance / 8 := by
  let selected := cached.original.selection
  let depth := firstDepth + (lastDepth + selected.stage)
  let source := (left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt
  let target := (left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt
  let original := dyadicIndexOf depth left right cached.spaces cached.spaces_eq spaceIndex
  let edge := (dyadicEdges depth left right)[original.val]'original.isLt
  have sourceEq := dyadic_source_of_eq depth left right cached.spaces cached.spaces_eq spaceIndex
  have targetEq := dyadic_target_of_eq depth left right cached.spaces cached.spaces_eq spaceIndex
  have widths : (target.parameter - source.parameter) ^ 2 =
      (edge.right.parameter - edge.left.parameter) ^ 2 :=
    congrArg₂ (fun first last : Endpoint => (last.parameter - first.parameter) ^ 2) sourceEq targetEq
  have widthBound := widths.trans_le (dyadicEdges_width_le depth selected.stage cached.original.spatialMinimum
    left right ordered edge (List.getElem_mem original.isLt))
  have temporalNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative
  have scaleBound : spatialScale (budget := budget) firstPath lastPath ≤
      jointScale (range := range) (budget := budget) increment firstPath lastPath :=
    (le_twice_sum (spatialScale (budget := budget) firstPath lastPath)
      (Norm.Basic.normSq increment * range.coefficient)
      (spatialScale_nonnegative (budget := budget) firstPath lastPath) temporalNonnegative).trans_eq (by
        unfold jointScale
        ring1)
  have paid := (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthBound
    (spatialScale_nonnegative (budget := budget) firstPath lastPath)).trans_eq (scaled_quarter _ selected.stage)
  exact (paid.trans (Geometric.Basic.quarterRadius_scale_mono scaleBound selected.stage)).trans_lt
    (selected.later_accurate (Nat.le_refl selected.stage))

include ordered in
/-- The actual selected temporal edge movement pays one eighth of the original common clearance. -/
private theorem time_accurate (timeIndex : Fin cached.times.length)
    (spaceIndex : Fin (left :: cached.spaces).length) :
    Norm.Basic.normSq
      (radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt)
          ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt) -
        radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt)
          ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt)) < budget.clearance / 8 :=
  (range.temporal_variation segment firstInside lastInside increment
    ((left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt).parameter
    ((left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt).parameter
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).parameter
    ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt).inside).trans_lt
      (time_scale_lt cached ordered timeIndex)

include ordered firstFactory lastFactory in
/-- The selected spatial edge movement pays one eighth of the SAME original common clearance. -/
private theorem space_accurate (timeIndex : Fin (left :: cached.times).length)
    (spaceIndex : Fin cached.spaces.length) :
    Norm.Basic.normSq
      (radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.val]'timeIndex.isLt)
          ((left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt) -
        radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.val]'timeIndex.isLt)
          ((left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt)) < budget.clearance / 8 :=
  (spatial_variation range budget factory segment firstInside lastInside increment admitted
    zeroInside oneInside firstPath lastPath firstFactory lastFactory
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).parameter
    ((left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt).parameter
    ((left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt).parameter
    ((left :: cached.times)[timeIndex.val]'timeIndex.isLt).inside
    ((left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt).inside
    ((left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt).inside).trans_lt
      (space_scale_lt cached ordered spaceIndex)

include ordered in
/-- The actual time-edge movement is admitted by its SAME stored source Owner's original contour clearance. -/
theorem time_small (timeIndex : Fin cached.times.length) (spaceIndex : Fin (left :: cached.spaces).length) :
    Norm.Basic.normSq
      (radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.castSucc.val]'timeIndex.castSucc.isLt)
          ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt) -
        radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.succ.val]'timeIndex.succ.isLt)
          ((left :: cached.spaces)[spaceIndex.val]'spaceIndex.isLt)) <
      (cached.owner timeIndex.castSucc spaceIndex).track.initial.clearance.bound := by
  rewrite [cached.owner_clearance timeIndex.castSucc spaceIndex]
  have small := time_accurate cached ordered timeIndex spaceIndex
  have ceiling := eighth_lt budget.clearance_positive
  exact ⟨Order.Basic.le_trans _ _ _ small.1 ceiling.1,
    fun reverse => ceiling.2 (Order.Basic.le_trans _ _ _ reverse small.1)⟩

include ordered firstFactory lastFactory in
/-- The actual spatial-edge movement is admitted by its SAME stored source Owner's original contour clearance. -/
theorem space_small (timeIndex : Fin (left :: cached.times).length) (spaceIndex : Fin cached.spaces.length) :
    Norm.Basic.normSq
      (radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.val]'timeIndex.isLt)
          ((left :: cached.spaces)[spaceIndex.castSucc.val]'spaceIndex.castSucc.isLt) -
        radicand (segment := segment) increment
          ((left :: cached.times)[timeIndex.val]'timeIndex.isLt)
          ((left :: cached.spaces)[spaceIndex.succ.val]'spaceIndex.succ.isLt)) <
      (cached.owner timeIndex spaceIndex.castSucc).track.initial.clearance.bound := by
  rewrite [cached.owner_clearance timeIndex spaceIndex.castSucc]
  have small := space_accurate cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex
  have ceiling := eighth_lt budget.clearance_positive
  exact ⟨Order.Basic.le_trans _ _ _ small.1 ceiling.1,
    fun reverse => ceiling.2 (Order.Basic.le_trans _ _ _ reverse small.1)⟩

/-- The original advance/comparison cache on one actual time edge and one shared spatial vertex. -/
@[expose] def TimeEdge (timeIndex : Fin cached.times.length) (spaceIndex : Fin (left :: cached.spaces).length) :=
  Advance (cached.owner timeIndex.castSucc spaceIndex) (cached.owner timeIndex.succ spaceIndex)
    (time_boxes cached timeIndex spaceIndex)
    (time_small cached ordered timeIndex spaceIndex)

/-- The original advance/comparison cache on one actual spatial edge and one shared time vertex. -/
@[expose] def SpaceEdge (timeIndex : Fin (left :: cached.times).length) (spaceIndex : Fin cached.spaces.length) :=
  Advance (cached.owner timeIndex spaceIndex.castSucc) (cached.owner timeIndex spaceIndex.succ)
    (space_boxes cached timeIndex spaceIndex)
    (space_small cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)

/-- One unique time-edge cache at every original edge/shared-vertex occurrence. -/
@[expose] def TimeEdges := DependentProduct cached.times (fun timeIndex =>
  DependentProduct (left :: cached.spaces) (fun spaceIndex =>
    TimeEdge cached ordered timeIndex spaceIndex))

/-- One unique spatial-edge cache at every original shared-vertex/edge occurrence. -/
@[expose] def SpaceEdges := DependentProduct (left :: cached.times) (fun timeIndex =>
  DependentProduct cached.spaces (fun spaceIndex =>
    SpaceEdge cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex))

/-- Bind one genuine advance and one original signed comparison per unique time edge.

Both source and target Owners are projected from the SAME existing vertex
table. The original advance refines the source box, and both vertex factories
identify that box with the exact target box before comparison.
-/
def timeEdges : TimeEdges cached ordered :=
  DependentProduct.ofFn cached.times (fun timeIndex =>
    DependentProduct.ofFn (left :: cached.spaces) (fun spaceIndex =>
      let first := cached.owner timeIndex.castSucc spaceIndex
      let last := cached.owner timeIndex.succ spaceIndex
      advanceTo first last (time_boxes cached timeIndex spaceIndex)
        (time_small cached ordered timeIndex spaceIndex)))

/-- Bind one genuine advance and one original signed comparison per unique spatial edge. -/
def spaceEdges : SpaceEdges cached ordered zeroInside oneInside firstFactory lastFactory :=
  DependentProduct.ofFn (left :: cached.times) (fun timeIndex =>
    DependentProduct.ofFn cached.spaces (fun spaceIndex =>
      let first := cached.owner timeIndex spaceIndex.castSucc
      let last := cached.owner timeIndex spaceIndex.succ
      advanceTo first last (space_boxes cached timeIndex spaceIndex)
        (space_small cached ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex)))

/-- The SAME whole shared vertex cache and both unique original edge tables, retaining their complete factories. -/
@[expose] def Edges :=
  (original : { value : Vertices range budget factory segment firstInside lastInside increment admitted
      firstPath lastPath grid // value = cached }) ×
  (_horizontal : { value : TimeEdges original.val ordered //
      value = timeEdges original.val ordered }) ×
    { vertical : SpaceEdges original.val ordered zeroInside oneInside firstFactory lastFactory //
      vertical = spaceEdges original.val ordered zeroInside oneInside firstFactory lastFactory }

/-- Retain the GIVEN shared vertices and construct each of the two unique edge tables once. -/
def edges : Edges cached ordered zeroInside oneInside firstFactory lastFactory :=
  let horizontal := timeEdges cached ordered
  let vertical := spaceEdges cached ordered zeroInside oneInside firstFactory lastFactory
  ⟨⟨cached, rfl⟩, ⟨horizontal, rfl⟩, ⟨vertical, rfl⟩⟩

namespace Edges

variable {cached ordered zeroInside oneInside firstFactory lastFactory}
    (retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory)

/-- Read the SAME complete original shared vertex cache. -/
@[expose] def original : Vertices range budget factory segment firstInside lastInside increment admitted
    firstPath lastPath grid := retained.1.val

/-- The whole original shared vertex cache is the GIVEN value, without any ownerAt replay. -/
theorem original_eq : retained.original = cached := retained.1.property

/-- Read the SAME unique table of original time-edge advances and comparisons. -/
@[expose] def horizontal : TimeEdges retained.original ordered :=
  retained.2.1.val

/-- The entire time-edge table retains its original one-pass materialization factory. -/
theorem horizontal_eq : retained.horizontal =
    timeEdges retained.original ordered := retained.2.1.property

/-- Read the SAME unique table of original spatial-edge advances and comparisons. -/
@[expose] def vertical : SpaceEdges retained.original ordered zeroInside oneInside firstFactory lastFactory :=
  retained.2.2.val

/-- The entire spatial-edge table retains its original one-pass materialization factory. -/
theorem vertical_eq : retained.vertical =
    spaceEdges retained.original ordered zeroInside oneInside firstFactory lastFactory := retained.2.2.property

/-- Read one actual time-edge cache without running its advance or comparison again. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    TimeEdge retained.original ordered timeIndex spaceIndex :=
  DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times retained.horizontal timeIndex) spaceIndex

/-- Read one actual spatial-edge cache without running its advance or comparison again. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    SpaceEdge retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex spaceIndex :=
  DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) retained.vertical timeIndex) spaceIndex

/-- Equal bounded time-edge occurrences read the SAME complete advance/comparison cache. -/
theorem time_index_heq {firstTime lastTime : Fin retained.original.times.length}
    {firstSpace lastSpace : Fin (left :: retained.original.spaces).length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (retained.time firstTime firstSpace) (retained.time lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

/-- Equal bounded spatial-edge occurrences read the SAME complete advance/comparison cache. -/
theorem space_index_heq {firstTime lastTime : Fin (left :: retained.original.times).length}
    {firstSpace lastSpace : Fin retained.original.spaces.length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (retained.space firstTime firstSpace) (retained.space lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

/-- The two actual ordered edge routes on one retained cell, with all four signed advance handoffs. -/
@[expose] def CellRoutes (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) :=
  TimeEdge retained.original ordered timeIndex spaceIndex.castSucc ×
  SpaceEdge retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex.succ spaceIndex ×
  SpaceEdge retained.original ordered zeroInside oneInside firstFactory lastFactory timeIndex.castSucc spaceIndex ×
  TimeEdge retained.original ordered timeIndex spaceIndex.succ

/-- Read both original cell routes from the SAME unique edge tables, preserving each actual signed handoff. -/
def cellRoutes (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) : retained.CellRoutes timeIndex spaceIndex :=
  ⟨retained.time timeIndex spaceIndex.castSucc, retained.space timeIndex.succ spaceIndex,
    retained.space timeIndex.castSucc spaceIndex, retained.time timeIndex spaceIndex.succ⟩

/-- Both actual cell routes and their derived finishing-root comparison through the SAME shared upper-right Owner. -/
@[expose] def Cell (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) :=
  (routes : { value : retained.CellRoutes timeIndex spaceIndex //
      value = retained.cellRoutes timeIndex spaceIndex }) ×
    { compared : Approximation.Gaussian.Equivalence.NamedEquivalent
        (ownerRootName routes.val.2.1.moved.parameterNonzero routes.val.2.1.moved)
        (ownerRootName routes.val.2.2.2.moved.parameterNonzero routes.val.2.2.2.moved) //
      compared = routes.val.2.1.compared.trans routes.val.2.2.2.compared.symm }

/-- Compare the two genuine final advances using their retained handoffs to one SAME cached finishing vertex.

The first route's intermediate handoff and the second route's intermediate
handoff remain in the retained four-edge tuple. They are not Owner identity,
whole Chain equality or vanishing stationary primitive increments.
-/
def cell (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) : retained.Cell timeIndex spaceIndex :=
  let routes := retained.cellRoutes timeIndex spaceIndex
  let compared := routes.2.1.compared.trans routes.2.2.2.compared.symm
  ⟨⟨routes, rfl⟩, ⟨compared, rfl⟩⟩

namespace Cell

variable {retained} {timeIndex : Fin retained.original.times.length}
    {spaceIndex : Fin retained.original.spaces.length} (result : retained.Cell timeIndex spaceIndex)

/-- Read the SAME four retained edge caches, including both actual intermediate signed handoffs. -/
@[expose] def routes : retained.CellRoutes timeIndex spaceIndex := result.1.val

/-- The full route tuple consists of the original shared edge-table outputs. -/
theorem routes_eq : result.routes = retained.cellRoutes timeIndex spaceIndex := result.1.property

/-- Read the SAME operational comparison between the two actual final advanced Owners. -/
@[expose] def compared : Approximation.Gaussian.Equivalence.NamedEquivalent
    (ownerRootName result.routes.2.1.moved.parameterNonzero result.routes.2.1.moved)
    (ownerRootName result.routes.2.2.2.moved.parameterNonzero result.routes.2.2.2.moved) := result.2.val

/-- The final comparison is exactly the composition of both GIVEN finishing handoffs through their shared vertex. -/
theorem compared_eq : result.compared =
    result.routes.2.1.compared.trans result.routes.2.2.2.compared.symm := result.2.property

end Cell

end Edges

end Vertices

variable (grid) (ordered : left.parameter ≤ right.parameter)
    (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

/-- One actual shared vertex construction followed by both unique edge constructions on those SAME cached Owners. -/
@[expose] def Preparation :=
  (cached : { value : Vertices range budget factory segment firstInside lastInside increment admitted
      firstPath lastPath grid //
    value = vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid }) ×
    Vertices.Edges cached.val ordered zeroInside oneInside firstFactory lastFactory

/-- Bind the complete vertex cache once, then construct both unique edge tables on those exact outputs.

Cell readers consume this retained finite preparation without acquiring any
additional vertex or advancing an edge again. Root comparisons preserve
their own actual refinement work; stationary handoffs remain distinct.
-/
def prepare : Preparation grid ordered zeroInside oneInside firstFactory lastFactory :=
  let cached := vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid
  let compared := Vertices.edges cached ordered zeroInside oneInside firstFactory lastFactory
  ⟨⟨cached, rfl⟩, compared⟩

namespace Preparation

variable {grid ordered zeroInside oneInside firstFactory lastFactory}
    (retained : Preparation grid ordered zeroInside oneInside firstFactory lastFactory)

/-- Read the SAME complete vertex cache, including the original grid and both endpoint words. -/
@[expose] def shared : Vertices range budget factory segment firstInside lastInside increment admitted
    firstPath lastPath grid := retained.1.val

/-- The complete shared vertex cache retains its original one-call construction factory. -/
theorem shared_eq : retained.shared =
    vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid :=
  retained.1.property

/-- Read both SAME unique edge tables and the retained original vertex cache beside them. -/
@[expose] def edges : Vertices.Edges retained.shared ordered zeroInside oneInside firstFactory lastFactory :=
  retained.2

end Preparation

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid

end
