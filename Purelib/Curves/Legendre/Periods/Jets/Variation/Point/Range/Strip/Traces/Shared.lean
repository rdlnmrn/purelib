module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Realizations
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Edges
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Corners
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Links
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Between

/-! # One actual shared-corner realization of both retained strip edge tables

All original link/request/advance/handoff caches are retained as data.
Endpoint requirements and every bounded corner maximum precede the one
native reading per coarse corner. Both temporal/spatial consumers use that
SAME complete corner bank and construct only their genuine interiors.
No reverse trace, different-polynomial concatenation or face filling is
asserted by the shared endpoint incidence.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Links (Requirements)

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
    {cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid}
    {ordered : left.parameter ≤ right.parameter} {zeroInside : Inside 0} {oneInside : Inside 1}
    {firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside}
    {lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside}
    (retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory)

/-- Both original edge tables realized with one SAME retained incoming reading per bounded coarse corner.

The entire original link prefix, both endpoint-floor tables, all incidence
maxima, the native corner bank and both actual realization tables remain
separate data fields with their complete construction factories.
-/
@[expose] def Shared :=
  (linked : { value : Links retained // value = Edges.links (retained := retained) }) ×
  (required : { value : Requirements (linked := linked.val) //
    value = Links.requirements (linked := linked.val) }) ×
  (demanded : { value : Requirements.Demands (linked := linked.val) (required := required.val) //
    value = Requirements.demands (linked := linked.val) (required := required.val) }) ×
  (targeted : { value : Requirements.Targets (linked := linked.val)
      (required := required.val) (demanded := demanded.val) //
    value = Requirements.targets (linked := linked.val)
      (required := required.val) (demanded := demanded.val) }) ×
  (observed : { value : Requirements.Readings (linked := linked.val)
      (required := required.val) (demanded := demanded.val) (targeted := targeted.val) //
    value = Requirements.readings (linked := linked.val)
      (required := required.val) (demanded := demanded.val) (targeted := targeted.val) }) ×
    { actual : Requirements.Readings.Realizations (linked := linked.val)
        (required := required.val) (demanded := demanded.val) (targeted := targeted.val) (observed := observed.val) //
      actual = Requirements.Readings.realize (linked := linked.val)
        (required := required.val) (demanded := demanded.val) (targeted := targeted.val) (observed := observed.val) }

/-- Prepare all actual links and floors, sample each coarse corner once, then realize only the edge interiors.

No source/member/query producer or ownerAt is called; the GIVEN419
endpoint advances are retained without replay.
The original prefix has its genuine midpoint/tail/comparison work. Both
native corner and interior observations are counted new work; the two
incoming corner readings are reused verbatim in each incident edge.
-/
def share : Shared retained :=
  let linked := Edges.links (retained := retained)
  let required := Links.requirements (linked := linked)
  let demanded := Requirements.demands (linked := linked) (required := required)
  let targeted := Requirements.targets (linked := linked) (required := required) (demanded := demanded)
  let observed := Requirements.readings (linked := linked) (required := required)
    (demanded := demanded) (targeted := targeted)
  let actual := Requirements.Readings.realize (linked := linked)
    (required := required) (demanded := demanded) (targeted := targeted) (observed := observed)
  ⟨⟨linked, rfl⟩, ⟨required, rfl⟩, ⟨demanded, rfl⟩, ⟨targeted, rfl⟩, ⟨observed, rfl⟩, ⟨actual, rfl⟩⟩

namespace Shared

variable {retained} (shared : Shared retained)

/-- Read the SAME entire retained request/link/advance/handoff preparation. -/
@[expose] def links : Links retained := shared.1.val

/-- The full link preparation keeps its original one-call factory on the GIVEN419 cache. -/
theorem links_eq : shared.links = Edges.links (retained := retained) := shared.1.property

/-- Read the SAME cached temporal/spatial endpoint requirements. -/
@[expose] def required : Requirements (linked := shared.links) := shared.2.1.val

/-- The complete endpoint requirements keep their original one-pass factories. -/
theorem required_eq : shared.required = Links.requirements (linked := shared.links) := shared.2.1.property

/-- Read the SAME whole pre-sampling corner-maximum table. -/
@[expose] def demanded : Requirements.Demands (linked := shared.links) (required := shared.required) :=
  shared.2.2.1.val

/-- The complete corner-maximum table keeps its factory on those SAME endpoint requirements. -/
theorem demanded_eq : shared.demanded =
    Requirements.demands (linked := shared.links) (required := shared.required) := shared.2.2.1.property

/-- Read ALL the SAME genuine original tails and final native indices retained before the first displayed sample. -/
@[expose] def targeted : Requirements.Targets (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) := shared.2.2.2.1.val

/-- The whole corner target table retains its original one-pass factory before any displayed reading. -/
theorem targeted_eq : shared.targeted = Requirements.targets (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) := shared.2.2.2.1.property

/-- Read the SAME whole native corner bank, including every original tail and one sampled reading. -/
@[expose] def observed : Requirements.Readings (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) (targeted := shared.targeted) := shared.2.2.2.2.1.val

/-- The complete corner bank keeps its one-pass factory after the SAME all-corner maxima. -/
theorem observed_eq : shared.observed = Requirements.readings (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) (targeted := shared.targeted) :=
  shared.2.2.2.2.1.property

/-- Read both SAME actual edge realization tables on that identical incoming corner bank. -/
@[expose] def actual : Requirements.Readings.Realizations (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) := shared.2.2.2.2.2.val

/-- Both realization tables keep their original once-built factories on the SAME retained corner readings. -/
theorem actual_eq : shared.actual = Requirements.Readings.realize (linked := shared.links)
    (required := shared.required) (demanded := shared.demanded) (targeted := shared.targeted)
      (observed := shared.observed) := shared.2.2.2.2.2.property

/-- Read the SAME actual temporal realization at its original bounded occurrence. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Requirements.Readings.TimeResult (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex :=
  Requirements.Readings.Realizations.time (realized := shared.actual) timeIndex spaceIndex

/-- Read the SAME actual spatial realization at its original bounded occurrence. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Requirements.Readings.SpaceResult (linked := shared.links) (required := shared.required)
      (demanded := shared.demanded) (targeted := shared.targeted) (observed := shared.observed) timeIndex spaceIndex :=
  Requirements.Readings.Realizations.space (realized := shared.actual) timeIndex spaceIndex

/-- Both actual cell routes meet at the same four stored corner values; all original stationary links remain.

Each complete edge realization keeps its own polynomial and checked data.
These endpoint equations do not concatenate different-Q Chains or fill a
parameter cell.
-/
theorem cell_values (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (shared.time timeIndex spaceIndex.castSucc).val.realization.first.value =
        (shared.space timeIndex.castSucc spaceIndex).val.realization.first.value ∧
    (shared.time timeIndex spaceIndex.castSucc).val.realization.last.value =
        (shared.space timeIndex.succ spaceIndex).val.realization.first.value ∧
    (shared.space timeIndex.castSucc spaceIndex).val.realization.last.value =
        (shared.time timeIndex spaceIndex.succ).val.realization.first.value ∧
    (shared.space timeIndex.succ spaceIndex).val.realization.last.value =
        (shared.time timeIndex spaceIndex.succ).val.realization.last.value :=
  Requirements.Readings.Realizations.cell_values (realized := shared.actual) timeIndex spaceIndex

end Shared

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges

end
