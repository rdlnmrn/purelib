module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Subedges
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Riemann.Periods.StandardPeriodAmbient
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
public import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

/-! # Actual regular-grid fragments on the SAME retained canonical child word

Pointwise rooted refinement carries original grid-line support and endpoint
containment to the actual acquired children. The original splitting and
regular-face constructors then consume a GIVEN retained child primitive
request unchanged. All partial, stationary and repeated occurrences keep
their original parent and request; no independent six-model bank, cycle
homology or physical integral identification is inferred.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes SplitPrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Branches
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {originalGrid : ClearGrid (Paths.polynomial parameter) (Ambient (Fibre.frameCurve frame))}
variable {point : Canonical} (owner : Owner ((Paths.polynomial parameter).eval point))
variable (period : PeriodWalk (curve := Fibre.frameCurve frame) originalGrid point owner basis)
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) point owner point
  (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
variable {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational}
variable {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive period.closed.traced.lineage inputCenters materialized factory)
variable (canonical : inputCenters = Centers.build period.closed.traced.lineage)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable (member : ContainsVertex originalGrid point)
variable (included : CoordinateInclusion originalGrid framed.bank.grid)

include canonical member included in
/-- The actual rooted children lie on the chosen grid's retained clear lines, including partial and stationary edges.

The original walk vertices enter that SAME grid through its actual finite
coordinate inclusion. The whole canonical center factory and genuine
parent-to-child query relations carry the original affine line certificate;
no line clearance is inferred from face containment or equal coordinates.
-/
theorem onLines : StandardPeriodGridLines.Grid.ParentsOnLines framed.bank.grid retained.parents := by
  apply StandardPeriodGridLines.Grid.ParentsOnLines.refinement
    (periodSubedges owner period retained canonical)
  rewrite [period.initial_eq]
  rewrite [period.closed.initial_parents (curve := Fibre.frameCurve frame) basis]
  exact StandardPeriodGridLines.Grid.prepared_onLines framed.bank.grid basis 0 period.closed.traced.prepared
    (included.path _ (period.closed.walk.vertices member))

include canonical in
/-- The actual rooted children retain endpoint containment in the original curve ambient.

Every new endpoint has its exact unit-interval location on an original
parent. The given original prepared path supplies both old endpoint bounds,
so the existing root-subedge operation carries those same bounds internally.
-/
theorem endpoints : EndpointsIn (Ambient (Fibre.frameCurve frame)) retained.parents := by
  apply StandardPeriodAmbient.EndpointsIn.refinement (periodSubedges owner period retained canonical)
  rewrite [period.initial_eq]
  rewrite [period.closed.initial_parents (curve := Fibre.frameCurve frame) basis]
  exact ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_endpoints
    (Fibre.frameCurve frame) basis 0 period.closed.traced.prepared

/-- The SAME child request, actual axis split, located fragments and regular incident-face assignments.

The existing exact products retain each original construction with its
whole factory. Every primitive value and constant remains owned by the
supplied request. These are geometric placements of those original
fragments, not an identification with an independent six-channel model.
-/
@[expose] def Fragments {target : Rational}
    (supplied : ControlledSumRequest retained.parents count target) : Type 2 :=
  (kept : {value : ControlledSumRequest retained.parents count target // value = supplied}) ×
  (axes : {value : PrimitiveAxes framed.bank.grid // value = PrimitiveAxes.build framed.bank.grid}) ×
  (split : {value : SplitPrimitiveRequest axes.val kept.val //
    value = SplitPrimitiveRequest.build axes.val kept.val}) ×
  (located : {value : LocatedPrimitiveSplits axes.val split.val.splits //
    value = LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
      (fun _ present => StandardPeriodAmbient.EndpointsIn.member
        (endpoints owner period retained canonical) present)}) ×
  {value : RegularPrimitiveSplits (base := framed) axes.val split.val.splits //
    value = RegularPrimitiveSplits.build located.val (onLines owner period retained canonical member included)}

/-- Split and regularly place the SAME supplied child request once on the SAME chosen grid.

The full original request is retained first. Each original constructor is
then executed once and its entire cached value/factory is passed to the
next. No child geometry, root trace, request, polynomial or source bank is
acquired again, and no desired fragment placement or sum bound is an input.
-/
def fragments {target : Rational} (supplied : ControlledSumRequest retained.parents count target) :
    Fragments owner period retained canonical member included supplied :=
  let kept : {value : ControlledSumRequest retained.parents count target // value = supplied} := ⟨supplied, rfl⟩
  let axes : {value : PrimitiveAxes framed.bank.grid // value = PrimitiveAxes.build framed.bank.grid} :=
    ⟨PrimitiveAxes.build framed.bank.grid, rfl⟩
  let split : {value : SplitPrimitiveRequest axes.val kept.val //
    value = SplitPrimitiveRequest.build axes.val kept.val} :=
    ⟨SplitPrimitiveRequest.build axes.val kept.val, rfl⟩
  let located : {value : LocatedPrimitiveSplits axes.val split.val.splits //
    value = LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
      (fun _ present => StandardPeriodAmbient.EndpointsIn.member
        (endpoints owner period retained canonical) present)} :=
    ⟨LocatedPrimitiveSplits.build framed.bank axes.val split.val.splits
      (fun _ present => StandardPeriodAmbient.EndpointsIn.member
        (endpoints owner period retained canonical) present), rfl⟩
  let regular : {value : RegularPrimitiveSplits (base := framed) axes.val split.val.splits //
    value = RegularPrimitiveSplits.build located.val (onLines owner period retained canonical member included)} :=
    ⟨RegularPrimitiveSplits.build located.val (onLines owner period retained canonical member included), rfl⟩
  ⟨kept, axes, split, located, regular⟩

/-- One acquired child request and its actual fragment cache, retaining both whole construction factories.

Strict parameter ordering is derived from the given geometry's original
child blocks. The request's original target, minimum, cover and model
indices remain retained for source comparisons and sheet assignments.
-/
@[expose] def AcquiredFragments (target : Rational) (targetPositive : 0 < target) (minimum : Nat) : Type 2 :=
  (request : {value : ControlledSumRequest retained.parents count target //
    value = ControlledSumRequest.acquire retained.covered retained.parents_proper target targetPositive minimum}) ×
  {value : Fragments owner period retained canonical member included request.val //
    value = fragments owner period retained canonical member included request.val}

/-- Acquire one request and split that same cached request once on the retained child geometry.

The original child ordering certificates supply properness internally.
Both complete results and their factories are retained; no source bank,
child geometry or signed-root comparison is prepared by this operation.
-/
def acquireFragments (target : Rational) (targetPositive : 0 < target) (minimum : Nat) :
    AcquiredFragments owner period retained canonical member included target targetPositive minimum :=
  let request : {value : ControlledSumRequest retained.parents count target //
      value = ControlledSumRequest.acquire retained.covered retained.parents_proper target targetPositive minimum} :=
    ⟨ControlledSumRequest.acquire retained.covered retained.parents_proper target targetPositive minimum, rfl⟩
  let actual : {value : Fragments owner period retained canonical member included request.val //
      value = fragments owner period retained canonical member included request.val} :=
    ⟨fragments owner period retained canonical member included request.val, rfl⟩
  ⟨request, actual⟩

namespace AcquiredFragments

variable {owner period retained canonical member included}
variable {target : Rational} {targetPositive : 0 < target} {minimum : Nat}
variable (actual : AcquiredFragments owner period retained canonical member included target targetPositive minimum)

/-- Read the same once-acquired complete child request and all its original model data. -/
@[expose] def request : ControlledSumRequest retained.parents count target := actual.1.val

/-- Read the actual fragment cache on that same acquired request. -/
@[expose] def fragments : Fragments owner period retained canonical member included actual.request := actual.2.val

/-- The stored request retains its whole original acquisition factory with internally derived properness. -/
theorem request_eq : actual.request =
    ControlledSumRequest.acquire retained.covered retained.parents_proper target targetPositive minimum :=
  actual.1.property

/-- The stored fragment cache is the original constructor on the same acquired request. -/
theorem fragments_eq : actual.fragments =
    Geometry.fragments owner period retained canonical member included actual.request := actual.2.property

end AcquiredFragments

namespace Fragments

variable {owner period retained canonical member included}
variable {target : Rational} {supplied : ControlledSumRequest retained.parents count target}
variable (actual : Fragments owner period retained canonical member included supplied)

/-- Read the SAME full original child request, including all independent primitive observations and constants. -/
@[expose] def request : ControlledSumRequest retained.parents count target := actual.1.val

/-- The retained full request is exactly the supplied original value. -/
theorem request_eq : actual.request = supplied := actual.1.property

/-- Read the actual selected grid axes without computing another coordinate list. -/
@[expose] def axes : PrimitiveAxes framed.bank.grid := actual.2.1.val

/-- The retained axes are exactly the original chosen-grid coordinate extraction. -/
theorem axes_eq : actual.axes = PrimitiveAxes.build framed.bank.grid := actual.2.1.property

/-- Read the actual original fragment increments and parameter partitions. -/
@[expose] def split : SplitPrimitiveRequest actual.axes actual.request := actual.2.2.1.val

/-- The whole split is exactly the original constructor on the SAME retained request and axes. -/
theorem split_eq : actual.split = SplitPrimitiveRequest.build actual.axes actual.request := actual.2.2.1.property

/-- Read the actual original midpoint-located fragment cells. -/
@[expose] def located : LocatedPrimitiveSplits actual.axes actual.split.splits := actual.2.2.2.1.val

/-- The located fragments retain their original whole placement factory on the SAME grid and split. -/
theorem located_eq : actual.located = LocatedPrimitiveSplits.build framed.bank actual.axes actual.split.splits
    (fun _ present => StandardPeriodAmbient.EndpointsIn.member
      (endpoints owner period retained canonical) present) := actual.2.2.2.1.property

/-- Read the actual regular incident faces for those SAME original fragments. -/
@[expose] def regular : RegularPrimitiveSplits (base := framed) actual.axes actual.split.splits :=
  actual.2.2.2.2.val

/-- The regular faces retain their whole original factory with the internally derived SAME-grid support. -/
theorem regular_eq : actual.regular = RegularPrimitiveSplits.build actual.located
    (onLines owner period retained canonical member included) := actual.2.2.2.2.property

/-- The original request's exact finite primitive sum is preserved by all retained oriented fragments. -/
theorem original_sum : actual.split.sum = supplied.primitiveSum :=
  actual.split.original_sum.trans (congrArg (fun value : ControlledSumRequest retained.parents count target =>
    value.primitiveSum) actual.request_eq)

/-- Each retained numerical fragment is one original ordered fragment occurrence. -/
theorem increments_length : actual.split.increments.length = actual.split.count := actual.split.length_eq

end Fragments

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
