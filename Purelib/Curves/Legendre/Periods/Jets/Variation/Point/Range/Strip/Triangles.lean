module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
public import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy.Triangle
public import Purelib.Riemann.Paths.OwnerTraceReadings.Trace
public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Dense.Bivariate.Specialization
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Topology.Mesh.CoordinateTriangulation

/-! # One genuinely root-paid local rectangle with two actual root triangles

A NEW finite selection pays both original clearance and the signed-root
relative movement target. Four original ownerAt outputs, four residual
requests and four native readings are materialized before either triangle.
Both triangles consume those SAME caches and original q/restriction tables.
This local construction does not replace an old strip bank or construct a
perimeter-conforming collar or ordered cylinder.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Bivariate.Basic (GaussianBivariate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.RootContinuation.SquareRootProvenance
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.Paths.OwnerTracePath (OwnerReading)
open Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (range : Range patch) (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (factory : budget = range.seedBudget)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (firstInside : patch.box.Contains start) (lastInside : patch.box.Contains finish)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (firstPath lastPath : PathData budget budget)

/-- The genuine additional root-relative target, keeping the original clearance target as a separate constraint. -/
@[expose] def triangleTarget : Rational := min (budget.clearance / 8) (traceAllowance patch.rootLower)

/-- Both original positive clearances make the NEW displayed triangle target strictly positive. -/
theorem triangleTarget_positive : 0 < triangleTarget (patch := patch) budget :=
  Order.Basic.lt_min
    (Order.Field.div_pos_direct budget.clearance_positive
      (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide +kernel)))
    (traceAllowance_positive patch.rootLower_positive)

/-- Select a NEW actual joint depth at the root-relative target, without modifying an existing grid or its selection. -/
def triangleSelection (minimum : Nat) :
    Geometric.Search.Selection (jointScale (range := range) (budget := budget) increment firstPath lastPath)
      minimum (triangleTarget (patch := patch) budget) :=
  Geometric.Search.Selection.build _
    (jointScale_nonnegative (range := range) (budget := budget) increment firstPath lastPath) minimum _
    (triangleTarget_positive (patch := patch) budget)

namespace RootTriangles

/-- The complete actual NEW selector and its original one-call factory. -/
@[expose] def Selected (minimum : Nat) : Type :=
  { value : Geometric.Search.Selection
      (jointScale (range := range) (budget := budget) increment firstPath lastPath)
      minimum (triangleTarget (patch := patch) budget) //
    value = triangleSelection range budget increment firstPath lastPath minimum }

/-- Bind the genuine new root-relative selector once before any corner Owner or observation. -/
def select (minimum : Nat) : Selected range budget increment firstPath lastPath minimum :=
  let value := triangleSelection range budget increment firstPath lastPath minimum
  ⟨value, rfl⟩

variable {range budget factory segment firstInside lastInside increment admitted firstPath lastPath}
    {minimum : Nat} (selected : Selected range budget increment firstPath lastPath minimum)
    (left right : Endpoint) (ordered : left.parameter ≤ right.parameter)
    (timeIndex spaceIndex : Fin (dyadicEdges selected.val.stage left right).length)

/-- The actual original bounded temporal cell occurrence at the NEW selected depth. -/
@[expose] def timeEdge : ParameterEdge :=
  (dyadicEdges selected.val.stage left right)[timeIndex.val]'timeIndex.isLt

/-- The actual original bounded spatial cell occurrence at the SAME new selected depth. -/
@[expose] def spaceEdge : ParameterEdge :=
  (dyadicEdges selected.val.stage left right)[spaceIndex.val]'spaceIndex.isLt

include ordered in
/-- Every whole point of this actual selected rectangle pays the NEW root-relative target. -/
private theorem cell_movement (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)
    (time fraction : Rational)
    (timeBetween : (timeEdge selected left right timeIndex).left.parameter ≤ time ∧
      time ≤ (timeEdge selected left right timeIndex).right.parameter)
    (spaceBetween : (spaceEdge selected left right spaceIndex).left.parameter ≤ fraction ∧
      fraction ≤ (spaceEdge selected left right spaceIndex).right.parameter) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter +
          Cast.Path.ofCoordinate (timeEdge selected left right timeIndex).left.parameter * increment)).eval
          (segment.pointAt (spaceEdge selected left right spaceIndex).left.parameter) -
        (Paths.polynomial (parameter + Cast.Path.ofCoordinate time * increment)).eval (segment.pointAt fraction)) <
      triangleTarget (patch := patch) budget := by
  let t := timeEdge selected left right timeIndex
  let s := spaceEdge selected left right spaceIndex
  have tInside : Inside time := ⟨t.left.inside.1.trans timeBetween.1, timeBetween.2.trans t.right.inside.2⟩
  have sInside : Inside fraction := ⟨s.left.inside.1.trans spaceBetween.1, spaceBetween.2.trans s.right.inside.2⟩
  have tWidth := dyadicEdges_width_le selected.val.stage selected.val.stage (Nat.le_refl _) left right ordered
    t (List.getElem_mem timeIndex.isLt)
  have sWidth := dyadicEdges_width_le selected.val.stage selected.val.stage (Nat.le_refl _) left right ordered
    s (List.getElem_mem spaceIndex.isLt)
  have tSquared := (Order.Arithmetic.pow_le_pow_direct
    (Order.Arithmetic.sub_nonneg_direct timeBetween.1)
    (Order.Arithmetic.sub_le_sub_right_direct timeBetween.2 t.left.parameter) 2).trans tWidth
  have sSquared := (Order.Arithmetic.pow_le_pow_direct
    (Order.Arithmetic.sub_nonneg_direct spaceBetween.1)
    (Order.Arithmetic.sub_le_sub_right_direct spaceBetween.2 s.left.parameter) 2).trans sWidth
  have varied := joint_variation range budget factory segment firstInside lastInside increment admitted
    zeroInside oneInside firstPath lastPath firstFactory lastFactory t.left.parameter time s.left.parameter fraction
    tInside s.left.inside sInside
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tSquared
        (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative))
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sSquared
        (spatialScale_nonnegative (budget := budget) firstPath lastPath)))
    (by decide +kernel : (0 : Rational) ≤ 2)
  have scalar :
      2 * ((Norm.Basic.normSq increment * range.coefficient) * Geometric.Basic.quarterRadius 1 selected.val.stage +
        spatialScale (budget := budget) firstPath lastPath * Geometric.Basic.quarterRadius 1 selected.val.stage) =
      Geometric.Basic.quarterRadius (jointScale (range := range) (budget := budget) increment firstPath lastPath)
        selected.val.stage := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold jointScale
    ring1
  exact ((varied.trans paid).trans_eq scalar).trans_lt (selected.val.later_accurate (Nat.le_refl _))

/-- The four corner endpoints keep their actual ordered temporal/spatial occurrence lists. -/
@[expose] def Owners : Type _ :=
  JointGrid.OwnerTable range budget factory segment firstInside lastInside increment admitted
    (timeEdge selected left right timeIndex).left [(timeEdge selected left right timeIndex).right]
    (spaceEdge selected left right spaceIndex).left [(spaceEdge selected left right spaceIndex).right]

/-- Read one SAME original corner Owner with all actual table indices explicitly retained. -/
@[expose] def owner (owners : Owners (factory := factory) (segment := segment)
    (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
    selected left right timeIndex spaceIndex) (i j : Fin 2) :
    Owner (JointGrid.radicand (segment := segment) increment
      (((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])[
        i.val]'i.isLt)
      (((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])[
        j.val]'j.isLt)) :=
  JointGrid.OwnerTable.owner (range := range) (budget := budget) (factory := factory)
    (segment := segment) (firstInside := firstInside) (lastInside := lastInside)
    (increment := increment) (admitted := admitted) (table := owners) i j

/-- Four complete original residual requests on that SAME corner table, each retaining its actual factory. -/
@[expose] def Requests (owners : Owners (factory := factory) (segment := segment)
    (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
    selected left right timeIndex spaceIndex) : Type _ :=
  DependentProduct ((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])
    (fun i => DependentProduct
      ((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])
      (fun j => { value : OwnerTail.TraceRequest (owner selected left right timeIndex spaceIndex owners i j)
          patch.rootLower patch.rootLower_positive //
        value = OwnerTail.requestTrace (owner selected left right timeIndex spaceIndex owners i j)
          patch.rootLower patch.rootLower_positive }))

/-- Select all four original trace residual floors before any corner reading is taken. -/
def requests (owners : Owners (factory := factory) (segment := segment)
    (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
    selected left right timeIndex spaceIndex) : Requests selected left right timeIndex spaceIndex owners :=
  DependentProduct.ofFn _ (fun i => DependentProduct.ofFn _ (fun j =>
    let value := OwnerTail.requestTrace (owner selected left right timeIndex spaceIndex owners i j)
      patch.rootLower patch.rootLower_positive
    ⟨value, rfl⟩))

section Observations

variable {owners : Owners (factory := factory) (segment := segment)
    (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
    selected left right timeIndex spaceIndex}

/-- Read one complete SAME already selected residual request without invoking its producer. -/
@[expose] def request (required : Requests selected left right timeIndex spaceIndex owners) (i j : Fin 2) :
    OwnerTail.TraceRequest (owner selected left right timeIndex spaceIndex owners i j)
      patch.rootLower patch.rootLower_positive :=
  (DependentProduct.get _ (DependentProduct.get _ required i) j).val

variable {required : Requests selected left right timeIndex spaceIndex owners}

/-- Four complete native readings of the SAME corner Owners at their previously selected request floors. -/
@[expose] def Readings (required : Requests selected left right timeIndex spaceIndex owners) : Type _ :=
  DependentProduct ((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])
    (fun i => DependentProduct
      ((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])
      (fun j => { value : OwnerReading (owner selected left right timeIndex spaceIndex owners i j) //
        value.tail = (request selected left right timeIndex spaceIndex required i j).tail ∧
        value.index = (request selected left right timeIndex spaceIndex required i j).compared.leftIndex }))

/-- Sample each actual corner once after the complete four-request table has been retained. -/
def readings (required : Requests selected left right timeIndex spaceIndex owners) :
    Readings selected left right timeIndex spaceIndex required :=
  DependentProduct.ofFn _ (fun i => DependentProduct.ofFn _ (fun j =>
    let retained := request selected left right timeIndex spaceIndex required i j
    let native := OwnerTail.Reading.acquire retained.tail retained.compared.leftIndex retained.compared.left_ge
    let value : OwnerReading (owner selected left right timeIndex spaceIndex owners i j) := ⟨retained.tail, native⟩
    ⟨value, rfl, rfl⟩))

/-- Read the complete SAME original native sample at its two bounded corner occurrences. -/
@[expose] def sample
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) (i j : Fin 2) :
    OwnerReading (owner selected left right timeIndex spaceIndex owners i j) :=
  (DependentProduct.get _ (DependentProduct.get _ observed i) j).val

/-- The SAME native sample has the exact original request-floor index. -/
theorem sample_index
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) (i j : Fin 2) :
    (sample selected left right timeIndex spaceIndex observed i j).index =
      (request selected left right timeIndex spaceIndex required i j).compared.leftIndex :=
  (DependentProduct.get _ (DependentProduct.get _ observed i) j).property.2

/-- Every SAME native corner lies in the original signed seed box by its actual OwnerTable factory. -/
theorem sample_inside
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) (i j : Fin 2) :
    patch.base.seed.owner.track.initial.box.Contains
      (sample selected left right timeIndex spaceIndex observed i j).value := by
  let kept := sample selected left right timeIndex spaceIndex observed i j
  let original := owner selected left right timeIndex spaceIndex owners i j
  have inside := original.certificate_candidate_in_initial_box original.parameterNonzero kept.tail.state
    kept.reading.possible
  have boxEq := JointGrid.OwnerTable.owner_box (range := range) (budget := budget) (factory := factory)
    (segment := segment) (firstInside := firstInside) (lastInside := lastInside)
    (increment := increment) (admitted := admitted) (table := owners) i j
  exact Eq.mp (congrArg (fun box : Box => box.Contains kept.value) boxEq) inside

/-- Every SAME retained corner reading satisfies its own original strict trace residual target. -/
theorem sample_residual
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) (i j : Fin 2) :
    Norm.Basic.normSq
      ((sample selected left right timeIndex spaceIndex observed i j).value *
          (sample selected left right timeIndex spaceIndex observed i j).value -
        JointGrid.radicand (segment := segment) increment
          (((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])[
            i.val]'i.isLt)
          (((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])[
            j.val]'j.isLt)) < traceAllowance patch.rootLower := by
  let kept := sample selected left right timeIndex spaceIndex observed i j
  let retained := request selected left right timeIndex spaceIndex required i j
  have later : retained.compared.leftIndex ≤ kept.index :=
    Eq.mpr (congrArg (fun index : Nat => retained.compared.leftIndex ≤ index)
      (sample_index selected left right timeIndex spaceIndex observed i j)) (Nat.le_refl _)
  exact retained.residual (kept.inTail retained.tail (retained.compared.left_ge.trans later)) later

/-- The SAME actual rational parameter rectangle, with ordered sides derived from its bounded dyadic occurrences. -/
def parameterBox : Box :=
  ⟨(timeEdge selected left right timeIndex).left.parameter,
    (timeEdge selected left right timeIndex).right.parameter,
    (spaceEdge selected left right spaceIndex).left.parameter,
    (spaceEdge selected left right spaceIndex).right.parameter,
    (dyadicEdges_bounds selected.val.stage left right ordered _ (List.getElem_mem timeIndex.isLt)).2.1,
    (dyadicEdges_bounds selected.val.stage left right ordered _ (List.getElem_mem spaceIndex.isLt)).2.1⟩

/-- The actual lower or upper cyclic triangle of that SAME retained parameter rectangle. -/
@[expose] def parameterTriangle (upper : Bool) : CoordinateTriangle :=
  let t := timeEdge selected left right timeIndex
  let s := spaceEdge selected left right spaceIndex
  if upper then
    ⟨⟨t.left.parameter, s.left.parameter⟩, ⟨t.right.parameter, s.right.parameter⟩,
      ⟨t.left.parameter, s.right.parameter⟩⟩
  else
    ⟨⟨t.left.parameter, s.left.parameter⟩, ⟨t.right.parameter, s.left.parameter⟩,
      ⟨t.right.parameter, s.right.parameter⟩⟩

/-- Both original cyclic triangles remain in their SAME actual parameter rectangle, including degenerate sides. -/
private theorem triangle_inside (upper : Bool) (u v : Rational) (inside : Triangle.Inside u v) :
    (parameterBox selected left right ordered timeIndex spaceIndex).Contains
      (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex upper) u v) := by
  let box := parameterBox selected left right ordered timeIndex spaceIndex
  have first : box.Contains (⟨box.xLower, box.yLower⟩ : Canonical) :=
    ⟨Order.Basic.le_refl _, box.x_valid, Order.Basic.le_refl _, box.y_valid⟩
  have second : box.Contains (⟨box.xUpper, box.yLower⟩ : Canonical) :=
    ⟨box.x_valid, Order.Basic.le_refl _, Order.Basic.le_refl _, box.y_valid⟩
  have third : box.Contains (⟨box.xUpper, box.yUpper⟩ : Canonical) :=
    ⟨box.x_valid, Order.Basic.le_refl _, box.y_valid, Order.Basic.le_refl _⟩
  have fourth : box.Contains (⟨box.xLower, box.yUpper⟩ : Canonical) :=
    ⟨Order.Basic.le_refl _, box.x_valid, box.y_valid, Order.Basic.le_refl _⟩
  cases upper with
  | false => exact Triangle.point_inside box _ first second third u v inside
  | true => exact Triangle.point_inside box _ first third fourth u v inside

/-- The selected root-relative allowance is bounded by the actual retained anchor norm-squared threshold. -/
private theorem allowance_le_norm (norm : Rational) (lower : patch.rootLower ≤ norm) :
    traceAllowance patch.rootLower ≤ norm ^ 2 / 1024 := by
  have first : patch.rootLower ^ 2 / 8192 ≤ patch.rootLower ^ 2 / 1024 :=
    Order.Field.div_le_div_of_nonneg_left_direct (Order.Arithmetic.sq_nonneg_direct _)
      (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by decide +kernel))
      (Data.Rat.Fraction.Cast.Order.natCast_le_direct (m := 1024) (n := 8192) (by decide +kernel))
  exact first.trans (Order.Field.divide_mono
    (Order.Arithmetic.pow_le_pow_direct patch.rootLower_positive.le lower 2)
    (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by decide +kernel)))

/-- The original lower-left native norm cache is the anchor used by both actual triangle consumers. -/
@[expose] def anchorNorm
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) : Rational :=
  (sample selected left right timeIndex spaceIndex observed 0 0).reading.norm

/-- The retained anchor norm cache is the SAME original native value's quadrance. -/
theorem anchorNorm_eq (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) :
    anchorNorm selected left right timeIndex spaceIndex observed =
      Canonical.normSq (sample selected left right timeIndex spaceIndex observed 0 0).value :=
  (sample selected left right timeIndex spaceIndex observed 0 0).reading.norm_eq

/-- The actual signed-box norm floor bounds the SAME retained native anchor norm. -/
theorem anchor_lower (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) :
    patch.rootLower ≤ anchorNorm selected left right timeIndex spaceIndex observed :=
  (patch.root_lower (sample_inside selected left right timeIndex spaceIndex observed 0 0)).trans_eq
    (anchorNorm_eq selected left right timeIndex spaceIndex observed).symm

variable (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

include ordered zeroInside oneInside firstFactory lastFactory in
/-- The actual entire selected rectangle, not just its four corners, pays the same trace movement request. -/
private theorem rectangle_trace_movement (time fraction : Rational)
    (timeBetween : (timeEdge selected left right timeIndex).left.parameter ≤ time ∧
      time ≤ (timeEdge selected left right timeIndex).right.parameter)
    (spaceBetween : (spaceEdge selected left right spaceIndex).left.parameter ≤ fraction ∧
      fraction ≤ (spaceEdge selected left right spaceIndex).right.parameter) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter +
          Cast.Path.ofCoordinate (timeEdge selected left right timeIndex).left.parameter * increment)).eval
          (segment.pointAt (spaceEdge selected left right spaceIndex).left.parameter) -
        (Paths.polynomial (parameter + Cast.Path.ofCoordinate time * increment)).eval (segment.pointAt fraction)) ≤
      traceAllowance patch.rootLower :=
  (cell_movement selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
    time fraction timeBetween spaceBetween).le.trans (Order.Basic.min_le_right _ _)

include ordered zeroInside oneInside firstFactory lastFactory in
/-- All three root-distance bounds follow internally from actual native residuals and the whole cell payment. -/
theorem root_close
    (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) (i j : Fin 2) :
    Canonical.normSq ((sample selected left right timeIndex spaceIndex observed i j).value -
      (sample selected left right timeIndex spaceIndex observed 0 0).value) ≤
      anchorNorm selected left right timeIndex spaceIndex observed / 1024 := by
  let anchor := sample selected left right timeIndex spaceIndex observed 0 0
  let final := sample selected left right timeIndex spaceIndex observed i j
  have firstInside' := sample_inside selected left right timeIndex spaceIndex observed 0 0
  have lastInside' := sample_inside selected left right timeIndex spaceIndex observed i j
  have firstLower : patch.rootLower ≤ Norm.Basic.normSq anchor.value := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact patch.root_lower firstInside'
  have sumLower : 4 * patch.rootLower ≤ Norm.Basic.normSq (anchor.value + final.value) := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact patch.root_sum_lower firstInside' lastInside'
  have tOrdered := (dyadicEdges_bounds selected.val.stage left right ordered _
    (List.getElem_mem timeIndex.isLt)).2.1
  have sOrdered := (dyadicEdges_bounds selected.val.stage left right ordered _
    (List.getElem_mem spaceIndex.isLt)).2.1
  have times : ∀ index : Fin 2,
      (timeEdge selected left right timeIndex).left.parameter ≤
          (((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])[
            index.val]'index.isLt).parameter ∧
        (((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])[
          index.val]'index.isLt).parameter ≤ (timeEdge selected left right timeIndex).right.parameter := by
    intro index
    exact Fin.cases ⟨Order.Basic.le_refl _, tOrdered⟩
      (Fin.cases ⟨tOrdered, Order.Basic.le_refl _⟩ (fun bad => Fin.elim0 bad)) index
  have spaces : ∀ index : Fin 2,
      (spaceEdge selected left right spaceIndex).left.parameter ≤
          (((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])[
            index.val]'index.isLt).parameter ∧
        (((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])[
          index.val]'index.isLt).parameter ≤ (spaceEdge selected left right spaceIndex).right.parameter := by
    intro index
    exact Fin.cases ⟨Order.Basic.le_refl _, sOrdered⟩
      (Fin.cases ⟨sOrdered, Order.Basic.le_refl _⟩ (fun bad => Fin.elim0 bad)) index
  have movement := rectangle_trace_movement selected left right ordered timeIndex spaceIndex
    zeroInside oneInside firstFactory lastFactory _ _ (times i) (spaces j)
  have close := trace_distance_le anchor.value final.value
    (JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)
    (JointGrid.radicand (segment := segment) increment
      (((timeEdge selected left right timeIndex).left :: [(timeEdge selected left right timeIndex).right])[
        i.val]'i.isLt)
      (((spaceEdge selected left right spaceIndex).left :: [(spaceEdge selected left right spaceIndex).right])[
        j.val]'j.isLt)) patch.rootLower_positive firstLower sumLower
    (sample_residual selected left right timeIndex spaceIndex observed 0 0).le movement
    (sample_residual selected left right timeIndex spaceIndex observed i j).le
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at close
  exact close.trans_eq (congrArg (fun value : Rational => value / 1024)
    (anchorNorm_eq selected left right timeIndex spaceIndex observed).symm)

/-- The original anchor reading's own certified tail gives its norm-relative residual, without a new request. -/
theorem anchor_residual (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required) :
    Canonical.normSq
      ((sample selected left right timeIndex spaceIndex observed 0 0).value ^ 2 -
        JointGrid.radicand (segment := segment) increment
          (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left) ≤
      (anchorNorm selected left right timeIndex spaceIndex observed) ^ 2 / 1024 :=
  (sample selected left right timeIndex spaceIndex observed 0 0).reading.residualNorm_eq.symm.trans_le
    (sample selected left right timeIndex spaceIndex observed 0 0).reading.residual_small

include ordered zeroInside oneInside firstFactory lastFactory in
/-- Both actual cyclic triangles satisfy the whole-radicand movement premise from the NEW selection internally. -/
theorem triangle_movement (observed : Readings selected left right timeIndex spaceIndex (owners := owners) required)
    (polynomial : { value : GaussianBivariate // value = radicandPolynomial segment increment })
    (upper : Bool) (u v : Rational) (inside : Triangle.Inside u v) :
    Canonical.normSq
      (Triangle.radicand polynomial.val
          (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex upper) u v) -
        JointGrid.radicand (segment := segment) increment
          (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left) ≤
      (anchorNorm selected left right timeIndex spaceIndex observed) ^ 2 / 1024 := by
  let point := Triangle.point (parameterTriangle selected left right timeIndex spaceIndex upper) u v
  have contained := triangle_inside selected left right ordered timeIndex spaceIndex upper u v inside
  have read := (congrArg (fun value : GaussianBivariate =>
    Bivariate.Basic.eval value (⟨point.re, 0⟩ : Canonical) (⟨point.im, 0⟩ : Canonical))
    polynomial.property).trans (radicandPolynomial_eval segment increment point.re point.im)
  have moved := rectangle_trace_movement selected left right ordered timeIndex spaceIndex
    zeroInside oneInside firstFactory lastFactory point.re point.im
    ⟨contained.1, contained.2.1⟩ contained.2.2
  rewrite [Norm.Basic.normSq_eq_canonical] at moved
  have reversed := (Canonical.normSq_neg
    ((Paths.polynomial (parameter + Cast.Path.ofCoordinate point.re * increment)).eval (segment.pointAt point.im) -
      JointGrid.radicand (segment := segment) increment
        (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left))
  have symmetry : Canonical.normSq
      ((Paths.polynomial (parameter + Cast.Path.ofCoordinate point.re * increment)).eval (segment.pointAt point.im) -
        JointGrid.radicand (segment := segment) increment
          (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left) ≤
      traceAllowance patch.rootLower := by
    have same : -((Paths.polynomial (parameter + Cast.Path.ofCoordinate point.re * increment)).eval
        (segment.pointAt point.im) - JointGrid.radicand (segment := segment) increment
          (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left) =
        JointGrid.radicand (segment := segment) increment
          (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left -
            (Paths.polynomial (parameter + Cast.Path.ofCoordinate point.re * increment)).eval
              (segment.pointAt point.im) := by ring1
    exact reversed.symm.trans_le ((congrArg Canonical.normSq same).trans_le moved)
  exact ((congrArg (fun value : Canonical => Canonical.normSq
    (value - JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)) read).trans_le
    symmetry).trans (allowance_le_norm _ (anchor_lower selected left right timeIndex spaceIndex observed))

end Observations

variable (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

/-- One actual local preparation retaining the whole original inputs and every genuine new cache/factory.

The two triangles and their three side tables consume the SAME four native
samples. This is a local new rectangle, not an identification with any
existing shared perimeter or a new global mesh.
-/
@[expose] def Preparation : Type _ :=
  (_original : { values : Range patch × FixedRootBoxBudget.Budget patch.base.seed.owner ×
      ClearSegment (Paths.polynomial parameter) ambient start finish ×
      PathData budget budget × PathData budget budget //
    values = (range, budget, segment, firstPath, lastPath) }) ×
  (_selected : { value : Selected range budget increment firstPath lastPath minimum // value = selected }) ×
  (polynomial : { value : GaussianBivariate // value = radicandPolynomial segment increment }) ×
  (owners : { value : Owners (factory := factory) (segment := segment)
      (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
      selected left right timeIndex spaceIndex //
    value = JointGrid.OwnerTable.build range budget factory segment firstInside lastInside increment admitted
      (timeEdge selected left right timeIndex).left [(timeEdge selected left right timeIndex).right]
      (spaceEdge selected left right spaceIndex).left [(spaceEdge selected left right spaceIndex).right] }) ×
  (required : { value : Requests selected left right timeIndex spaceIndex owners.val //
    value = requests selected left right timeIndex spaceIndex owners.val }) ×
  (observed : { value : Readings selected left right timeIndex spaceIndex required.val //
    value = readings selected left right timeIndex spaceIndex required.val }) ×
  (_lower : { value : GaussianBivariate // value = Triangle.affine
      (sample selected left right timeIndex spaceIndex observed.val 0 0).value
      (sample selected left right timeIndex spaceIndex observed.val 1 0).value
      (sample selected left right timeIndex spaceIndex observed.val 1 1).value }) ×
  (_lowerSides : { value : Triangle.Sides polynomial.val
      (parameterTriangle selected left right timeIndex spaceIndex false) //
    value = Triangle.sides polynomial.val (parameterTriangle selected left right timeIndex spaceIndex false) }) ×
  (_upper : { value : GaussianBivariate // value = Triangle.affine
      (sample selected left right timeIndex spaceIndex observed.val 0 0).value
      (sample selected left right timeIndex spaceIndex observed.val 1 1).value
      (sample selected left right timeIndex spaceIndex observed.val 0 1).value }) ×
    { upperSides : Triangle.Sides polynomial.val
        (parameterTriangle selected left right timeIndex spaceIndex true) //
      upperSides = Triangle.sides polynomial.val (parameterTriangle selected left right timeIndex spaceIndex true) }

/-- Construct four original Owners and requests before four corner observations and the two actual triangles. -/
def prepare : Preparation (factory := factory) (segment := segment) (firstInside := firstInside)
    (lastInside := lastInside) (admitted := admitted) selected left right timeIndex spaceIndex :=
  let polynomial : { value : GaussianBivariate // value = radicandPolynomial segment increment } :=
    let value := radicandPolynomial segment increment
    ⟨value, rfl⟩
  let owners : { value : Owners (factory := factory) (segment := segment)
      (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
      selected left right timeIndex spaceIndex //
    value = JointGrid.OwnerTable.build range budget factory segment firstInside lastInside increment admitted
      (timeEdge selected left right timeIndex).left [(timeEdge selected left right timeIndex).right]
      (spaceEdge selected left right spaceIndex).left [(spaceEdge selected left right spaceIndex).right] } :=
    let value := JointGrid.OwnerTable.build range budget factory segment firstInside lastInside increment admitted
      (timeEdge selected left right timeIndex).left [(timeEdge selected left right timeIndex).right]
      (spaceEdge selected left right spaceIndex).left [(spaceEdge selected left right spaceIndex).right]
    ⟨value, rfl⟩
  let required : { value : Requests selected left right timeIndex spaceIndex owners.val //
      value = requests selected left right timeIndex spaceIndex owners.val } :=
    let value := requests selected left right timeIndex spaceIndex owners.val
    ⟨value, rfl⟩
  let observed : { value : Readings selected left right timeIndex spaceIndex required.val //
      value = readings selected left right timeIndex spaceIndex required.val } :=
    let value := readings selected left right timeIndex spaceIndex required.val
    ⟨value, rfl⟩
  let lower := Triangle.affine (sample selected left right timeIndex spaceIndex observed.val 0 0).value
    (sample selected left right timeIndex spaceIndex observed.val 1 0).value
    (sample selected left right timeIndex spaceIndex observed.val 1 1).value
  let lowerSides := Triangle.sides polynomial.val (parameterTriangle selected left right timeIndex spaceIndex false)
  let upper := Triangle.affine (sample selected left right timeIndex spaceIndex observed.val 0 0).value
    (sample selected left right timeIndex spaceIndex observed.val 1 1).value
    (sample selected left right timeIndex spaceIndex observed.val 0 1).value
  let upperSides := Triangle.sides polynomial.val (parameterTriangle selected left right timeIndex spaceIndex true)
  ⟨⟨(range, budget, segment, firstPath, lastPath), rfl⟩, ⟨selected, rfl⟩,
    polynomial, owners, required, observed, ⟨lower, rfl⟩, ⟨lowerSides, rfl⟩, ⟨upper, rfl⟩, ⟨upperSides, rfl⟩⟩

namespace Preparation

variable {selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory}
    (prepared : Preparation (factory := factory) (segment := segment) (firstInside := firstInside)
      (lastInside := lastInside) (admitted := admitted) selected left right timeIndex spaceIndex)

/-- Read the SAME retained bivariate radicand table, including its original whole factory. -/
@[expose] def polynomial : { value : GaussianBivariate // value = radicandPolynomial segment increment } :=
  prepared.2.2.1

/-- Read the SAME whole original four-corner OwnerTable rather than reconstructing any Owner. -/
@[expose] def owners : Owners (factory := factory) (segment := segment)
    (firstInside := firstInside) (lastInside := lastInside) (admitted := admitted)
    selected left right timeIndex spaceIndex := prepared.2.2.2.1.val

/-- Read the SAME four original selected residual-request caches. -/
@[expose] def required : Requests selected left right timeIndex spaceIndex prepared.owners :=
  prepared.2.2.2.2.1.val

/-- Read the SAME complete four-sample native reading bank used by both actual triangles. -/
@[expose] def observed : Readings selected left right timeIndex spaceIndex prepared.required :=
  prepared.2.2.2.2.2.1.val

/-- Read the actual retained lower affine-root map. -/
@[expose] def lower : GaussianBivariate := prepared.2.2.2.2.2.2.1.val

/-- Read the actual retained upper affine-root map. -/
@[expose] def upper : GaussianBivariate := prepared.2.2.2.2.2.2.2.2.1.val

/-- Read all three SAME original lower-side polynomial tables. -/
@[expose] def lowerSides : Triangle.Sides prepared.polynomial.val
    (parameterTriangle selected left right timeIndex spaceIndex false) := prepared.2.2.2.2.2.2.2.1.val

/-- Read all three SAME original upper-side polynomial tables. -/
@[expose] def upperSides : Triangle.Sides prepared.polynomial.val
    (parameterTriangle selected left right timeIndex spaceIndex true) := prepared.2.2.2.2.2.2.2.2.2.val

/-- The entire original Range, Budget, parent segment and both endpoint spatial paths are retained as GIVEN. -/
theorem originals_eq : prepared.1.val = (range, budget, segment, firstPath, lastPath) := prepared.1.property

/-- The entire new joint selection, including its original floor and factory, is the GIVEN retained selection. -/
theorem selected_eq : prepared.2.1.val = selected := prepared.2.1.property

/-- The SAME retained owner table has exactly its original four-owner materialization factory. -/
theorem owners_eq : prepared.owners =
    JointGrid.OwnerTable.build range budget factory segment firstInside lastInside increment admitted
      (timeEdge selected left right timeIndex).left [(timeEdge selected left right timeIndex).right]
      (spaceEdge selected left right spaceIndex).left [(spaceEdge selected left right spaceIndex).right] :=
  prepared.2.2.2.1.property

/-- The SAME complete four-request table retains its one actual pre-reading materialization factory. -/
theorem required_eq : prepared.required = requests selected left right timeIndex spaceIndex prepared.owners :=
  prepared.2.2.2.2.1.property

/-- The SAME four-corner native reading bank retains its one actual observation factory. -/
theorem observed_eq : prepared.observed = readings selected left right timeIndex spaceIndex prepared.required :=
  prepared.2.2.2.2.2.1.property

/-- All three lower restriction tables retain their original affine-substitution factories. -/
theorem lowerSides_eq : prepared.lowerSides =
    Triangle.sides prepared.polynomial.val (parameterTriangle selected left right timeIndex spaceIndex false) :=
  prepared.2.2.2.2.2.2.2.1.property

/-- All three upper restriction tables retain their original affine-substitution factories. -/
theorem upperSides_eq : prepared.upperSides =
    Triangle.sides prepared.polynomial.val (parameterTriangle selected left right timeIndex spaceIndex true) :=
  prepared.2.2.2.2.2.2.2.2.2.property

/-- The retained lower map evaluates to the SAME three actual original native corner values. -/
theorem lower_eval (u v : Rational) :
    Bivariate.Basic.eval prepared.lower (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v) =
      Triangle.value (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
        (sample selected left right timeIndex spaceIndex prepared.observed 1 0).value
        (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value u v :=
  (congrArg (fun polynomial : GaussianBivariate =>
    Bivariate.Basic.eval polynomial (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v))
    prepared.2.2.2.2.2.2.1.property).trans (Triangle.affine_eval _ _ _ u v)

/-- The retained upper map evaluates to the SAME three actual original native corner values. -/
theorem upper_eval (u v : Rational) :
    Bivariate.Basic.eval prepared.upper (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v) =
      Triangle.value (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
        (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
        (sample selected left right timeIndex spaceIndex prepared.observed 0 1).value u v :=
  (congrArg (fun polynomial : GaussianBivariate =>
    Bivariate.Basic.eval polynomial (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v))
    prepared.2.2.2.2.2.2.2.2.1.property).trans (Triangle.affine_eval _ _ _ u v)

include ordered zeroInside oneInside firstFactory lastFactory in
/-- Genuine whole-cell and signed-root payments derive the lower triangle's full homogeneous dominance internally. -/
theorem lower_dominance (u v : Rational) (inside : Triangle.Inside u v) :
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed) ^ 2 / 32 ≤
      Canonical.normSq ((Bivariate.Basic.eval prepared.lower
        (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v)) ^ 2) -
      Canonical.normSq ((Bivariate.Basic.eval prepared.lower
        (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v)) ^ 2 -
          Triangle.radicand prepared.polynomial.val
            (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex false) u v)) := by
  have derived := Triangle.dominance prepared.polynomial.val _
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed)
    (anchorNorm_eq selected left right timeIndex spaceIndex prepared.observed)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 1)
    (anchor_residual selected left right timeIndex spaceIndex prepared.observed)
    (triangle_movement selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed prepared.polynomial false) u v inside
  exact Eq.mpr (congrArg (fun root : Canonical =>
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed) ^ 2 / 32 ≤
      Canonical.normSq (root ^ 2) - Canonical.normSq (root ^ 2 -
        Triangle.radicand prepared.polynomial.val
          (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex false) u v)))
    (prepared.lower_eval u v)) derived

include ordered zeroInside oneInside firstFactory lastFactory in
/-- The SAME original corner bank and new cell payment derive the upper triangle's actual homogeneous dominance. -/
theorem upper_dominance (u v : Rational) (inside : Triangle.Inside u v) :
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed) ^ 2 / 32 ≤
      Canonical.normSq ((Bivariate.Basic.eval prepared.upper
        (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v)) ^ 2) -
      Canonical.normSq ((Bivariate.Basic.eval prepared.upper
        (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v)) ^ 2 -
          Triangle.radicand prepared.polynomial.val
            (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex true) u v)) := by
  have derived := Triangle.dominance prepared.polynomial.val _
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
    (sample selected left right timeIndex spaceIndex prepared.observed 0 1).value
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed)
    (anchorNorm_eq selected left right timeIndex spaceIndex prepared.observed)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 1)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 1)
    (anchor_residual selected left right timeIndex spaceIndex prepared.observed)
    (triangle_movement selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed prepared.polynomial true) u v inside
  exact Eq.mpr (congrArg (fun root : Canonical =>
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed) ^ 2 / 32 ≤
      Canonical.normSq (root ^ 2) - Canonical.normSq (root ^ 2 -
        Triangle.radicand prepared.polynomial.val
          (Triangle.point (parameterTriangle selected left right timeIndex spaceIndex true) u v)))
    (prepared.upper_eval u v)) derived

include ordered zeroInside oneInside firstFactory lastFactory in
/-- The actual lower triangle consumes each SAME retained side polynomial in original finite Rouché comparison data. -/
theorem lower_sideData (side : Fin 3) :
    Triangle.SideData prepared.lowerSides
      (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
      (sample selected left right timeIndex spaceIndex prepared.observed 1 0).value
      (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value side :=
  Triangle.sideData prepared.polynomial.val _ prepared.lowerSides
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed)
    (anchorNorm_eq selected left right timeIndex spaceIndex prepared.observed)
    (patch.rootLower_positive.trans_le (anchor_lower selected left right timeIndex spaceIndex prepared.observed))
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 1)
    (anchor_residual selected left right timeIndex spaceIndex prepared.observed)
    (triangle_movement selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed prepared.polynomial false) side

include ordered zeroInside oneInside firstFactory lastFactory in
/-- The actual upper triangle consumes each SAME retained side polynomial in original finite Rouché comparison data. -/
theorem upper_sideData (side : Fin 3) :
    Triangle.SideData prepared.upperSides
      (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
      (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
      (sample selected left right timeIndex spaceIndex prepared.observed 0 1).value side :=
  Triangle.sideData prepared.polynomial.val _ prepared.upperSides
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (JointGrid.radicand (segment := segment) increment
      (timeEdge selected left right timeIndex).left (spaceEdge selected left right spaceIndex).left)
    (sample selected left right timeIndex spaceIndex prepared.observed 0 0).value
    (sample selected left right timeIndex spaceIndex prepared.observed 1 1).value
    (sample selected left right timeIndex spaceIndex prepared.observed 0 1).value
    (anchorNorm selected left right timeIndex spaceIndex prepared.observed)
    (anchorNorm_eq selected left right timeIndex spaceIndex prepared.observed)
    (patch.rootLower_positive.trans_le (anchor_lower selected left right timeIndex spaceIndex prepared.observed))
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 0)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 1 1)
    (root_close selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed 0 1)
    (anchor_residual selected left right timeIndex spaceIndex prepared.observed)
    (triangle_movement selected left right ordered timeIndex spaceIndex zeroInside oneInside firstFactory lastFactory
      prepared.observed prepared.polynomial true) side

end Preparation

end RootTriangles

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
