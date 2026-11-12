module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedEstimates
import Init.Core
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
open Purelib.Data.Rat
open Purelib.Riemann.Normalization

/-!
# Requested joined cap comparison on the actual exterior parent

All polynomial, endpoint and junction requests are selected before the shared
sample. Evaluation consumes the original reciprocal area cells, retains their
source summary, and certifies both errors against the full corrected cap path.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea (SideAreaBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings (JunctionRequests)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {cover :
    UniformReciprocalCover.Cover data}

set_option genInjectivity false in
/-- A cached request for a complete cap-parent path with actual endpoint and junction connectors.

Separate polynomial and reading stages pay both total and area targets against the original comparison cells before the
shared samples are evaluated. -/
structure JoinedRequest (prepared : Preparation regular cover) (totalTarget areaTarget :
  Coordinate) (floor : Nat) where
  /-- The cached uniform magnitude ceiling for the retained cap cells. -/ bound : Coordinate
  /-- The ceiling is exactly twice the sum of the retained slope and comparison scale. -/ bound_eq : bound = 2 *
    (prepared.budget.slope + prepared.budget.scale)
  /-- The retained magnitude ceiling is nonnegative. -/ bound_nonnegative : 0 ≤ bound
  /-- The finite cell-count budget paying quarter shares of the requested total and area targets. -/ budget :
    SideAreaBudget bound cover.mesh.edges.length (totalTarget / 4) (areaTarget / 4)
  /-- The retained polynomial comparison request or its exact evaluated cache. -/ polynomial : Request
    prepared (totalTarget / 4) (areaTarget / 4) floor
  /-- The cached endpoint requests for the original retained owner spine. -/ endpoints :
    EndpointRequests (budget.tolerance / 4) floor prepared.owners
  /-- The cached comparisons at every actual retained endpoint junction. -/ junctions : JunctionRequests
    (budget.tolerance / 4) floor prepared.owners prepared.links
  /-- The cached polynomial stage paying both the comparison and endpoint requests. -/ index : Nat
  /-- The polynomial stage is the maximum of the retained comparison and endpoint requirements. -/ index_eq : index =
    max polynomial.index endpoints.maximum
  /-- The cached reading stage paying all retained endpoint and junction comparisons. -/ readingIndex : Nat
  /-- The reading stage is the maximum of the retained endpoint and junction requirements. -/ readingIndex_eq :
    readingIndex = max endpoints.readingMaximum junctions.maximum

constructive_injectivity JoinedRequest

namespace JoinedRequest

/-- Cache the polynomial, endpoint and junction requests with their separate quarter-target budgets and common stage
bounds. -/
@[expose] def build (prepared : Preparation regular cover) (totalTarget areaTarget :
  Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
    JoinedRequest prepared totalTarget areaTarget floor :=
  let bound := 2 * (prepared.budget.slope + prepared.budget.scale)
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg prepared.budget.slope_nonnegative prepared.budget.nonnegative)
  have totalQuarter := Fraction.Order.Field.div_pos_direct totalPositive (by
      decide : (0 : Coordinate) < 4)
  have areaQuarter := Fraction.Order.Field.div_pos_direct areaPositive (by
      decide : (0 : Coordinate) < 4)
  let budget := SideAreaBudget.build bound boundNonnegative cover.mesh.edges.length (totalTarget / 4) (areaTarget / 4)
    totalQuarter areaQuarter
  let polynomial := Request.build prepared (totalTarget / 4) (areaTarget / 4) totalQuarter areaQuarter
    floor
  have tolerancePositive := Fraction.Order.Field.div_pos_direct budget.positive (by
      decide : (0 : Coordinate) < 4)
  let endpoints := EndpointRequests.build (budget.tolerance / 4) tolerancePositive floor prepared.owners
  let junctions := JunctionRequests.build (budget.tolerance / 4) tolerancePositive floor prepared.owners prepared.links
  ⟨bound, rfl, boundNonnegative, budget, polynomial, endpoints, junctions, max polynomial.index endpoints.maximum, rfl,
    max endpoints.readingMaximum junctions.maximum, rfl⟩

variable {prepared : Preparation regular cover}
  {totalTarget areaTarget : Coordinate} {floor depth : Nat}
  {originalTarget : Coordinate} {original :
    Cover.AreaRequest cover depth originalTarget}
  {box : Geometry.Rational.Box} {capSample :
    Primitives.Sample cap differential original.index box}

/-- The retained polynomial stage respects the original request floor. -/
theorem floor_le (request : JoinedRequest prepared totalTarget
  areaTarget floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact request.polynomial.floor_le.trans (Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- The cached original source comparison and complete corrected cap path with paid total and area errors. -/
structure Evaluation (request : JoinedRequest prepared
  totalTarget areaTarget floor)
    (original : Cover.AreaRequest cover depth originalTarget)
    (capSample : Primitives.Sample cap differential original.index box) (readingIndex : Nat) where
  /-- The retained polynomial comparison request or its exact evaluated cache. -/ polynomial :
    Request.Evaluation request.polynomial original capSample
  /-- The cached actual endpoint readings on the retained polynomial comparison cells. -/ readings :
    EndpointRequests.EvaluationData (readingIndex := readingIndex) request.endpoints polynomial.cells
  /-- The retained first and last readings selected through the original boundary owner views. -/ boundary :
    EndpointRequests.BoundaryReadings prepared.boundary request.endpoints polynomial.cells readings
  /-- The cached operational connections between the actual consecutive endpoint readings. -/ coordinates :
    EndpointRequests.CoordinateConnections request.endpoints polynomial.cells readings
  /-- The cached initial endpoint value of the complete corrected path. -/ firstValue : Gaussian
  /-- The initial value is exactly the first value of the retained endpoint-reading bank. -/ firstValue_eq : firstValue
    = EndpointRequests.firstValue request.endpoints polynomial.cells readings
  /-- The cached complete corrected path retaining all original fine increments and connectors. -/ joined :
    JoinedCells request.endpoints polynomial.cells readings firstValue request.bound
  /-- The original source and complete corrected cap totals satisfy the requested target. -/ total_close :
    Basic.normSq (polynomial.left.total - joined.summary.total) < totalTarget
  /-- The original source and complete corrected cap areas satisfy the requested target. -/ area_close :
    Basic.normSq (polynomial.left.area - joined.summary.area) < areaTarget

constructive_injectivity Evaluation

/-- Assemble the original joined path from already certified polynomial and endpoint data. This constructor does not
resample either cache. -/
@[expose] def evaluateWithReadings (request : JoinedRequest
  prepared totalTarget areaTarget floor)
    (polynomial : Request.Evaluation request.polynomial original capSample) {readingIndex : Nat}
    (readings : EndpointRequests.EvaluationData (readingIndex := readingIndex) request.endpoints polynomial.cells)
    (readingLater : request.readingIndex ≤ readingIndex) :
      Evaluation request original capSample
      readingIndex := by
  let firstValue := EndpointRequests.firstValue request.endpoints polynomial.cells readings
  have small := JunctionRequests.accurate request.endpoints polynomial.cells readings request.junctions
    ((Data.Nat.Order.le_max_right _ _).trans (request.readingIndex_eq.ge.trans readingLater)) firstValue (by
      change Basic.normSq (firstValue - firstValue) ≤ request.budget.tolerance / 4
      rw [Data.Gaussian.Basic.sub_self, Basic.normSq_zero]
      exact Fraction.Order.Field.div_nonneg_direct request.budget.positive.le (by decide))
  let joined : JoinedCells request.endpoints polynomial.cells readings firstValue request.bound := by
    exact Eq.mpr (congrArg (fun bound => JoinedCells request.endpoints polynomial.cells readings firstValue
      bound) request.bound_eq)
      (JoinedCells.build prepared.budget request.budget.positive.le request.endpoints polynomial.cells readings
        firstValue
        prepared.bounded small)
  have capTotal : polynomial.cap.total = polynomial.cells.capSummary.total := by
    rw [polynomial.cap.total_eq, polynomial.cells.capSummary.total_eq]
  have capArea : polynomial.cap.area = polynomial.cells.capSummary.area := by
    rw [polynomial.cap.area_eq, polynomial.cells.capSummary.area_eq]
  have totalClose : Basic.normSq (polynomial.cap.total - joined.summary.total) < totalTarget
    / 4 := by
    rw [capTotal, show polynomial.cells.capSummary.total - joined.summary.total =
      -(joined.summary.total - polynomial.cells.capSummary.total) by ring1, Basic.normSq_neg]
    exact JoinedEstimates.total_close request.budget joined
  have areaClose : Basic.normSq (polynomial.cap.area - joined.summary.area) < areaTarget / 4
    := by
    rw [capArea, show polynomial.cells.capSummary.area - joined.summary.area =
      -(joined.summary.area - polynomial.cells.capSummary.area) by ring1, Basic.normSq_neg]
    exact JoinedEstimates.area_close request.budget joined request.bound_nonnegative
  exact ⟨polynomial, readings, EndpointRequests.boundaryReadings prepared.boundary request.endpoints polynomial.cells
    readings,
    JunctionRequests.coordinateConnections request.endpoints polynomial.cells readings request.junctions
      ((Data.Nat.Order.le_max_right _ _).trans (request.readingIndex_eq.ge.trans readingLater)), firstValue, rfl,
        joined,
    (fun {first middle last : Gaussian} {target : Coordinate}
      (before : Basic.normSq (first - middle) < target / 4)
      (after : Basic.normSq (middle - last) < target / 4) =>
      show Basic.normSq (first - last) < target from by
      have triangle : first - last = (first - middle) + (middle - last) := by ring1
      rewrite [triangle]
      exact Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance.normSq_add_lt_of_quarters before after.le)
        polynomial.total_close totalClose, (fun {first middle last : Gaussian} {target :
        Coordinate}
      (before : Basic.normSq (first - middle) < target / 4)
      (after : Basic.normSq (middle - last) < target / 4) =>
      show Basic.normSq (first - last) < target from by
      have triangle : first - last = (first - middle) + (middle - last) := by ring1
      rewrite [triangle]
      exact Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance.normSq_add_lt_of_quarters before after.le)
        polynomial.area_close areaClose⟩

/-- The only stage condition is the computed request floor; no endpoint matching, path identification or area estimate
is supplied by the caller. -/
@[expose] def evaluate (request : JoinedRequest prepared
  totalTarget areaTarget floor)
    (original : Cover.AreaRequest cover depth originalTarget)
    (capSample : Primitives.Sample cap differential original.index box)
    (later : request.index ≤ original.index) (readingIndex : Nat) (readingLater : request.readingIndex ≤ readingIndex) :
    Evaluation request original capSample
      readingIndex := by
  have indices := request.index_eq.ge.trans later
  let polynomial := request.polynomial.evaluate original capSample ((Data.Nat.Order.le_max_left _ _).trans indices)
  let readings := EndpointRequests.evaluate request.endpoints polynomial.cells ((Data.Nat.Order.le_max_right _ _).trans
    indices)
    ((Data.Nat.Order.le_max_left _ _).trans (request.readingIndex_eq.ge.trans readingLater))
  exact request.evaluateWithReadings polynomial readings readingLater

end JoinedRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
