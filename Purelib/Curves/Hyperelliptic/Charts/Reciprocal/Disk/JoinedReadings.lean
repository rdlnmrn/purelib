module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners
open Purelib.Data.Rat
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization

/-!
# One reading stage for every junction of a retained parent

The cached owner links select all comparison stages before the shared cap
polynomial is sampled. Their certificates bound the actual gaps between the
endpoint readings used by the complete parent evaluator.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (EvaluationData)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap}

namespace EndpointRequests

variable {target : Coordinate} {floor index depth readingIndex :
  Nat}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index} {box
    : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}

/-- Read the first actual cached original endpoint value, using zero for an empty bank. -/
@[expose] def firstValue : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian
  | _, _, _, .nil, .nil, _ => 0
  | _, _, _, .cons _ _, .cons _ _, readings => readings.1.firstValue

/-- Read the last actual cached original endpoint value, retaining the incoming value for an empty bank. -/
@[expose] def lastValue : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian →
        Gaussian
  | _, _, _, .nil, .nil, _, previous => previous
  | _, _, _, .cons _ rest, .cons _ cells, readings, _ =>
    EndpointRequests.lastValue rest cells readings.2
    readings.1.lastValue

/-- Read the first actual cached original root coordinate, using zero for an empty bank. -/
@[expose] def firstCoordinate : {edges : List ParameterEdge} → {bank :
  Bank regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian
  | _, _, _, .nil, .nil, _ => 0
  | _, _, _, .cons _ _, .cons _ _, readings => readings.1.firstReading.coordinate

/-- Read the last actual cached original root coordinate, retaining the incoming coordinate for an empty bank. -/
@[expose] def lastCoordinate : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian →
        Gaussian
  | _, _, _, .nil, .nil, _, previous => previous
  | _, _, _, .cons _ rest, .cons _ cells, readings, _ =>
    EndpointRequests.lastCoordinate rest cells
    readings.2 readings.1.lastReading.coordinate

/-- The original already sampled first root and primitive reading. -/
@[expose] def firstReading {edges : List ParameterEdge} {bank : Bank
  regular data edges} {owners : Owners bank}
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells)
    {first last : Coordinate} (chain : From first edges last) (nonempty : edges ≠ []) :
    {result : EndpointView.RootReading (firstView owners chain nonempty) capSample readingIndex //
      result.reading.value = firstValue
        requests cells readings ∧
      result.reading.coordinate =
        firstCoordinate requests cells
        readings} := by
  cases requests with
  | nil => exact False.elim (nonempty rfl)
  | @cons edge remaining cell comparison bank first rest request tail =>
      cases cells with
      | cons cell cells =>
          exact ⟨EndpointView.rootReading first.bounds.first chain.1.symm readings.1.firstReading,
            EndpointView.rootReading_value _ _ _, EndpointView.rootReading_coordinate _ _ _⟩

/-- The original already sampled last root and primitive reading. -/
@[expose] def lastReading {edges : List ParameterEdge} {bank : Bank
  regular data edges} {owners : Owners bank}
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells)
    {first last : Coordinate} (chain : From first edges last) (nonempty : edges ≠ []) :
    {result : EndpointView.RootReading (lastView owners chain nonempty) capSample readingIndex //
      ∀ previous, result.reading.value =
        lastValue requests cells readings
        previous ∧
        result.reading.coordinate =
          lastCoordinate requests cells
          readings previous} := by
  cases requests with
  | nil => exact False.elim (nonempty rfl)
  | @cons edge remaining cell comparison bank owned rest request tail =>
      cases cells with
      | cons cell cells =>
          cases tail with
          | nil =>
              cases cells
              exact ⟨EndpointView.rootReading owned.bounds.last chain.2 readings.1.lastReading, fun _ =>
                ⟨EndpointView.rootReading_value _ _ _, EndpointView.rootReading_coordinate _ _ _⟩⟩
          | cons next tail =>
              have selected :=
                EndpointRequests.lastReading (.cons
                next tail) cells readings.2 chain.2 (by intro equal; cases equal)
              exact ⟨selected.1, fun _ => ⟨(selected.2 readings.1.lastValue).1, (selected.2
                readings.1.lastReading.coordinate).2⟩⟩
termination_by structural requests

/-- Every actual original endpoint gap, including the supplied incoming gap, satisfies the retained squared-norm bound.
-/
@[expose] def GapsSmall : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian →
        Coordinate → Prop
  | _, _, _, .nil, .nil, _, _, _ => True
  | _, _, _, .cons _ rest, .cons _ cells, readings, previous, bound =>
      Basic.normSq (readings.1.firstValue - previous) ≤ bound ∧
        EndpointRequests.GapsSmall rest cells
        readings.2 readings.1.lastValue bound

/-- Coordinate connectors consume the same cached roots as the endpoint pairs. -/
@[expose] def coordinateGaps : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    (requests : EndpointRequests target floor owners) → (cells : ComparedCells source
      capSample depth bank) →
      EvaluationData (readingIndex := readingIndex) requests cells → Gaussian →
        List Gaussian
  | _, _, _, .nil, .nil, _, _ => []
  | _, _, _, .cons _ rest, .cons _ cells, readings, previous =>
      (readings.1.firstReading.coordinate - previous) ::
        EndpointRequests.coordinateGaps rest cells
        readings.2 readings.1.lastReading.coordinate

/-- The retained original root-coordinate connector list has one entry per actual covered edge. -/
theorem coordinateGaps_length {edges : List ParameterEdge} {bank : Bank
  regular data edges} {owners : Owners bank}
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells) (previous :
      Gaussian) :
    (coordinateGaps requests cells readings
      previous).length = edges.length := by
  induction requests generalizing previous with
  | nil => cases cells; rfl
  | cons request rest ih =>
      cases cells with
      | cons cell cells => exact congrArg Nat.succ (ih cells readings.2 readings.1.lastReading.coordinate)

set_option genInjectivity false in
/-- Cached original boundary coordinates and every actual root-coordinate connector.

The exact endpoint readbacks and connector count refer to the retained endpoint evaluations, and each gap pays the
original collar clearance bound. -/
structure CoordinateConnections {edges : List ParameterEdge} {bank : Bank
  regular data edges} {owners : Owners bank}
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells) where
  /-- The cached original first endpoint coordinate or exact chart endpoint view. -/ first :
    Gaussian
  /-- The first coordinate is exactly the original retained endpoint evaluation's readback. -/ first_eq : first =
    firstCoordinate requests cells readings
  /-- The cached original last endpoint coordinate or exact chart endpoint view. -/ last :
    Gaussian
  /-- The last coordinate is exactly the original retained endpoint evaluation's readback. -/ last_eq : last =
    lastCoordinate requests cells readings
    first
  /-- The cached actual root-coordinate connectors between original retained cells. -/ gaps : List
    Gaussian
  /-- The connectors are exactly those read from the original cached endpoint evaluations. -/ gaps_eq : gaps =
    coordinateGaps requests cells readings
    first
  /-- The retained connector count equals the original covered-edge count. -/ length_eq : gaps.length = edges.length
  /-- Every actual retained connector satisfies the original collar clearance allowance. -/ bounded : ∀ gap ∈ gaps,
    Basic.normSq gap ≤ collar.coordinateBound / 64

constructive_injectivity CoordinateConnections

set_option genInjectivity false in
/-- Boundary records are views of the same endpoint evaluations consumed by the path. -/
structure BoundaryReadings {mesh : UniformReciprocalCover.Mesh data} {bank : Bank regular data mesh.edges}
  {owners : Owners bank}
    (boundary : Boundary mesh owners)
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells) where
  /-- The cached original first endpoint coordinate or exact chart endpoint view. -/ first :
    Coordinates.Overlap.Endpoint boundary.first.point.coordinates capSample
  /-- The original already sampled first root and primitive reading. -/ firstReading : ChartReadings.Endpoint.Reading
    first readingIndex
  /-- The retained boundary view reads exactly the original first root coordinate. -/ first_coordinate :
    firstReading.coordinate =
    firstCoordinate requests cells readings
  /-- The retained boundary view reads exactly the original first primitive value. -/ first_value :
    first.approximation.sample readingIndex =
    firstValue requests cells readings
  /-- The cached original last endpoint coordinate or exact chart endpoint view. -/ last : Coordinates.Overlap.Endpoint
    boundary.last.point.coordinates capSample
  /-- The original already sampled last root and primitive reading. -/ lastReading : ChartReadings.Endpoint.Reading last
    readingIndex
  /-- For every incoming coordinate, the retained boundary view reads the actual original last root coordinate. -/
    last_coordinate : ∀ previous, lastReading.coordinate =
    lastCoordinate requests cells readings
    previous
  /-- For every incoming value, the retained boundary view reads the actual original last primitive value. -/ last_value
    : ∀ previous, last.approximation.sample readingIndex =
    lastValue requests cells readings
    previous

constructive_injectivity BoundaryReadings

/-- Expose the original cached first and last readings through their certified retained boundary views. -/
@[expose] def boundaryReadings {mesh : UniformReciprocalCover.Mesh data} {bank : Bank regular data
  mesh.edges} {owners : Owners bank}
    (boundary : Boundary mesh owners)
    (requests : EndpointRequests target floor owners) (cells : ComparedCells source
      capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) requests cells) :
    BoundaryReadings boundary requests cells
      readings := by
  rcases boundary with ⟨_, firstEq, _, lastEq⟩
  cases firstEq
  cases lastEq
  let first := firstReading requests cells
    readings (mesh_from mesh) (mesh_nonempty mesh)
  let last := lastReading requests cells
    readings (mesh_from mesh) (mesh_nonempty mesh)
  exact ⟨first.1.endpoint, first.1.reading, first.2.2, first.1.reading.sample_eq.symm.trans first.2.1,
    last.1.endpoint, last.1.reading, fun previous => (last.2 previous).2,
    fun previous => last.1.reading.sample_eq.symm.trans (last.2 previous).1⟩

end EndpointRequests

/-- Paid original adjacent-owner comparisons indexed by the exact retained endpoint-owner link spine. -/
@[expose] def JunctionRequests (target : Coordinate) (floor : Nat) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      (owners : Owners bank) → Links owners → Type
  | _, _, .nil, _ => PUnit
  | _, _, .cons _ .nil, _ => PUnit
  | _, _, .cons first (@cons _ _ _ _ _ _ _ _ _ _ _ _ _ nextComparison _ next remaining), links =>
      JunctionRequests.Request first.bounds.last links.head target floor ×
        JoinedReadings.JunctionRequests target floor (.cons
          (comparison := nextComparison) next remaining) links.tail

namespace JunctionRequests

/-- Request every original cached junction at the supplied target and reading floor without rebuilding owner joins. -/
@[expose] def build (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      (owners : Owners bank) →
      (links : Links owners) → JunctionRequests target
        floor owners links
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons _ .nil, _ => ⟨⟩
  | _, _, .cons first (@cons _ _ _ _ _ _ _ _ _ _ _ _ _ nextComparison _ next remaining), links =>
      ⟨JunctionRequests.Request.build first.bounds.last links.head target positive floor,
        JunctionRequests.build target positive floor
          (.cons (comparison := nextComparison) next remaining) links.tail⟩

variable {target : Coordinate} {floor : Nat}

/-- Compute one stage above every original retained junction request. -/
@[expose] def maximum : {edges : List ParameterEdge} → {bank : Bank
  regular data edges} → {owners : Owners bank} →
    {links : Links owners} → JunctionRequests target
      floor owners links → Nat
  | _, _, .nil, _, _ => floor
  | _, _, .cons _ .nil, _, _ => floor
  | _, _, .cons _ (@cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, requests =>
      max requests.1.index (JunctionRequests.maximum
        requests.2)

variable {endpointTarget : Coordinate} {endpointFloor index depth
  readingIndex : Nat}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index} {box
    : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}

/-- At the common retained reading stage, every original endpoint gap satisfies its paid junction target. -/
theorem accurate {edges : List ParameterEdge} {bank : Bank regular data
  edges} {owners : Owners bank}
    (endpoints : EndpointRequests endpointTarget endpointFloor owners) (cells :
      ComparedCells source capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) endpoints cells)
    {links : Links owners} (requests :
      JunctionRequests target floor owners links)
    (later : maximum requests ≤
      readingIndex) (previous : Gaussian)
    (small : Basic.normSq
      (EndpointRequests.firstValue endpoints cells readings -
      previous) ≤ target) :
    EndpointRequests.GapsSmall endpoints cells readings
      previous target := by
  induction endpoints generalizing previous with
  | nil => cases cells; trivial
  | cons request rest ih =>
      cases cells with
      | cons cell cells =>
          refine ⟨small, ?_⟩
          cases rest with
          | nil => cases cells; trivial
          | cons next rest =>
              cases cells with
              | cons nextCell cells =>
                  apply ih (.cons nextCell cells) readings.2 requests.2
                    ((Data.Nat.Order.le_max_right _ _).trans later) readings.1.lastValue
                  change Basic.normSq (readings.2.1.firstValue - readings.1.lastValue) ≤
                    target
                  rw [readings.2.1.firstValue_eq, readings.1.lastValue_eq]
                  exact (requests.1.accurate readings.1.last readings.2.1.first ((Data.Nat.Order.le_max_left _ _).trans
                    later) ((Data.Nat.Order.le_max_left _ _).trans later)).le

/-- All cell joins satisfy the geometric clearance budget at the same stage as the original primitive connector
comparisons. -/
theorem coordinate_accurate {edges : List ParameterEdge} {bank : Bank
  regular data edges} {owners : Owners bank}
    (endpoints : EndpointRequests endpointTarget endpointFloor owners) (cells :
      ComparedCells source capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) endpoints cells)
    {links : Links owners} (requests :
      JunctionRequests target floor owners links)
    (later : maximum requests ≤
      readingIndex) (previous : Gaussian)
    (small : Basic.normSq
      (EndpointRequests.firstCoordinate endpoints cells
      readings - previous) ≤ collar.coordinateBound / 64) :
    ∀ gap ∈ EndpointRequests.coordinateGaps endpoints cells
      readings previous, Basic.normSq gap ≤ collar.coordinateBound / 64 := by
  induction endpoints generalizing previous with
  | nil => cases cells; intro _ member; exact False.elim (List.not_mem_nil member)
  | cons request rest ih =>
      cases cells with
      | cons cell cells =>
          intro gap member
          rcases Data.List.Membership.mem_cons.mp member with same | member
          · subst gap; exact small
          · cases rest with
            | nil => cases cells; exact False.elim (List.not_mem_nil member)
            | cons next rest =>
                cases cells with
                | cons nextCell cells =>
                    apply ih (.cons nextCell cells) readings.2 requests.2 ((Data.Nat.Order.le_max_right _ _).trans
                      later)
                      readings.1.lastReading.coordinate ?_ gap member
                    change Basic.normSq (readings.2.1.firstReading.coordinate -
                      readings.1.lastReading.coordinate) ≤ _
                    rw [readings.2.1.firstReading.coordinate_eq, readings.1.lastReading.coordinate_eq]
                    exact (requests.1.coordinate_accurate ((Data.Nat.Order.le_max_left _ _).trans later)
                      ((Data.Nat.Order.le_max_left _ _).trans later)).le

/-- Cache the original endpoint coordinates and their actual connector list at the paid common stage. -/
@[expose] def coordinateConnections {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners : Owners bank}
    (endpoints : EndpointRequests endpointTarget endpointFloor owners) (cells :
      ComparedCells source capSample depth bank)
    (readings : EvaluationData (readingIndex := readingIndex) endpoints cells)
    {links : Links owners} (requests :
      JunctionRequests target floor owners links)
    (later : maximum requests ≤
      readingIndex) : EndpointRequests.CoordinateConnections
      endpoints cells readings := by
  let first := EndpointRequests.firstCoordinate endpoints
    cells readings
  let last := EndpointRequests.lastCoordinate endpoints cells
    readings first
  let gaps := EndpointRequests.coordinateGaps endpoints cells
    readings first
  exact ⟨first, rfl, last, rfl, gaps, rfl,
    EndpointRequests.coordinateGaps_length endpoints cells
    readings first,
    requests.coordinate_accurate endpoints cells readings later first (by
      change Basic.normSq (first - first) ≤ _
      rw [Data.Gaussian.Basic.sub_self, Basic.normSq_zero]
      exact (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide +kernel)).le)⟩

end JunctionRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
