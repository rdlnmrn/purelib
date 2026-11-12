module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Quotients
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Euler
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Vector.Dependent
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order

/-! # One actual sample stage for all adjacent retained local jets

Each edge derives its four reference quotient floors and retains its own
connection residual selection. Their finite maximum precedes evaluation
of the unchanged vertex jets. Adjacent Euler defects therefore use the
same actual sample at their shared vertex, with all payments derived.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows
  (QuotientBounds referenceEulerFactor)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.LinearAlgebra.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage intervals : Nat}
    (offsets : Fin (intervals + 1) → Canonical)
    (admitted : ∀ vertex, Norm.Basic.normSq (offsets vertex) ≤ allocation.bound)
    (members : DependentVector (fun vertex => LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage (offsets vertex) (admitted vertex)))
    (steps : Fin intervals → Rational)

/-- One original reference-floor certificate and residual selection for an actual adjacent cached pair.

Both input jets are the original entries of the retained vertex vector.
The residual selection uses the same first Frame and literal step width.
-/
@[expose] def EdgeSampling (residualStart : Nat) (edge : Fin intervals) :=
  LocalMember.QuotientFloors (members.get edge.castSucc) (members.get edge.succ) ×
    Search.Selection 1 residualStart
      (steps edge ^ 2 * (ParameterClearance.ofFrame (members.get edge.castSucc).targetFrame).connectionLowerSq)

/-- Derive each edge's original quotient floors and connection selection before reading any vertex sample. -/
def edgeSampling
    (positive : ∀ edge : Fin intervals, 0 < steps edge) (firstStart lastStart freshStart residualStart : Nat)
    (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1)
    (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) (spatial : AccuracyRequest) :
    DependentVector (EdgeSampling offsets admitted members steps residualStart) :=
  DependentVector.ofFn (fun edge =>
    let bounds := LocalMember.quotientFloors (members.get edge.castSucc) (members.get edge.succ)
      firstStart lastStart freshStart (unit edge) (nonzero edge) spatial
    let selection := Connection.connectionSelection (members.get edge.castSucc).targetFrame
      (steps edge) (positive edge) residualStart
    ⟨bounds, selection⟩)

/-- The same original edge entry's three stage requirements: outgoing, incoming and connection residual. -/
def edgeStage {residualStart : Nat} (edge : Fin intervals)
    (paid : EdgeSampling offsets admitted members steps residualStart edge) : Nat :=
  Nat.max paid.1.val.1 (Nat.max paid.1.val.2 paid.2.stage)

/-- One finite maximum reads only the actual retained edge certificates and selections. -/
def samplingFloor {residualStart : Nat}
    (edges : DependentVector (EdgeSampling offsets admitted members steps residualStart)) : Nat :=
  edges.maximum (edgeStage offsets admitted members steps)

/-- Materialize both original value-channel readings at every stored vertex and one supplied common index. -/
def sampleValues (index : Nat) : Vec (Vec Canonical 2) (intervals + 1) :=
  vectorOfFn (fun vertex => vectorOfFn (fun coordinate =>
    (((members.get vertex).jet.value coordinate).integral.model index).integralSample))

/-- Each stored vector coordinate reads that same original cached jet at the common index. -/
theorem sampleValues_apply (index : Nat) (vertex : Fin (intervals + 1)) (coordinate : Fin 2) :
    sampleValues offsets admitted members index vertex coordinate =
      (((members.get vertex).jet.value coordinate).integral.model index).integralSample := by
  unfold sampleValues
  exact (congrArg (fun value : Vec Canonical 2 => value coordinate) (vectorOfFn_apply _ vertex)).trans
    (vectorOfFn_apply _ coordinate)

/-- The original edge data, common stage, cached values and all internally derived connection Euler defects. -/
@[expose] def ConnectionSampleConsumer
    (positive : ∀ edge : Fin intervals, 0 < steps edge) (firstStart lastStart freshStart residualStart : Nat)
    (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1)
    (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) (spatial : AccuracyRequest)
    (minimum : Nat) (direction : Canonical) (Result : Type u) :=
  (edges : DependentVector (EdgeSampling offsets admitted members steps residualStart)) →
  edges = edgeSampling offsets admitted members steps positive firstStart lastStart freshStart residualStart
    unit nonzero spatial →
  (index : Nat) →
  index = Nat.max minimum (samplingFloor offsets admitted members steps edges) →
  (values : Vec (Vec Canonical 2) (intervals + 1)) →
  values = sampleValues offsets admitted members index →
  (∀ edge : Fin intervals,
    Norm.vector (Euler.defect
      (Connection.alongMatrix (parameter + offsets edge.castSucc) direction) (steps edge)
      (values edge.castSucc) (values edge.succ)) ≤
        referenceEulerFactor (covered := covered) direction * steps edge ^ 4) → Result

/-- Construct consistent finite vertex readings and derive every local connection Euler defect internally.

The same stored vertex member serves its incoming and outgoing edges.
One finite maximum pays every reference floor and actual residual
selection before the value vector is materialized. Exact scaled offset
increments are intrinsic path data; no numerical defect, derivative or
ODE identity is an admission. A zero-edge family is allowed.
-/
def withConnectionSamples
    (positive : ∀ edge : Fin intervals, 0 < steps edge) (firstStart lastStart freshStart residualStart : Nat)
    (unit : ∀ edge : Fin intervals, Norm.Basic.normSq (offsets edge.succ - offsets edge.castSucc) ≤ 1)
    (nonzero : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc ≠ 0) (spatial : AccuracyRequest)
    (minimum : Nat) (direction : Canonical)
    (scaled : ∀ edge : Fin intervals, offsets edge.succ - offsets edge.castSucc = scale (steps edge) direction)
    {Result : Type u}
    (consume : ConnectionSampleConsumer offsets admitted members steps positive
      firstStart lastStart freshStart residualStart unit nonzero spatial minimum direction Result) : Result :=
  let edges := edgeSampling offsets admitted members steps positive firstStart lastStart freshStart residualStart
    unit nonzero spatial
  let index := Nat.max minimum (samplingFloor offsets admitted members steps edges)
  let values := sampleValues offsets admitted members index
  have bounded (edge : Fin intervals) :
      Norm.vector (Euler.defect
        (Connection.alongMatrix (parameter + offsets edge.castSucc) direction) (steps edge)
        (values edge.castSucc) (values edge.succ)) ≤
          referenceEulerFactor (covered := covered) direction * steps edge ^ 4 := by
    let paid := edges.get edge
    have maximum := DependentVector.get_le_maximum
      (edgeStage offsets admitted members steps) edges edge
    have after : edgeStage offsets admitted members steps edge paid ≤ index :=
      maximum.trans (Order.le_max_right minimum (samplingFloor offsets admitted members steps edges))
    have firstAfter : paid.1.val.1 ≤ index :=
      (Order.le_max_left paid.1.val.1 (Nat.max paid.1.val.2 paid.2.stage)).trans after
    have lastAfter : paid.1.val.2 ≤ index :=
      (Order.le_max_left paid.1.val.2 paid.2.stage).trans
        ((Order.le_max_right paid.1.val.1 (Nat.max paid.1.val.2 paid.2.stage)).trans after)
    have residualAfter : paid.2.stage ≤ index :=
      (Order.le_max_right paid.1.val.2 paid.2.stage).trans
        ((Order.le_max_right paid.1.val.1 (Nat.max paid.1.val.2 paid.2.stage)).trans after)
    exact ShiftedGeometry.BetweenRows.QuotientBounds.eulerDefect_le paid.1.property
      (steps edge) direction (scaled edge) (nonzero edge)
      residualStart index index paid.2 (Data.Nat.Order.max_le firstAfter residualAfter) lastAfter
      (values edge.castSucc) (values edge.succ)
      (fun coordinate => sampleValues_apply offsets admitted members index edge.castSucc coordinate)
      (fun coordinate => sampleValues_apply offsets admitted members index edge.succ coordinate)
  consume edges rfl index rfl values rfl bounded

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
