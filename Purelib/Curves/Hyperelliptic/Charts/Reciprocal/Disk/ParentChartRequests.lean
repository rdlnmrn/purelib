module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization

/-!
# One common chart preparation for the original reciprocal parent bank

Every request is indexed by the existing owner and comparison spines. The
source and spatial maxima precede sampling; the chart maximum precedes all
root readings. Existing pair certificates consume those same readings.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners OwnedEndpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- The chart-area request spine indexed by the actual original parent owners. -/
inductive ChartRequests (target : InverseRootPolynomial.Coordinate) (floor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      ParentOwners.Owners bank → Type 1
  /-- The empty original parent-owner bank needs no chart-area requests. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor .nil
  /-- Retain one actual parent request and the remaining request spine on their original owners. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      {first : ParentOwners.OwnedEndpoints regular cell} {rest : ParentOwners.Owners bank}
      (head : ChartAreaRequest.AreaRequest comparison first target floor) (tail :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor rest) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor (.cons
        (comparison := comparison) first rest)

constructive_injectivity ChartRequests

namespace ChartRequests

/-- Build one chart-area request per original parent owner before selecting a shared sample. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      (owners : ParentOwners.Owners bank) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners
  | _, _, .nil => .nil
  | _, _, .cons first rest => .cons (AreaRequest.build _ first target positive floor)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests.build target positive floor
    rest)

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read the sufficient common source-model stage of all original parent requests, retaining the caller floor. -/
@[expose] def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners → Nat
  | _, _, _, .nil => floor
  | _, _, _, .cons head tail => max head.mesh.index tail.maximum

/-- Read the sufficient common spatial depth from every retained parent request. -/
@[expose] def depthMaximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners → Nat
  | _, _, _, .nil => 0
  | _, _, _, .cons head tail => max head.spatial.depth tail.depthMaximum

end ChartRequests

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index minimum : Nat} {box :
  Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The actual chart meshes indexed by the original request spine and one shared cap sample. -/
inductive ChartPlans (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners → Type 1
  /-- The empty request spine has no actual chart meshes. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum .nil
  /-- Retain one actual chart mesh and the remaining meshes on the same original sample and request spine. -/ | cons
    {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      {first : ParentOwners.OwnedEndpoints regular cell} {rest : ParentOwners.Owners bank}
      {head : ChartAreaRequest.AreaRequest comparison first target floor} {tail :
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor rest}
      (chart : VertexTree.ChartMesh head.mesh capSample minimum) (charts :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum tail) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum (.cons head
        tail)

constructive_injectivity ChartPlans

namespace ChartPlans

/-- Cache every actual chart mesh on the supplied shared cap sample and retained reading floor. -/
@[expose] def build (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail => .cons (ChartMesh.build head.mesh capSample minimum)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.build capSample minimum tail)

/-- Read the common sufficient endpoint-reading stage of the cached actual chart meshes. -/
@[expose] def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests → Nat
  | _, _, _, _, .nil => minimum
  | _, _, _, _, .cons head tail => max head.stage tail.maximum

variable {depth readingIndex : Nat} {source :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}

/-- The dependent product of actual chart evaluations on the original compared parent cells. -/
@[expose] def EvaluationData (readingIndex : Nat) : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  {bank : ParentBank.Bank regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests →
      ParentPaths.ComparedCells source capSample depth bank → Type 1
  | _, _, _, _, .nil, .nil => PUnit
  | _, _, _, _, .cons head tail, .cons cell cells =>
      AreaRequest.Evaluation head cell readingIndex ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex
        tail cells

/-- Evaluate every retained chart plan using the same supplied source and cap samples at sufficient common model,
spatial and reading stages. -/
@[expose] def evaluate : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} →
      (plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → requests.maximum ≤ index → requests.depthMaximum ≤
      depth →
    plans.maximum ≤ readingIndex →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells
  | _, _, _, _, .nil, .nil, _, _, _ => ⟨⟩
  | _, _, _, _, .cons head tail, .cons cell cells, later, fineLater, readingLater =>
      ⟨AreaRequest.evaluate _ head cell ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _
        _).trans fineLater)
        readingIndex ((Data.Nat.Order.le_max_left _ _).trans readingLater),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.evaluate tail cells
          ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans fineLater)
          ((Data.Nat.Order.le_max_right _ _).trans readingLater)⟩

/-- The original endpoint-request spine is certified from the chart data; no endpoint factor, coordinate or numerical
value is evaluated a second time. -/
@[expose] def endpointReadings {pairTarget : InverseRootPolynomial.Coordinate} {pairFloor : Nat} :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} →
      (plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells
      →
    (pairs : ParentEndpoints.EndpointRequests pairTarget pairFloor owners) → pairs.maximum ≤ index →
      pairs.readingMaximum ≤ readingIndex →
    EndpointRequests.EvaluationData (readingIndex := readingIndex) pairs cells
  | _, _, _, _, .nil, .nil, _, .nil, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, .cons pair rest, later, readingLater =>
      ⟨(Evaluation.endpointPair evaluated.1 pair ((Data.Nat.Order.le_max_left _ _).trans later)
        ((Data.Nat.Order.le_max_left _ _).trans readingLater)).pair,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.endpointReadings tail cells
          evaluated.2 rest ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans
          readingLater)⟩

end ChartPlans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
