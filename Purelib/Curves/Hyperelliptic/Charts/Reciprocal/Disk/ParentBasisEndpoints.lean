module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-! Basis source endpoint acquisition on every cell of the retained parent. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
  Nat}

/-- The dependent basis source endpoint requests on every cell of the original retained parent chart spine. -/
def BasisEndpointRequests (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget :
  InverseRootPolynomial.Coordinate) (sourceFloor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
      ParentChartRequests.ChartRequests target floor owners → Type 2
  | _, _, _, .nil => PUnit
  | _, _, _, .cons head tail => Mesh.BasisEndpoints head.mesh covers sourceTarget sourceFloor ×
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget
        sourceFloor tail

namespace BasisEndpointRequests

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

/-- Prepare each original cell's basis source endpoints and midpoint tree at the positive target and retained source
floor. -/
def build (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget : InverseRootPolynomial.Coordinate)
  (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget
      sourceFloor requests
  | _, _, _, .nil => ⟨⟩
  | _, _, _, .cons head tail =>
      ⟨BasisEndpoints.build head.mesh covers sourceTarget positive sourceFloor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests.build covers
          sourceTarget positive sourceFloor tail⟩

/-- The maximum source-polynomial stage of all retained cell requests, preserving the source floor on an empty spine. -/
def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget
      sourceFloor requests → Nat
  | _, _, _, .nil, _ => sourceFloor
  | _, _, _, .cons _ tail, sources => max sources.1.index
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests.maximum tail
    sources.2)

end BasisEndpointRequests

variable {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

/-- The dependent basis comparison plans sharing one original polynomial bank across all retained parent cells. -/
def BasisEndpointPlans (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget
      sourceFloor requests → Type 2
  | _, _, _, _, .nil, _ => PUnit
  | _, _, _, _, .cons head tail, sources => BasisEndpoints.Plan sources.1 head polynomials ×
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials tail
        sources.2

namespace BasisEndpointPlans

/-- Prepare every actual retained cell's endpoint comparison using the same original basis polynomial bank. -/
def build (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources
  | _, _, _, _, .nil, _ => ⟨⟩
  | _, _, _, _, .cons head tail, sources =>
      ⟨BasisEndpoints.Plan.build sources.1 head polynomials,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.build polynomials
        tail sources.2⟩

/-- The maximum reading stage of all retained basis endpoint plans, preserving the supplied minimum on an empty spine.
-/
def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources →
      Nat
  | _, _, _, _, .nil, _, _ => minimum
  | _, _, _, _, .cons _ tail, sources, planned => max planned.1.stage
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.maximum tail sources.2
    planned.2)

/-- The common basis reading threshold also pays every original chart request, so the anchor paths can be evaluated at
that same stage. -/
theorem original_le : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests) → (planned :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    plans.maximum ≤ planned.maximum plans sources
  | _, _, _, _, .nil, _, _ => le_rfl
  | _, _, _, _, .cons head tail, sources, planned => by
      apply Data.Nat.Order.max_le
      · have headLe : head.stage ≤ planned.1.stage := by
          rw [planned.1.stage_eq]
          exact Data.Nat.Order.le_max_left _ _
        exact headLe.trans (Data.Nat.Order.le_max_left _ _)
      · exact (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.original_le
          tail sources.2 planned.2).trans (Data.Nat.Order.le_max_right _ _)

variable {depth readingIndex : Nat} {source :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}

/-- The complete basis endpoint comparisons consuming the exact original cell and chart evaluations from one shared
numerical bank. -/
def Samples (numerical : BasisSourceLocations.SampleBank covers index) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources →
      Type 2
  | _, _, _, _, .nil, .nil, _, _, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned =>
      Plan.Evaluation planned.1 numerical evaluated.1.vertices ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Samples numerical
          tail cells evaluated.2 sources.2 planned.2

/-- The complete parent consumes one existing basis numerical bank. Each cell uses its already-retained chart endpoint
readings and their owner proofs. -/
def evaluate (numerical : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests) → (planned :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    sources.maximum requests ≤ index → planned.maximum plans sources ≤ readingIndex →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Samples numerical plans cells
      evaluated sources planned
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, modelLater, readingLater =>
      ⟨planned.1.evaluate numerical evaluated.1.vertices branch ((Data.Nat.Order.le_max_left _ _).trans modelLater)
          ((Data.Nat.Order.le_max_left _ _).trans readingLater),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.evaluate numerical
          branch tail cells evaluated.2 sources.2 planned.2
          ((Data.Nat.Order.le_max_right _ _).trans modelLater) ((Data.Nat.Order.le_max_right _ _).trans readingLater)⟩

variable {edges : List Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners}

set_option genInjectivity false in
/-- The acquired original parent chart paths and all dependent basis endpoint comparisons at one cached reading stage.

The common stage also retains the supplied external reading floor. -/
structure Acquisition (numerical : BasisSourceLocations.SampleBank covers index)
    (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
      capSample depth bank)
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests)
    (planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans
      sources) (readingFloor : Nat) where
  /-- The actual common reading stage used by the original chart and basis endpoint evaluations. -/ readingIndex : Nat
  /-- The actual reading stage is exactly the maximum of the supplied floor and complete retained basis plan threshold.
  -/
  readingIndex_eq : readingIndex = max readingFloor (planned.maximum plans sources)
  /-- The original chart path evaluations acquired once at the retained common reading stage. -/ original :
    ChartPlans.EvaluationData readingIndex plans cells
  /-- The basis endpoint comparisons consuming those exact original path readings and the shared numerical bank. -/
    endpoints : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Samples numerical
    plans cells original sources planned

constructive_injectivity Acquisition

/-- Acquire the anchor paths once at the shared threshold, then consume their retained roots for every basis endpoint. A
larger join threshold can be supplied as the reading floor before either evaluation occurs. -/
def acquire (numerical : BasisSourceLocations.SampleBank covers index)
    (plans : ParentChartRequests.ChartPlans capSample minimum requests) (cells : ParentPaths.ComparedCells source
      capSample depth bank)
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointRequests covers
      sourceTarget sourceFloor requests)
    (planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans polynomials plans
      sources) (readingFloor : Nat)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : requests.maximum ≤ index) (sourceLater : sources.maximum requests ≤ index)
    (spatial : requests.depthMaximum ≤ depth) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Acquisition numerical plans
      cells sources planned readingFloor :=
  let readingIndex := max readingFloor (planned.maximum plans sources)
  let original := ChartPlans.evaluate (readingIndex := readingIndex) plans cells modelLater spatial
    ((planned.original_le plans sources).trans (Data.Nat.Order.le_max_right _ _))
  ⟨readingIndex, rfl, original,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.evaluate numerical branch plans
    cells original sources planned sourceLater (Data.Nat.Order.le_max_right _ _)⟩

end BasisEndpointPlans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Acquisition

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans.Acquisition
