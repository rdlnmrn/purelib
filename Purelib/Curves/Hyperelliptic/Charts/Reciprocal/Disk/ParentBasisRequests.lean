module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Energy

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Shared homogeneous radial preparation for every retained cell of a parent

All inexpensive accuracy requests are collected before a single fan is
built. One polynomial-bound cache and one final radial mesh serve the
original chart spine, including cells with different required depths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry.AreaRequest.Evaluation (basisFanGeometry)
open Purelib.Riemann.RootContinuation

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

/-- The inexpensive homogeneous radial requests for every actual retained parent cell.

One shared polynomial-bound cache supplies the whole original chart spine before a common fan mesh is selected. -/
def BasisEnergyRequests (bounds : CapBasisBounds.RegularBasisBounds polynomials RootRadialGeometry.domain) (energyTarget
  : InverseRootPolynomial.Coordinate) (energyFloor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → Type
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      CapBasisRequest.RegularBasisRequest bounds evaluated.1.vertices.path.segments.length energyTarget energyFloor ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests bounds energyTarget
          energyFloor tail cells evaluated.2

namespace BasisEnergyRequests

/-- Prepare the original homogeneous energy request for each actual evaluated cell using the same retained coefficient
bounds. -/
def build (bounds : CapBasisBounds.RegularBasisBounds polynomials RootRadialGeometry.domain) (energyTarget :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < energyTarget) (energyFloor : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests bounds energyTarget energyFloor
      plans cells evaluated
  | _, _, _, _, .nil, .nil, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      ⟨RegularBasisRequest.build bounds evaluated.1.vertices.path.segments.length energyTarget positive energyFloor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests.build bounds
          energyTarget positive energyFloor tail cells evaluated.2⟩

variable {bounds : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials Purelib.Riemann.RootContinuation.RootRadialGeometry.domain} {energyTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}

/-- The maximum actual cell fan depth, retaining the original energy floor for an empty spine. -/
def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → {plans : ParentChartRequests.ChartPlans
      capSample minimum requests} →
    {cells : ParentPaths.ComparedCells source capSample depth bank} → {evaluated : ChartPlans.EvaluationData
      readingIndex plans cells} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests bounds energyTarget energyFloor
      plans cells evaluated → Nat
  | _, _, _, _, .nil, .nil, _, _ => energyFloor
  | _, _, _, _, .cons _ _, .cons _ _, _, requests => max requests.1.depth
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests.maximum requests.2)

end BasisEnergyRequests

/-- The actual retained cell energy evaluations at one exact common radial depth.

Each original chart path keeps its own energy certificate and depth equality, while the dependent tail preserves its
original cells. -/
def BasisEnergyData {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box} (energyTarget :
  InverseRootPolynomial.Coordinate) (energyFloor energyDepth : Nat) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → Type 1
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      { energy : Evaluation.RequestedBasisEnergy evaluated.1.vertices.path.segments polynomials energyTarget energyFloor
        // energy.request.depth = energyDepth } ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyData (polynomials :=
          polynomials) energyTarget energyFloor energyDepth tail cells evaluated.2

namespace BasisEnergyRequests

variable {bounds : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials Purelib.Riemann.RootContinuation.RootRadialGeometry.domain} {energyTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

open Purelib.Data in
/-- Existing chart readings and sources are reused. The common mesh is passed down the whole spine; no already-built fan
is discarded or rebuilt. -/
def evaluate (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (energyRequests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests bounds
      energyTarget energyFloor plans cells evaluated) → energyRequests.maximum ≤ energyDepth →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyData (polynomials := polynomials)
      energyTarget energyFloor energyDepth plans cells evaluated
  | _, _, _, _, .nil, .nil, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, requests, later =>
      ⟨⟨RequestedBasisEnergy.buildWithRequest evaluated.1.vertices.path.segments polynomials
          (Evaluation.basisFanGeometry evaluated.1 branch oriented) bounds
          (requests.1.atDepth energyDepth ((Nat.Order.le_max_left _ _).trans later)) parameters, rfl⟩,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests.BasisEnergyRequests.evaluate branch
          oriented parameters tail cells evaluated.2 requests.2 ((Nat.Order.le_max_right _ _).trans later)⟩

end BasisEnergyRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
