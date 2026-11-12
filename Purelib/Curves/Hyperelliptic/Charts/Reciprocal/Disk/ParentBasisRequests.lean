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
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar} {parent :
    Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

/-- The inexpensive homogeneous radial requests for every actual retained parent cell.

One shared polynomial-bound cache supplies the whole original chart spine before a common fan mesh is selected. -/
def BasisEnergyRequests (bounds : RegularBasisBounds polynomials RootRadialGeometry.domain) (energyTarget
  : Coordinate) (energyFloor : Nat) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      {owners : Owners bank} →
    {requests : ChartRequests target floor owners} → (plans : ChartPlans
      capSample minimum requests) →
    (cells : ComparedCells source capSample depth bank) → EvaluationData readingIndex plans cells
      → Type
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      RegularBasisRequest bounds evaluated.1.vertices.path.segments.length energyTarget energyFloor ×
        ParentBasisRequests.BasisEnergyRequests bounds energyTarget
          energyFloor tail cells evaluated.2

namespace BasisEnergyRequests

/-- Prepare the original homogeneous energy request for each actual evaluated cell using the same retained coefficient
bounds. -/
def build (bounds : RegularBasisBounds polynomials RootRadialGeometry.domain) (energyTarget :
  Coordinate)
    (positive : 0 < energyTarget) (energyFloor : Nat) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      {owners : Owners bank} →
    {requests : ChartRequests target floor owners} → (plans : ChartPlans
      capSample minimum requests) →
    (cells : ComparedCells source capSample depth bank) → (evaluated : EvaluationData
      readingIndex plans cells) →
    BasisEnergyRequests bounds energyTarget energyFloor
      plans cells evaluated
  | _, _, _, _, .nil, .nil, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      ⟨RegularBasisRequest.build bounds evaluated.1.vertices.path.segments.length energyTarget positive energyFloor,
        BasisEnergyRequests.build bounds
          energyTarget positive energyFloor tail cells evaluated.2⟩

variable {bounds : RegularBasisBounds
  polynomials RootRadialGeometry.domain} {energyTarget :
  Coordinate} {energyFloor : Nat}

/-- The maximum actual cell fan depth, retaining the original energy floor for an empty spine. -/
def maximum : {edges : List ParameterEdge} → {bank : Bank regular data
  edges} → {owners : Owners bank} →
    {requests : ChartRequests target floor owners} → {plans : ChartPlans
      capSample minimum requests} →
    {cells : ComparedCells source capSample depth bank} → {evaluated : EvaluationData
      readingIndex plans cells} →
    BasisEnergyRequests bounds energyTarget energyFloor
      plans cells evaluated → Nat
  | _, _, _, _, .nil, .nil, _, _ => energyFloor
  | _, _, _, _, .cons _ _, .cons _ _, _, requests => max requests.1.depth
    (BasisEnergyRequests.maximum requests.2)

end BasisEnergyRequests

/-- The actual retained cell energy evaluations at one exact common radial depth.

Each original chart path keeps its own energy certificate and depth equality, while the dependent tail preserves its
original cells. -/
def BasisEnergyData {polynomials : RegularBasisPolynomials cap index box} (energyTarget :
  Coordinate) (energyFloor energyDepth : Nat) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      {owners : Owners bank} →
    {requests : ChartRequests target floor owners} → (plans : ChartPlans
      capSample minimum requests) →
    (cells : ComparedCells source capSample depth bank) → EvaluationData readingIndex plans cells
      → Type 1
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      { energy : RequestedBasisEnergy evaluated.1.vertices.path.segments polynomials energyTarget energyFloor
        // energy.request.depth = energyDepth } ×
        ParentBasisRequests.BasisEnergyData (polynomials :=
          polynomials) energyTarget energyFloor energyDepth tail cells evaluated.2

namespace BasisEnergyRequests

variable {bounds : RegularBasisBounds
  polynomials RootRadialGeometry.domain} {energyTarget :
  Coordinate} {energyFloor energyDepth : Nat}

open Purelib.Data in
/-- Existing chart readings and sources are reused. The common mesh is passed down the whole spine; no already-built fan
is discarded or rebuilt. -/
def evaluate (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : Parameters energyDepth) :
    {edges : List ParameterEdge} → {bank : Bank regular data edges} →
      {owners : Owners bank} →
    {requests : ChartRequests target floor owners} → (plans : ChartPlans
      capSample minimum requests) →
    (cells : ComparedCells source capSample depth bank) → (evaluated : EvaluationData
      readingIndex plans cells) →
    (energyRequests : BasisEnergyRequests bounds
      energyTarget energyFloor plans cells evaluated) → energyRequests.maximum ≤ energyDepth →
    BasisEnergyData (polynomials := polynomials)
      energyTarget energyFloor energyDepth plans cells evaluated
  | _, _, _, _, .nil, .nil, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, requests, later =>
      ⟨⟨RequestedBasisEnergy.buildWithRequest evaluated.1.vertices.path.segments polynomials
          (basisFanGeometry evaluated.1 branch oriented) bounds
          (requests.1.atDepth energyDepth ((Nat.Order.le_max_left _ _).trans later)) parameters, rfl⟩,
        BasisEnergyRequests.evaluate branch
          oriented parameters tail cells evaluated.2 requests.2 ((Nat.Order.le_max_right _ _).trans later)⟩

end BasisEnergyRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
