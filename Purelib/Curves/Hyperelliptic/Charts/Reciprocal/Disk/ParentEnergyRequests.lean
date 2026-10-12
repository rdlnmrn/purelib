module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
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

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Shared radial preparation for every retained cell of a parent

All inexpensive accuracy requests are collected before a single fan is
built. One polynomial-bound cache and one final radial mesh serve the
original chart spine, including cells with different required depths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests

open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyRequest)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation (RequestedEnergy)

variable {genus count index depth readingIndex floor minimum : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve
  genus}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {target : Normalization.InverseRootPolynomial.Coordinate}

/-- Dependent original fan-accuracy requests along the retained chart spine using one polynomial-bound cache. -/
@[expose] def EnergyRequests (bounds : Cap.EnergyBounds capSample
  RootContinuation.RootRadialGeometry.domain) (energyTarget : Normalization.InverseRootPolynomial.Coordinate)
  (energyFloor : Nat) :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells → Type
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      Cap.EnergyRequest bounds evaluated.1.vertices.path.segments.length
        energyTarget energyFloor ×
        EnergyRequests bounds energyTarget
          energyFloor tail cells evaluated.2

namespace EnergyRequests

/-- Collect each original chart's inexpensive energy request before selecting the shared radial depth. -/
@[expose] def build (bounds : Cap.EnergyBounds capSample
  RootContinuation.RootRadialGeometry.domain) (energyTarget : Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < energyTarget) (energyFloor : Nat) :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) → (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells) →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyRequests bounds energyTarget energyFloor plans cells
      evaluated
  | _, _, _, _, .nil, .nil, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      ⟨EnergyRequest.build bounds evaluated.1.vertices.path.segments.length energyTarget positive energyFloor,
        build bounds
          energyTarget positive energyFloor tail cells evaluated.2⟩

variable {bounds : Cap.EnergyBounds capSample
  RootContinuation.RootRadialGeometry.domain} {energyTarget : Normalization.InverseRootPolynomial.Coordinate}
  {energyFloor : Nat}

/-- Take the maximum of every original requested fan depth and the retained energy floor. -/
@[expose] def maximum : {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
  Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → {plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests} →
    {cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank} → {evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells} →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyRequests bounds energyTarget energyFloor plans cells
      evaluated → Nat
  | _, _, _, _, .nil, .nil, _, _ => energyFloor
  | _, _, _, _, .cons _ _, .cons _ _, _, requests => max requests.1.depth
    (maximum requests.2)

end EnergyRequests

/-- The original retained chart energies, each certified to use exactly the same common radial depth. -/
@[expose] def EnergyData (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor energyDepth : Nat)
  :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells → Type
      1
  | _, _, _, _, .nil, .nil, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated =>
      { energy : Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated.1
        energyTarget energyFloor // energy.request.depth = energyDepth } ×
        EnergyData energyTarget energyFloor
          energyDepth tail cells evaluated.2

namespace EnergyRequests

variable {bounds : Cap.EnergyBounds capSample
  RootContinuation.RootRadialGeometry.domain} {energyTarget : Normalization.InverseRootPolynomial.Coordinate}
  {energyFloor energyDepth : Nat}

/-- Existing chart readings and sources are reused. The common mesh is
passed down the whole spine; no already-built fan is discarded or rebuilt. -/
@[expose] def evaluate (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth) :
    {edges : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} → {owners :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank) → (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells) →
    (energyRequests : Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyRequests bounds energyTarget
      energyFloor plans cells evaluated) → energyRequests.maximum ≤ energyDepth →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyData energyTarget energyFloor energyDepth plans
      cells evaluated
  | _, _, _, _, .nil, .nil, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, requests, later =>
      ⟨⟨RequestedEnergy.buildWithRequest evaluated.1 branch oriented bounds
          (requests.1.atDepth energyDepth ((Data.Nat.Order.le_max_left _ _).trans later)) parameters, rfl⟩,
        evaluate branch oriented
          parameters tail cells evaluated.2 requests.2 ((Data.Nat.Order.le_max_right _ _).trans later)⟩

end EnergyRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
