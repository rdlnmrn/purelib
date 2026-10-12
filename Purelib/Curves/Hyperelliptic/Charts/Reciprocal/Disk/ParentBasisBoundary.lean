module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
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
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-! Exact signed boundary identity for the retained homogeneous parent cells. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyData)
open Purelib.Riemann.RootContinuation
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

/-- The actual first acquired root coordinate of the original cell bank, with zero for an empty bank. -/
def chartFirstRoot : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => 0
  | _, _, _, _, .cons _ _, .cons _ _, evaluated => evaluated.1.vertices.first.root.coordinate

/-- The actual last acquired root coordinate of the original cell bank, with zero for an empty bank. -/
def chartLastRoot : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => 0
  | _, _, _, _, .cons _ .nil, .cons _ .nil, evaluated => evaluated.1.vertices.last.root.coordinate
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated =>
      chartLastRoot (.cons next tail) (.cons
        nextCell cells) evaluated.2

/-- Signed trace including the edge between every pair of successive cells. -/
def basisJoinedTrace (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : {edges : List
      ClearSheetContinuation.Subdivision.ParameterEdge} →
      {bank : ParentBank.Bank regular data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → ChartPlans.EvaluationData readingIndex plans cells
      → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => 0
  | _, _, _, _, .cons _ .nil, .cons _ .nil, evaluated =>
      IncrementArea.traceArea (polynomials.value coefficients evaluated.1.vertices.first.root.coordinate)
        (evaluated.1.vertices.path.segments.map (fun segment =>
          polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
            segment.first.root.coordinate))
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated =>
      IncrementArea.traceArea (polynomials.value coefficients evaluated.1.vertices.first.root.coordinate)
        (evaluated.1.vertices.path.segments.map (fun segment =>
          polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
            segment.first.root.coordinate)) +
      BoundaryRibbon.area (polynomials.value coefficients evaluated.1.vertices.last.root.coordinate)
        (polynomials.value coefficients evaluated.2.1.vertices.first.root.coordinate) +
      basisJoinedTrace polynomials coefficients
        (.cons next tail) (.cons nextCell cells) evaluated.2

namespace BasisEnergyData

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- The signed per-cell discrepancy between each retained homogeneous energy area and its actual chart trace with both
radial endpoints. -/
def cellErrors (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth plans cells
      evaluated → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, energies =>
      (energies.1.val.area coefficients -
        (-IncrementArea.traceArea (polynomials.value coefficients evaluated.1.vertices.first.root.coordinate)
          (evaluated.1.vertices.path.segments.map (fun segment =>
            polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
              segment.first.root.coordinate)) +
          RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
            evaluated.1.vertices.last.root.coordinate -
          RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
            evaluated.1.vertices.first.root.coordinate)) ::
        cellErrors coefficients
          tail cells evaluated.2 energies.2

/-- All internal radial endpoints cancel with exactly the retained join defects. The two external radial terms remain,
with their original signs. -/
theorem boundary_identity (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data edges} {owners
      : ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans : ParentChartRequests.ChartPlans capSample
      minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated : ChartPlans.EvaluationData readingIndex
      plans cells)
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (BasisEnergyData.values coefficients plans cells evaluated energies) -
      (-Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace polynomials coefficients plans
        cells evaluated +
        RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot plans cells evaluated) -
        RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartFirstRoot plans cells evaluated)) =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (cellErrors coefficients plans
      cells evaluated energies) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (ParentBasisJoinErrors.basisJoinErrors polynomials coefficients
        energyDepth plans cells evaluated) := by
  induction plans with
  | nil =>
      cases cells
      simp only [BasisEnergyData.values,
        cellErrors,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_1,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_2,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_3,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartFirstRoot,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_1,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_2,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_3,
        ParentBasisJoinErrors.basisJoinErrors.eq_1,
        ParentBasisJoinErrors.basisJoinErrors.eq_2,
        ParentBasisJoinErrors.basisJoinErrors.eq_3, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      ring1
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases tail with
          | nil =>
              cases cells
              simp only [BasisEnergyData.values,
                cellErrors,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_1,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_2,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_3,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartFirstRoot,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_1,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_2,
                Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_3,
                ParentBasisJoinErrors.basisJoinErrors.eq_1,
                ParentBasisJoinErrors.basisJoinErrors.eq_2,
                ParentBasisJoinErrors.basisJoinErrors.eq_3, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
              ring1
          | cons next tail =>
              cases cells with
              | cons nextCell cells =>
                  have rest := ih (.cons nextCell cells) evaluated.2 energies.2
                  simp only [BasisEnergyData.values,
                    cellErrors,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_1,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_2,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.basisJoinedTrace.eq_3,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartFirstRoot,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_1,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_2,
                    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary.chartLastRoot.eq_3,
                    ParentBasisJoinErrors.basisJoinErrors.eq_1,
                    ParentBasisJoinErrors.basisJoinErrors.eq_2,
                    ParentBasisJoinErrors.basisJoinErrors.eq_3, Data.Gaussian.Norm.Sum.Basic.gaussianSum] at rest ⊢
                  have recover {first last total : Data.Gaussian.Basic.Canonical}
                      (identity : first - last = total) : first = total + last := by
                    calc
                      first = (first - last) + last := by ring1
                      _ = total + last := congrArg (· + last) identity
                  rw [recover rest]
                  ring1

end BasisEnergyData
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary

