module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples
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
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisPath
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSamples

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Cached complete signed boundary data for the retained parent chart path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisJoinErrors (BasisJoinSample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary (chartFirstRoot chartLastRoot
  basisJoinedTrace)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisPath (basisJoinedPath basisJoinedPath_total
  basisJoinedPath_trace)
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

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {energyTarget joinTarget : Coordinate} {energyFloor energyDepth :
    Nat}

set_option genInjectivity false in
/-- Retained boundary data for the actual joined root-chart path. The cell residual is computed from cached totals,
never by reacquiring fan energies. -/
structure BasisBoundarySample
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (joinTarget : InverseRootPolynomial.Coordinate)
      where
  /-- The cached signed homogeneous cell energy values in original retained cell order. -/ values : List
    InverseRootPolynomial.Gaussian
  /-- The energy value cache equals the actual original cell evaluations. -/ values_eq : values = BasisEnergyData.values
    coefficients plans cells evaluated energies
  /-- The cached total of all retained original signed cell energies. -/ energy : InverseRootPolynomial.Gaussian
  /-- The energy cache is exactly the Gaussian sum of the retained original cell values. -/ energy_eq : energy =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The original energy total satisfies its homogeneous signed lower bound with the actual retained cell count. -/
    lower : -(PreparedObservationCoercivity.coefficientNormSq coefficients * ((edges.length :
    InverseRootPolynomial.Coordinate) * energyTarget)) ≤ energy.im / 4
  /-- The actual previously certified original internal join defects and their retained total. -/ joins :
    ParentBasisJoinErrors.BasisJoinSample polynomials coefficients energyDepth plans cells evaluated joinTarget
  /-- The cached complete original joined chart increment path. -/ path : List InverseRootPolynomial.Gaussian
  /-- The path cache is exactly the original cell increments with every actual retained connector. -/ path_eq : path =
    ParentBasisPath.basisJoinedPath polynomials coefficients plans cells evaluated
  /-- The cached total and area summary of that exact original joined path. -/ summary : IncrementArea.Summary path
  /-- The cached actual first root coordinate of the original retained chart spine. -/ firstRoot :
    InverseRootPolynomial.Gaussian
  /-- The first root cache reads the original retained chart bank. -/ first_root : firstRoot =
    ParentBasisBoundary.chartFirstRoot plans cells evaluated
  /-- The cached actual last root coordinate of the original retained chart spine. -/ lastRoot :
    InverseRootPolynomial.Gaussian
  /-- The last root cache reads the original retained chart bank. -/ last_root : lastRoot =
    ParentBasisBoundary.chartLastRoot plans cells evaluated
  /-- The cached original coefficient-weighted primitive value at the actual first root. -/ firstValue :
    InverseRootPolynomial.Gaussian
  /-- The first value cache uses the original polynomial bank and retained first root. -/ first_value : firstValue =
    polynomials.value coefficients firstRoot
  /-- The cached original coefficient-weighted primitive value at the actual last root. -/ lastValue :
    InverseRootPolynomial.Gaussian
  /-- The last value cache uses the original polynomial bank and retained last root. -/ last_value : lastValue =
    polynomials.value coefficients lastRoot
  /-- The complete actual joined path total is its retained last primitive value minus the first. -/ total_eq :
    summary.total = lastValue - firstValue
  /-- The cached original first radial area at the retained common energy depth. -/ firstRadial :
    InverseRootPolynomial.Gaussian
  /-- The first radial cache is exactly the original primitive radial area at the actual first root. -/ first_radial :
    firstRadial = RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth firstRoot
  /-- The cached original last radial area at the retained common energy depth. -/ lastRadial :
    InverseRootPolynomial.Gaussian
  /-- The last radial cache is exactly the original primitive radial area at the actual last root. -/ last_radial :
    lastRadial = RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth lastRoot
  /-- The cached complete original uncentered chart trace area. -/ trace : InverseRootPolynomial.Gaussian
  /-- The trace cache reads the actual original joined path with its retained initial value. -/ trace_eq : trace =
    IncrementArea.traceArea firstValue path
  /-- The cached complete signed cell residual computed from the original retained totals. -/ cellError :
    InverseRootPolynomial.Gaussian
  /-- The residual cache equals the sum of the actual original per-cell boundary discrepancies. -/ cell_error :
    cellError = Data.Gaussian.Norm.Sum.Basic.gaussianSum (BasisEnergyData.cellErrors coefficients plans cells
    evaluated energies)
  /-- The original complete energy-versus-boundary discrepancy is the retained cell residual minus the actual join
    defect total. -/ discrepancy : energy - (-trace + lastRadial - firstRadial) = cellError - joins.total

constructive_injectivity BasisBoundarySample

namespace BasisBoundarySample

/-- Consume the previously certified join sample and acquire each cell's homogeneous area once. All subsequent
comparisons use the retained totals. -/
def build (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated)
    (joins : ParentBasisJoinErrors.BasisJoinSample polynomials coefficients energyDepth plans cells evaluated
      joinTarget) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample.BasisBoundarySample energies coefficients
      joinTarget := by
  let values := BasisEnergyData.values coefficients plans cells evaluated energies
  let energy := Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  let path := ParentBasisPath.basisJoinedPath polynomials coefficients plans cells evaluated
  let summary := IncrementArea.Summary.build path
  let firstRoot := ParentBasisBoundary.chartFirstRoot plans cells evaluated
  let lastRoot := ParentBasisBoundary.chartLastRoot plans cells evaluated
  let firstValue := polynomials.value coefficients firstRoot
  let lastValue := polynomials.value coefficients lastRoot
  have totalEq : summary.total = lastValue - firstValue :=
    summary.total_eq.trans (ParentBasisPath.basisJoinedPath_total polynomials coefficients plans cells evaluated)
  let firstRadial := RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth firstRoot
  let lastRadial := RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth lastRoot
  let trace := summary.area + BoundaryRibbon.area firstValue lastValue
  have traceEq : trace = IncrementArea.traceArea firstValue path := by
    rw [IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq, totalEq,
      BoundaryRibbon.area_sub_self_right]
  have identity : energy - (-trace + lastRadial - firstRadial) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (BasisEnergyData.cellErrors coefficients plans cells evaluated
        energies) - joins.total := by
    rw [traceEq, joins.total_eq, joins.errors_eq]
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum (BasisEnergyData.values coefficients plans cells evaluated
      energies) -
      (-IncrementArea.traceArea (polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells
        evaluated))
        (ParentBasisPath.basisJoinedPath polynomials coefficients plans cells evaluated) + _ - _) = _
    rw [ParentBasisPath.basisJoinedPath_trace]
    exact BasisEnergyData.boundary_identity coefficients plans cells evaluated energies
  let cellError := energy - (-trace + lastRadial - firstRadial) + joins.total
  have cellEq : cellError = Data.Gaussian.Norm.Sum.Basic.gaussianSum (BasisEnergyData.cellErrors coefficients plans
    cells evaluated energies) := by
    dsimp only [cellError]
    rw [identity]
    ring1
  exact ⟨values, rfl, energy, rfl, BasisEnergyData.lower coefficients plans cells evaluated energies, joins,
    path, rfl, summary, firstRoot, rfl, lastRoot, rfl, firstValue, rfl, lastValue, rfl, totalEq,
    firstRadial, rfl, lastRadial, rfl, trace, traceEq, cellError, cellEq, by dsimp only [cellError]; ring1⟩

end BasisBoundarySample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
