module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration
public import Purelib.Integration.Path.HomogeneousTraceConnection
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Paid restored parents compose on their literal paths and endpoint potentials. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisConnection

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample (BasisBoundarySample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBudgets (BasisBoundaryBudgets)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (boundaryEnergy_sub_budget_le)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound (ParentBasisBoundaryBudget)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound (ParentBasisBoundaryBudget)
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

namespace ParentBasisRestorationAllowance

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {allowance energyTarget : Coordinate} {energyFloor energyDepth :
    Nat}

/-- Use the restored parent's cached summary and paid energy bound as one segment of the complete exterior connection.
Its path remains in the type. -/
def connection (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length allowance)
    {requests : ParentChartRequests.ChartRequests allocation.target floor owners} {plans :
      ParentChartRequests.ChartPlans capSample minimum requests}
    {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated : ChartPlans.EvaluationData readingIndex
      plans cells}
    {energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients allocation.target}
    (restored : BasisBoundarySample.EndpointRestoration sample allocation.target allocation.target)
    (budget : ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (previous previousPotential :
      InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (restored.firstValue - previous) ≤ allocation.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (joined : Data.Gaussian.Norm.Basic.normSq (restored.joinError previous previousPotential) ≤
      (80 * allocation.target + 2 * allocation.target) * (PreparedObservationCoercivity.coefficientNormSq coefficients)
        ^ 2) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients (restored.path previous)
      previous restored.lastValue previousPotential restored.lastPotential ((edges.length :
        InverseRootPolynomial.Coordinate) * energyTarget + allowance) := by
  let summary := restored.summary previous
  let trace := summary.area + BoundaryRibbon.area previous summary.total
  have traceEq : trace = IncrementArea.traceArea previous (restored.path previous) := by
    rw [IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq]
  let corrected := -trace + restored.lastPotential - previousPotential
  have lower := ParentBasisRestorationAllowance.trace_lower allocation restored budget branch previous previousPotential
    gap joined
  rw [← traceEq] at lower
  exact ⟨summary, restored.total previous, trace, traceEq, corrected, rfl, lower⟩

end ParentBasisRestorationAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisConnection
