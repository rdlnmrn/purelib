module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts

public section

/-! Construct the regular cap refinement and physical basis evaluations at one
shared depth from the retained polynomial bank. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawCapSampling

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSurfaceSchedule (SurfaceSchedule)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  (ReciprocalGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest (Evaluations
  evaluate)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {observations : ProtectedObservations original} {preparation : NewtonPreparation original} {radius :
    Rational}
  (gridData : RawEnergyGrid observations preparation radius)
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

variable {physicalMinimum physicalFloor stage : Nat} {box : Geometry.Rational.Box}
  (surfaceData : SurfaceSchedule gridData regular physicalMinimum physicalFloor)
  {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared :
    AllSurfacePreparation
    regular gridData.domains differential}
  (attached : CapAttachment
    prepared)
  (polynomials : RegularBasisPolynomials cap
    stage box)

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path.Dyadic in
set_option genInjectivity false in
/-- Retained cap request, radial geometry and basis evaluations.

Keeps the actual polynomial bounds, allowance request, attached reciprocal geometry and radial parameters, together with
caps and physical-basis evaluations at the same requested depth. -/
structure CapSampling where
  /-- Actual bounds for the retained regular basis polynomials. -/ bounds :
    RegularBasisBounds polynomials
  /-- Cap request at the raw-energy allowance and retained basis depth floor. -/ request :
    RegularBasisRequest bounds attached.caps.length (rawEnergyAllowance
    observations) surfaceData.schedule.basis.depth
  /-- Reciprocal geometry of the original cap attachment. -/ geometry :
    ReciprocalGeometry attached
  /-- Radial triangle parameters at the exact requested depth. -/ parameters : Parameters request.depth
  /-- Actual regular basis caps over those geometry and parameter owners. -/ caps :
    RegularBasisCap geometry parameters polynomials
  /-- Physical basis evaluations at the retained cap request depth. -/ evaluated :
    PhysicalBasisRequest.Evaluations surfaceData.schedule.basis
    polynomials request.depth

constructive_injectivity CapSampling

namespace CapSampling

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path.Dyadic in
/-- Construct cap samples in the unramified reciprocal chart.

Under origin order zero and the retained basis index bound, allocates the raw-energy allowance and reuses the resulting
depth for radial parameters, caps and basis evaluations. -/
@[expose] def build (chart : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (later : surfaceData.schedule.basis.index ≤ stage) : CapSampling gridData regular surfaceData attached polynomials
      :=
  let bounds := RegularBasisBounds.build polynomials
  let request := RegularBasisRequest.build bounds attached.caps.length
    (rawEnergyAllowance observations)
    (rawEnergyAllowance_positive observations) surfaceData.schedule.basis.depth
  let geometry := ReciprocalGeometry.build
    attached
  let parameters := Parameters.build request.depth
  let caps := RegularBasisCap.build geometry parameters polynomials
    chart
    (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations)
  let evaluated := PhysicalBasisRequest.evaluate
    surfaceData.schedule.basis polynomials chart later (depth := request.depth)
  ⟨bounds, request, geometry, parameters, caps, evaluated⟩

end CapSampling
end Purelib.Riemann.RootContinuation.NewtonRawCapSampling
