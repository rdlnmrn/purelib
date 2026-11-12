module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Shared radial requests and fan acquisition for the actual common chart
paths. All intervals consume one retained polynomial-bound and parameter bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy

open Purelib.Data

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : UniformReciprocalCover.Cover data} {covers :
    SourceLocations.BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)

/-- The original interval fan requests on one retained polynomial-bound bank.

Every entry keeps the actual acquired interval segment count, common energy target and supplied energy floor. -/
@[expose] def EnergyRequests (bounds : Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials RootRadialGeometry.domain)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Type
  | _, .nil, _, _ => PUnit
  | _, .cons _ tail, plans, readings =>
      RegularBasisRequest bounds
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments.length energyTarget energyFloor ×
        CommonChartEnergy.EnergyRequests bounds energyTarget
          energyFloor tail plans.2 readings.2

namespace EnergyRequests

/-- Prepare every actual interval fan request with the shared original polynomial bounds, target and floor. -/
@[expose] def build (bounds : Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
  RootRadialGeometry.domain)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    EnergyRequests bounds energyTarget energyFloor requests
      plans readings
  | _, .nil, _, _ => ⟨⟩
  | _, .cons _ tail, plans, readings =>
      ⟨RegularBasisRequest.build bounds
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments.length energyTarget positive energyFloor,
        EnergyRequests.build bounds
          energyTarget positive energyFloor tail plans.2 readings.2⟩

variable {bounds : Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
  RootRadialGeometry.domain} {energyTarget : Normalization.InverseRootPolynomial.Coordinate}
  {energyFloor : Nat}

/-- The maximum sufficient radial depth for the retained interval requests, including the empty-bank floor. -/
@[expose] def maximum : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    EnergyRequests bounds energyTarget energyFloor requests
      plans readings → Nat
  | _, .nil, _, _, _ => energyFloor
  | _, .cons _ _, _, _, energies => max energies.1.depth
    (EnergyRequests.maximum energies.2)

end EnergyRequests

/-- The dependent bank of actual acquired interval fan energies at one common retained radial depth. -/
@[expose] def Energies (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor energyDepth : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Type 1
  | _, .nil, _, _ => PUnit
  | _, .cons _ tail, plans, readings =>
      { energy : RequestedBasisEnergy
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments polynomials energyTarget energyFloor //
        energy.request.depth = energyDepth } ×
          CommonChartEnergy.Energies energyTarget energyFloor
          energyDepth tail plans.2 readings.2

namespace EnergyRequests

variable {bounds : Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
  RootRadialGeometry.domain}
  {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- The same fan implementation serves whole cells and common intervals.
No endpoint, polynomial or inverse sample is reacquired. -/
@[expose] def acquire (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    CommonChartOrientation.Orientation requests plans readings →
    (energies : EnergyRequests bounds energyTarget
      energyFloor requests plans readings) → energies.maximum ≤ energyDepth →
    Energies energyTarget energyFloor energyDepth requests
      plans readings
  | _, .nil, _, _, _, _, _ => ⟨⟩
  | _, .cons _ tail, plans, readings, oriented, energies, later =>
      let geometry : ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments := fun segment member =>
        let certified := oriented.1 segment member
        ⟨certified.1, certified.2.1, certified.2.2.le⟩
      ⟨⟨RequestedBasisEnergy.buildWithRequest
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments polynomials geometry bounds
          (energies.1.atDepth energyDepth ((Nat.Order.le_max_left _ _).trans later)) parameters, rfl⟩,
        EnergyRequests.acquire parameters
          tail plans.2 readings.2 oriented.2 energies.2 ((Nat.Order.le_max_right _ _).trans later)⟩

end EnergyRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
