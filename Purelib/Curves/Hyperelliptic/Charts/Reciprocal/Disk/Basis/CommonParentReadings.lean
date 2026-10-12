module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Acquire a parent's common-chart readings at the shared numerical and
root stages, then prepare its fan requests without resampling the roots. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace BasisCommonParentRequest

variable {coverFloor : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover
  covers coverFloor}
  {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}

set_option genInjectivity false in
/-- The retained common-chart polynomial plans and joint reading stage for one parent request. -/
structure Plan (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest common
  basis allowance coefficientTarget floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) where
  /-- The original chart plans using the supplied cap sample and polynomial bank. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample polynomials
    minimum request.charts.requests
  /-- The cached stage sufficient for the parent reading floor and all chart plans. -/ stage : Nat
  /-- The selected stage is the maximum of the original parent and chart thresholds. -/ stage_eq : stage = max
    request.readingFloor
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans.stage
    request.charts.requests charts)

constructive_injectivity Plan

namespace Plan

/-- Prepare the original chart plans and cache their sufficient joint reading stage. -/
@[expose] def build (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
  common basis allowance coefficientTarget floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan
      request capSample polynomials minimum :=
  let charts := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans.build
    capSample polynomials minimum request.charts.requests
  ⟨charts, max request.readingFloor
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans.stage
    request.charts.requests charts), rfl⟩

variable {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest common basis
  allowance coefficientTarget floor}

set_option genInjectivity false in
/-- The acquired original chart readings with their geometry, orientation and physical-junction stage certificate.

All fields refer to the same retained parent plan, supplied primitive banks and common stage. -/
structure Acquisition (plan :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan request capSample
  polynomials minimum)
    (anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index
      cover.mesh.edges)
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index)
      (stage : Nat) where
  /-- The acquired chart readings from the original anchor and source banks. -/ readings :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage request.charts.requests plan.charts
  /-- The retained geometry of those same chart readings. -/ geometry :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry request.charts.requests plan.charts readings
  /-- The certified orientation of those same chart readings. -/ orientation :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation.Orientation request.charts.requests plan.charts
    readings
  /-- The acquisition stage covers all original physical connector junctions. -/ joins_later :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage request.charts.requests
    request.connectors.junctions ≤ stage

constructive_injectivity Acquisition

/-- Acquire the original common-chart readings and their certified geometry and orientation at one sufficiently late
stage. -/
@[expose] def acquire (plan :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan request capSample
  polynomials minimum)
    (anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index
      cover.mesh.edges)
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (modelLater : request.index ≤ index) (stage : Nat) (readingLater : plan.stage ≤ stage) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition plan
      anchorBank bank stage := by
  have chartLater := (Purelib.Data.Nat.Order.le_max_right request.readingFloor
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans.stage
    request.charts.requests plan.charts)).trans
    (plan.stage_eq.symm.trans_le readingLater)
  let readings := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.read
    anchorBank bank branch stage request.charts.requests plan.charts
    (request.charts_le.trans modelLater) chartLater
  have geometry := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation.geometry_and_orientation
    request.coordinates request.arcs.angular branch oriented
    request.arcs.coordinate_le (le_min request.arcs.coordinate_tolerance request.arcs.angular_tolerance)
    request.charts.requests plan.charts readings
  have joinsLater := request.connectors_le.trans ((Purelib.Data.Nat.Order.le_max_left ..).trans
    (plan.stage_eq.symm.trans_le readingLater))
  exact ⟨readings, geometry.1, geometry.2, joinsLater⟩

/-- Prepare fan requests from the already acquired chart readings, preserving their roots and original parent allowance.
-/
@[expose] def Acquisition.prepareFans {plan :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan request capSample
  polynomials minimum}
    (acquired :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition plan
      anchorBank bank stage) (energyFloor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation request.charts.requests
      plan.charts acquired.readings allowance energyFloor :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation.build request.charts.requests
    plan.charts acquired.readings allowance request.positive energyFloor

end Plan
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
