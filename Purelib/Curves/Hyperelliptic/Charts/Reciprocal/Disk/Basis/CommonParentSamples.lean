module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

public section

/-! Prepare all radial fans from the acquired bank, then materialize every
parent at one shared radial depth without repeating root acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count}
  {basis : BasisBounds bounds}
  {allowance coefficientTarget : Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  GaussianVector genus}

/-- The original radial-fan preparations on every acquired common-parent reading. -/
@[expose] def FanPreparations (energyFloor : Nat) : {parents : List (CenteredEdge curve
  differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    Readings anchors sources bank plans inputs stage → Type 2
  | _, .nil, _, _, _, _, _ => PUnit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings =>
      EnergyPreparation bank.1.request.charts.requests plans.1.charts readings.1.readings
        allowance energyFloor ×
        CommonParentSamples.FanPreparations energyFloor tail
          sources.tail bank.2 plans.2 inputs.2 readings.2

/-- Prepare every radial fan from the retained acquired parent bank without repeating root acquisition. -/
@[expose] def prepareFans (energyFloor : Nat) : {parents : List (CenteredEdge curve
  differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    FanPreparations energyFloor anchors sources
      bank plans inputs readings
  | _, .nil, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings =>
      (Acquisition.prepareFans readings.1 energyFloor,
        CommonParentSamples.prepareFans energyFloor tail
        sources.tail bank.2 plans.2 inputs.2 readings.2)

/-- The maximum requested radial depth across the retained fan preparations. -/
@[expose] def FanPreparations.depth : {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    FanPreparations energyFloor anchors sources
      bank plans inputs readings → Nat
  | _, .nil, _, _, _, _, _, _ => energyFloor
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared =>
      max prepared.1.radialDepth (depth tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2)

/-- The complete retained common-parent samples at one coefficient vector and shared radial depth. -/
@[expose] def Samples (coefficients : GaussianVector genus) (radialDepth : Nat) :
    {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    FanPreparations energyFloor anchors sources
      bank plans inputs readings → Type 2
  | _, .nil, _, _, _, _, _, _ => PUnit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared =>
      Acquisition.Sample readings.1 prepared.1 inputs.1.originals coefficients radialDepth ×
        CommonParentSamples.Samples coefficients radialDepth
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2

/-- Materialize all original parent samples at a common paid radial depth.

Every sample reuses its acquired readings, original primitive bank and retained fan preparation. -/
@[expose] def sample (coefficients : GaussianVector genus)
    (parameters : RadialTriangles.Parameters radialDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {parents : List (CenteredEdge curve differential)} →
    (anchors : ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : Plans capSample polynomials minimum anchors sources bank) → (inputs :
      NumericalBank index anchors sources) →
    (readings : Readings anchors sources bank plans inputs stage) →
    (prepared : FanPreparations energyFloor
      anchors sources bank plans inputs readings) →
    prepared.depth anchors sources bank plans inputs readings ≤ radialDepth →
    Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared
  | _, .nil, _, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, later =>
      (Acquisition.sample readings.1 prepared.1 inputs.1.originals coefficients parameters branch
        ((Nat.Order.le_max_left ..).trans later),
        CommonParentSamples.sample coefficients parameters
          branch tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2
          ((Nat.Order.le_max_right ..).trans later))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
