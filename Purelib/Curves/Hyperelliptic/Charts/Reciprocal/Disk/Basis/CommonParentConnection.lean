module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
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
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
public import Purelib.Integration.Path.Homogeneous.FamilyConnection
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Integration.Path.IncrementArea

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Data.Rat

open Purelib.Integration.Budget.Trace

open Purelib.Integration.Path

open Purelib.Integration.Path.Homogeneous

open Purelib.Integration.Path.Homogeneous.FamilyConnection

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-! Restore and compose the acquired parent bank in its original order.
The family retains the literal source-detour paths and endpoint potentials. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank (counts)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank (Junctions)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : BasisBounds bounds}
  {allowance coefficientTarget : Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)
open Purelib.Integration.Path.Homogeneous.FamilyConnection (BasisTraceFamily)
open Purelib.Data.Rat.Fraction.Compatibility

namespace Samples

/-- The literal restored parent paths in their original order, joined at cached direct endpoints. -/
@[expose] def restoredPaths : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared →
      InverseRootPolynomial.Gaussian → List (List InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _, _, _, _, _ => []
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, previous =>
      Acquisition.Sample.restoredPath samples.1 previous ::
        restoredPaths tail
        sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 samples.1.endpoints.last.2

/-- The last actual source endpoint and outgoing potential, retaining the supplied values for an empty bank. -/
@[expose] def lastValues : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared →
      InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian ×
      InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _, _, _, _, previous, potential => (previous, potential)
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, _, _ =>
      lastValues tail
        sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 samples.1.endpoints.last.2
        (Acquisition.Sample.outgoingPotential samples.1)

/-- The homogeneous trace on the original first restored parent, or the trivial datum for an empty bank. -/
@[expose] def HeadTrace : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared →
      InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian → Type
  | _, .nil, _, _, _, _, _, _, _, _, _ => PUnit
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples, previous, potential =>
      HomogeneousTraceConnection.HomogeneousTrace coefficients (Acquisition.Sample.restoredPath samples.1 previous)
        previous samples.1.endpoints.last.2
        potential (Acquisition.Sample.outgoingPotential samples.1) (allowance + allowance + allowance + allowance)

/-- Retain a homogeneous trace while displaying the original parent count with zero per-interval charge. -/
@[expose] def counted {path : List InverseRootPolynomial.Gaussian} {first last firstPotential lastPotential :
  InverseRootPolynomial.Gaussian}
    (trace : HomogeneousTraceConnection.HomogeneousTrace coefficients path first last firstPotential lastPotential
      (allowance + allowance + allowance + allowance)) (count : Nat) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients path first last firstPotential lastPotential
      ((count : InverseRootPolynomial.Coordinate) * 0 + (allowance + allowance + allowance + allowance)) := by
  rw [Fraction.Field.mul_zero_direct, _root_.zero_add]
  exact trace

/-- Compose the actual restored parent traces from a supplied first trace and paid retained junctions.

The family keeps literal source-detour paths, original interval counts and every cached endpoint potential. -/
@[expose] def familyFromHead (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (joins : BasisCommonParentBank.Junctions anchors sources bank) → joins.stage anchors sources bank ≤ stage →
    (previous potential : InverseRootPolynomial.Gaussian) →
      HeadTrace anchors sources bank
      plans inputs readings prepared samples previous potential →
    FamilyConnection.BasisTraceFamily coefficients 0 (allowance + allowance + allowance + allowance)
      (BasisCommonParentBank.counts anchors sources bank)
        (restoredPaths anchors sources
        bank plans inputs readings prepared samples previous)
      previous (lastValues anchors
        sources bank plans inputs readings prepared samples previous potential).1
      potential (lastValues anchors
        sources bank plans inputs readings prepared samples previous potential).2
  | _, .nil, _, _, _, _, _, _, _, _, _, previous, potential, _ => .nil previous potential
  | _, .cons _ _ _ .nil, _, bank, _, _, _, _, samples, _, _, _, _, head =>
      .cons (counted head
        bank.1.common.intervals.length) (.nil samples.1.endpoints.last.2 (Acquisition.Sample.outgoingPotential
        samples.1))
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, plans, inputs, readings, prepared, samples, joins, later, _, _, head =>
      .cons (counted head
        bank.1.common.intervals.length)
        (familyFromHead branch
          _ _ bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 joins.2
          ((Nat.Order.le_max_right ..).trans later) samples.1.endpoints.last.2 (Acquisition.Sample.outgoingPotential
            samples.1)
          (Acquisition.Sample.restoreAfter samples.1 samples.2.1 joins.1.request branch
            ((Nat.Order.le_max_left ..).trans later) ((Nat.Order.le_max_left ..).trans later)))

/-- The first actual direct endpoint and incoming potential, or zero values for an empty bank. -/
@[expose] def firstValues : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared →
      InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _, _, _, _ => (0, 0)
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples => (samples.1.endpoints.first.2, (Acquisition.Sample.incomingPotential
    samples.1))

/-- Restore the original first parent at its own cached direct starting endpoint. -/
@[expose] def firstTrace : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    HeadTrace anchors sources bank
      plans inputs readings prepared samples
      (firstValues anchors sources bank
        plans inputs readings prepared samples).1
      (firstValues anchors sources bank
        plans inputs readings prepared samples).2
  | _, .nil, _, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ _, _, _, _, _, _, _, samples => Acquisition.Sample.restoreFirst samples.1

variable {parents : List (CenteredEdge curve differential)}
  {anchors : ParentCovers parents} {sources :
    BasisParentSourceCovers parents}
  {bank : BasisCommonParentBank anchors
    sources basis allowance coefficientTarget coverFloor floor}
  {plans : Plans capSample polynomials
    minimum anchors sources bank} {inputs :
    NumericalBank index anchors sources}
  {readings : Readings anchors sources bank
    plans inputs stage}
  {prepared : FanPreparations energyFloor
    anchors sources bank plans inputs readings}

/-- Exact path, count and endpoint indices of the restored family. -/
@[expose] def Family (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs
  readings prepared) : Type :=
  let first := firstValues anchors
    sources bank plans inputs readings prepared samples
  let last := lastValues anchors
    sources bank plans inputs readings prepared samples first.1 first.2
  FamilyConnection.BasisTraceFamily coefficients 0 (allowance + allowance + allowance + allowance)
    (BasisCommonParentBank.counts anchors sources bank)
    (restoredPaths anchors sources bank
      plans inputs readings prepared samples first.1)
    first.1 last.1 first.2 last.2

/-- Complete family on the literal restored paths. The first source endpoint sets the initial potential; each subsequent
join reuses its scheduled request. -/
@[expose] def family (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs
  readings prepared)
    (joins : BasisCommonParentBank.Junctions anchors sources bank) (branch : HyperellipticReciprocal.originOrder curve =
      1)
    (later : joins.stage anchors sources bank ≤ stage) :
      Family samples :=
  familyFromHead branch anchors sources
    bank plans inputs readings prepared samples joins later
    (firstValues anchors sources bank
      plans inputs readings prepared samples).1
    (firstValues anchors sources bank
      plans inputs readings prepared samples).2
    (firstTrace anchors sources bank
      plans inputs readings prepared samples)

/-- A homogeneous trace on the flattened original restored paths at the supplied target budget.

Its endpoint and potential indices are the exact first and last values retained by the acquired parent bank. -/
@[expose] def PaidConnection (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans
  inputs readings prepared)
    (target : InverseRootPolynomial.Coordinate) : Type :=
  let first := firstValues anchors
    sources bank plans inputs readings prepared samples
  let last := lastValues anchors
    sources bank plans inputs readings prepared samples first.1 first.2
  HomogeneousTraceConnection.HomogeneousTrace coefficients
    (restoredPaths anchors sources bank
      plans inputs readings prepared samples first.1).flatten
    first.1 last.1 first.2 last.2 target

/-- The allowance is selected from the original number of parents before their requests are built. The count readback
pays the exact acquired family. -/
@[expose] def connectPaid {target : InverseRootPolynomial.Coordinate}
    (allocation : Family.BasisFamilyAllowance parents.length target)
    {bank : CommonParentBank.BasisCommonParentBank anchors sources basis allocation.allowance coefficientTarget
      coverFloor floor}
    {plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank} {inputs :
      CommonParentPlans.NumericalBank index anchors sources}
    {readings : CommonParentPlans.Readings anchors sources bank plans inputs stage}
    {prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings}
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (joins : BasisCommonParentBank.Junctions anchors sources bank) (branch : HyperellipticReciprocal.originOrder curve =
      1)
    (later : joins.stage anchors sources bank ≤ stage) :
      PaidConnection samples target :=
  BasisFamilyAllowance.connect allocation
    (family samples joins branch later)
    (BasisCommonParentBank.counts_length anchors sources bank)

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
