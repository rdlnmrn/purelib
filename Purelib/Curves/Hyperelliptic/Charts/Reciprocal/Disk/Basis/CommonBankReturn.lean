module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
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
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Return estimates for the original acquired common-parent bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankReturn

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank
  BasisCommonParentEntry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank (counts)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank (Junctions)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank (LastJunction
  ClosingJunction)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank NumericalInput
  Readings)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
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

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open
  Reciprocal.Disk.Basis.CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample
  (returnScale returned_potential_bound)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples (lastValues firstValues)

variable {cover : Cover data} {targetSources :
  BasisSourceCovers parent}

/-- The actual last parent's outgoing potential approximates the supplied target sample's incoming potential.

The nonempty original parent bank and its retained closing junction determine the two endpoint owners and the paid
return bound. -/
private theorem lastReturn (branch : HyperellipticReciprocal.originOrder curve = 1)
    (target : CommonParentBank.BasisCommonParentEntry cover targetSources basis allowance coefficientTarget coverFloor
      floor)
    (targetPlan : BasisCommonParentRequest.Plan target.request capSample polynomials minimum)
    (targetInput : CommonParentPlans.NumericalInput cover targetSources index)
    (targetReading : Plan.Acquisition targetPlan targetInput.anchor targetInput.cells stage)
    (targetFans : CommonEnergyPreparation.EnergyPreparation target.request.charts.requests targetPlan.charts
      targetReading.readings allowance energyFloor)
    (targetSample : Acquisition.Sample targetReading targetFans targetInput.originals coefficients radialDepth) :
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
    (closing : BasisCommonParentBank.LastJunction target anchors sources bank) → closing.stage target anchors sources
      bank ≤ stage →
    (before beforePotential : InverseRootPolynomial.Gaussian) → parents ≠ [] →
    Data.Gaussian.Norm.Basic.normSq ((Samples.lastValues anchors sources bank plans inputs readings prepared
      samples before beforePotential).2 - (Acquisition.Sample.incomingPotential targetSample)) ≤
      Acquisition.Sample.returnScale (basis := basis) (allowance := allowance) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _ _ .nil, _, _, _, _, _, _, samples, closing, later, _, _, _ =>
      Acquisition.Sample.returned_potential_bound samples.1 targetSample closing.request branch later later
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, plans, inputs, readings, prepared, samples, closing, later, _, _, _ =>
      lastReturn branch target
        targetPlan targetInput targetReading targetFans targetSample
        _ _ bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 closing later
        samples.1.endpoints.last.2 (Acquisition.Sample.outgoingPotential samples.1) (by intro empty; cases empty)

/-- The closing request is tied to the literal final and initial parent samples, including the empty-bank base case. -/
theorem returned_bound (branch : HyperellipticReciprocal.originOrder curve = 1) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    (closing : BasisCommonParentBank.ClosingJunction anchors sources bank) → closing.stage anchors sources bank ≤ stage
      →
    let first := Samples.firstValues anchors sources bank plans inputs readings prepared samples
    Data.Gaussian.Norm.Basic.normSq ((Samples.lastValues anchors sources bank plans inputs readings prepared
      samples first.1 first.2).2 - first.2) ≤
      Acquisition.Sample.returnScale (basis := basis) (allowance := allowance) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, .nil, _, _, _, _, _, _, _, _, _ => by
      change Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) ≤ _
      rw [_root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (by
            decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 180)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
            basis.coefficient_nonnegative)) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  | _, .cons patch data cover tail, sources, bank, plans, inputs, readings, prepared, samples, closing, later =>
      lastReturn branch bank.1 plans.1
        inputs.1 readings.1 prepared.1 samples.1
        (.cons patch data cover tail) sources bank plans inputs readings prepared samples closing later
        samples.1.endpoints.first.2 (Acquisition.Sample.incomingPotential samples.1) (by intro empty; cases empty)

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankReturn
