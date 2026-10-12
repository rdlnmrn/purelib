module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins
import Mathlib.Algebra.Group.Defs
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

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation

open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! The scheduled closing join bounds the returned endpoint value itself. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankEndpointReturn

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank
  BasisCommonParentEntry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank NumericalInput
  Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank (Junctions)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank (LastJunction
  ClosingJunction)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples (lastValues firstValues)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples (firstValue_bound)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
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

variable {cover : Cover data} {targetSources :
  BasisSourceCovers parent}

/-- The paid final-to-target join bounds the returned endpoint of a nonempty original common-parent bank.

The estimate retains the actual terminal sample and target sample and scales by their shared coefficient norm. -/
private theorem lastEndpointReturn (branch : HyperellipticReciprocal.originOrder curve = 1)
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
      samples before beforePotential).1 - targetSample.endpoints.first.2) ≤
      (4 * allowance)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _ _ .nil, _, _, _, _, _, _, samples, closing, later, _, _, _ =>
      by
        have gap := PreparedComparison.incoming_gap
          samples.1 targetSample closing.request branch later later
        have paid : target.request.restoration.target ≤ (4 * allowance)^2 :=
          (show target.request.restoration.target = 1 * target.request.restoration.target by ring1).trans_le
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
                decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 436)
              target.request.restoration.positive.le).trans
              ((show 436 * target.request.restoration.target =
                416 * target.request.restoration.target + 20 * target.request.restoration.target by ring1).trans_le
                target.request.restoration.paid))
        have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
          FiniteSum.Fin.sumFin_zero.symm.trans_le
            (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
              (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
        change Data.Gaussian.Norm.Basic.normSq (samples.1.endpoints.last.2 - targetSample.endpoints.first.2) ≤
          _
        rw [show samples.1.endpoints.last.2 - targetSample.endpoints.first.2 =
          -(targetSample.endpoints.first.2 - samples.1.endpoints.last.2) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
        exact gap.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid nonnegative)
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, plans, inputs, readings, prepared, samples, closing, later, _, _, _ =>
      lastEndpointReturn
        branch target targetPlan targetInput targetReading targetFans targetSample
        _ _ bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 closing later
        samples.1.endpoints.last.2 (Acquisition.Sample.outgoingPotential samples.1) (by intro empty; cases empty)

/-- The closing request is tied to the literal final and initial parent samples, including the empty-bank base case. -/
theorem returned_endpoint_bound (branch : HyperellipticReciprocal.originOrder curve = 1) : {parents : List
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
      samples first.1 first.2).1 - first.1) ≤
      (4 * allowance)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, .nil, _, _, _, _, _, _, _, _, _ => by
      change Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) ≤ _
      rw [_root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (FiniteSum.Fin.sumFin_zero.symm.trans_le
          (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _
            (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))))
  | _, .cons patch data cover tail, sources, bank, plans, inputs, readings, prepared, samples, closing, later =>
      lastEndpointReturn branch
        bank.1 plans.1 inputs.1 readings.1 prepared.1 samples.1
        (.cons patch data cover tail) sources bank plans inputs readings prepared samples closing later
        samples.1.endpoints.first.2 (Acquisition.Sample.incomingPotential samples.1) (by intro empty; cases empty)

/-- The closing ribbon is small, rather than discarded as a zero term. Its bound uses the actual initial endpoint and
the same scheduled closing join. -/
theorem returned_ribbon_bound (branch : HyperellipticReciprocal.originOrder curve = 1)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples)
    (closing : BasisCommonParentBank.ClosingJunction anchors sources bank) (later : closing.stage anchors sources bank ≤
      stage) :
    let first := Samples.firstValues anchors sources bank plans inputs readings prepared samples
    let last := Samples.lastValues anchors sources bank plans inputs readings prepared samples first.1 first.2
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area first.1 (last.1 - first.1)) ≤
      4 * (2 + 8 * basis.coefficient) * (4 * allowance)^2 * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  dsimp only
  have first := Samples.firstValue_bound branch anchors sources bank plans inputs readings prepared samples comparisons
  have gap := returned_endpoint_bound
    branch anchors sources bank plans inputs readings prepared samples closing later
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct first gap (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans first)
  exact (BoundaryRibbon.area_bound _ _).trans
    ((show 4 * Data.Gaussian.Norm.Basic.normSq _ * Data.Gaussian.Norm.Basic.normSq _ = 4 *
      (Data.Gaussian.Norm.Basic.normSq _ * Data.Gaussian.Norm.Basic.normSq _) by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq (by ring1)))

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankEndpointReturn
