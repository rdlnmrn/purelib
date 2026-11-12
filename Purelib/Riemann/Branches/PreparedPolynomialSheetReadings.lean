module
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic

public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
public import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
import Purelib.Riemann.Normalization.InverseModelBackwardSigns
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# Read an aligned operational patch at its retained polynomial index

The operational alignment relation uses two extra Newton steps only in its
proof. Backwards sign preservation removes that floor from the polynomial
actually consumed by a primitive request, including indices zero and one.
-/

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetReadings

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Normalization in
/-- Root alignment gives nearestness against any original independent polynomial refinement index.

The original model and continued patch both contain the same point, and the supplied operational root-name equivalence
connects their retained owners. Backward two-step comparison removes the extra refinements without changing the selected
sign. -/
theorem nearest_at_index {polynomial : Polynomial} {box : Box}
    {model : OverlapReady polynomial box} {point : Gaussian} {root : Name.Basic.Named}
    (aligned : RootAligned model point root) (pointInside : box.Contains point)
    {count : Nat} (patch : ContinuedNeighborhood polynomial count) (inside : patch.box.Contains point)
    (sample : ContinuedNeighborhood.Point patch point) (roots : Equivalence.NamedEquivalent root
      sample.certificate.value.name)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point - (patch.base.refine index).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point + (patch.base.refine index).value.eval point) := by
  have nearest : Basic.Canonical.normSq (model.model.value.eval point - (patch.base.refine index).step.step.value.eval
    point) ≤
      Basic.Canonical.normSq (model.model.value.eval point + (patch.base.refine index).step.step.value.eval point) := by
    have scalar := aligned patch inside sample roots index
    simpa only [Norm.Basic.normSq_eq_canonical, OwnerSeededInverseRoot.SeededNeighborhood.refine,
      InverseRootPolynomial.Model.refine] using scalar
  have scalar := model.nearest_before_two_steps (patch.base.refine index) pointInside
    (patch.box_refines.contains inside) nearest
  simpa only [Norm.Basic.normSq_eq_canonical] using scalar

end Purelib.Riemann.Branches.PreparedPolynomialSheetReadings

end

public section

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetReadings

open Purelib
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box Model)
open Purelib.Riemann.Normalization.InverseModelRootSamples (RootSamples)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRootRequests (InverseRequest)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat

/-- The actual aligned model root reading is close to the parameter times an independently paid inverse-owner reading.

The same retained sample bank supplies its uniform root bound. The actual
inverse request pays the continued polynomial and owner floors independently;
nearest-sign alignment bounds the discrepancy between the two original
polynomial refinements. The conclusion preserves both finite indices and the
actual request's target, with no endpoint root-name equality assumed.
-/
theorem requested_root_distance_le {polynomial : Polynomial} {box : Box} {model : Model polynomial box}
    {point : Gaussian} (data : RootSamples model point) (pointInside : box.Contains point)
    (modelIndex : Nat) {count : Nat} (patch : ContinuedNeighborhood polynomial count)
    (inside : patch.box.Contains point) (sample : ContinuedNeighborhood.Point patch point)
    {root : Name.Basic.Named}
    (aligned : RootAligned
      (InverseRootPolynomial.Model.overlapRefine model modelIndex) point root)
    (roots : NamedEquivalent root sample.certificate.value.name)
    {owner : Certificate (polynomial.eval point)}
    {target : Coordinate} {floor : Nat} (request : InverseRequest sample owner target floor)
    {patchIndex rootIndex : Nat} (patchLater : request.index ≤ patchIndex)
    (rootLater : request.observation.comparison.leftIndex ≤ rootIndex) :
    normSq (data.sample (modelIndex + 2) - polynomial.eval point *
      inv ((Name.Sampling.approximation owner.value.name).sample rootIndex)) ≤
      12 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound) * data.bound +
        2 * normSq (polynomial.eval point) * target := by
  let left := (model.refine (modelIndex + 2)).value.eval point
  let right := (patch.base.refine patchIndex).value.eval point
  let parameter := polynomial.eval point
  have nearest : normSq (left - right) ≤ normSq (left + right) := by
    have modelEq : (InverseRootPolynomial.Model.overlapRefine model modelIndex).model =
        model.refine (modelIndex + 2) := by rfl
    have actual := nearest_at_index aligned pointInside patch inside sample roots patchIndex
    rewrite [modelEq] at actual
    simpa only [Norm.Basic.normSq_eq_canonical] using actual
  let alignment : SignAlignment left right := ⟨false, right, rfl, nearest⟩
  have firstResidual : normSq (1 - parameter * left ^ 2) ≤ (model.refine (modelIndex + 2)).bound := by
    rw [← (model.refine (modelIndex + 2)).residual_eq]
    exact (model.refine (modelIndex + 2)).residualBound point pointInside
  have lastResidual : normSq (1 - parameter * right ^ 2) ≤ (patch.base.refine patchIndex).bound := by
    rw [← (patch.base.refine patchIndex).residual_eq]
    exact (patch.base.refine patchIndex).residualBound point (patch.box_refines.contains inside)
  have distance : normSq (left - right) ≤
      6 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound) * normSq left :=
    alignment.distance_le firstResidual lastResidual (model.refine (modelIndex + 2)).bound_small
  have combinedNonnegative : 0 ≤
      6 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (by
        have total := Arithmetic.add_le_add_direct
          (model.refine (modelIndex + 2)).bound_nonnegative (patch.base.refine patchIndex).bound_nonnegative
        change (0 : Coordinate) ≤ _ at total
        exact total)
  have scaled : normSq (parameter * left - parameter * right) ≤
      6 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound) * data.bound := by
    rw [← mul_sub, normSq_mul]
    calc
      _ ≤ normSq parameter *
          (6 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound) * normSq left) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct distance (normSq_nonneg _)
      _ = (6 * ((model.refine (modelIndex + 2)).bound + (patch.base.refine patchIndex).bound)) *
          normSq (data.sample (modelIndex + 2)) := by
        rw [data.sample_eq, normSq_mul]
        ring1
      _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (data.sample_bounded pointInside (modelIndex + 2)) combinedNonnegative
  have paid : normSq (parameter * right - parameter *
      inv ((Name.Sampling.approximation owner.value.name).sample rootIndex)) ≤
      normSq parameter * target := by
    rw [← mul_sub, normSq_mul]
    apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (normSq_nonneg _)
    exact (request.accurate patchLater rootLater).le
  rw [data.sample_eq]
  have triangle := Norm.Bounds.normSq_sub_le_via
    (parameter * left) (parameter * right)
    (parameter * inv ((Name.Sampling.approximation owner.value.name).sample rootIndex))
  rewrite [Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at triangle
  apply triangle.trans
  apply (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct scaled paid) (by decide +kernel : (0 : Coordinate) ≤ 2)).trans_eq
  ring1

/-- Compare the same model's numerical root samples with an actual aligned continued owner.

The original inverse request is paid once per comparison. Geometric searches
choose independent polynomial floors, and its saved residual observation
chooses the actual owner floor. Both arbitrary later sample indices remain
inputs. Exact guarded division and the retained owner's square identity
then identify the parameter-over-root channel with that same original root.
-/
def rootEquivalent {polynomial : Polynomial} {box : Box} {model : Model polynomial box}
    {point : Gaussian} (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (pointInside : box.Contains point) {count : Nat} (patch : ContinuedNeighborhood polynomial count)
    (inside : patch.box.Contains point) (sample : ContinuedNeighborhood.Point patch point)
    (owner : Certificate (polynomial.eval point))
    (roots : NamedEquivalent owner.value.name sample.certificate.value.name)
    (aligned : ∀ index, RootAligned
      (InverseRootPolynomial.Model.overlapRefine model index) point owner.value.name) :
    Equivalence.Equivalent (data.approximation small pointInside) (Name.Sampling.approximation owner.value.name) := by
  let numerator := Name.Coherent.CoherentNamed.Coherence.exact data.parameter
  have parameterNormEq : data.parameterNorm = normSq (polynomial.eval point) :=
    data.parameterNorm_eq.trans (congrArg normSq data.parameter_eq)
  have parameterNormNonnegative : 0 ≤ data.parameterNorm := by
    rw [data.parameterNorm_eq]
    exact normSq_nonneg _
  let sampled := Name.Coherent.Division.Sample.sampledQuotientApproximation numerator owner.value owner.apart
  have numerical : Equivalence.Equivalent (data.approximation small pointInside) sampled := {
    compare := fun leftStart rightStart target positive => by
      let weight := 24 * data.bound + 2 * data.parameterNorm
      have weightNonnegative : 0 ≤ weight := by
        have total := Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 24) data.bound_nonnegative)
          (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 2) parameterNormNonnegative)
        change (0 : Coordinate) ≤ weight at total
        exact total
      let allowance := Budget.Weighted.allowance target weight
      have allowancePositive : 0 < allowance :=
        Budget.Weighted.allowance_positive positive weightNonnegative
      let request := InverseRequest.build sample inside owner roots allowance allowancePositive rightStart
      let firstIndex := Geometric.Search.firstQuarterBelow model.bound leftStart allowance
      let lastIndex := max request.index
        (Geometric.Search.firstQuarterBelow patch.base.model.bound 0 allowance)
      have firstFloor : leftStart ≤ firstIndex :=
        Geometric.Search.firstQuarterBelow_ge _ _ _
      have lastFloor : request.index ≤ lastIndex := Data.Nat.Order.le_max_left _ _
      have lastSearch :
          Geometric.Search.firstQuarterBelow patch.base.model.bound 0 allowance ≤ lastIndex :=
        Data.Nat.Order.le_max_right _ _
      refine ⟨firstIndex + 2, request.observation.comparison.leftIndex,
        firstFloor.trans (Nat.le_add_right _ _), request.observation.comparison.left_ge, ?_⟩
      intro leftLater rightLater leftOrder rightOrder
      have atLeastTwo : 2 ≤ leftLater := (Nat.le_add_left 2 firstIndex).trans leftOrder
      have leftEq : leftLater - 2 + 2 = leftLater := Nat.sub_add_cancel atLeastTwo
      have leftRadius : (model.refine leftLater).bound ≤ allowance := by
        rw [Model.refine_bound]
        apply (Geometric.Basic.quarterRadius_antitone model.bound_nonnegative
          ((Nat.le_add_right firstIndex 2).trans leftOrder)).trans
        exact (Geometric.Search.firstQuarterBelow_accurate model.bound
          model.bound_nonnegative leftStart allowance allowancePositive).le
      have rightRadius : (patch.base.refine lastIndex).bound ≤ allowance := by
        change (patch.base.model.refine lastIndex).bound ≤ allowance
        rw [Model.refine_bound]
        apply (Geometric.Basic.quarterRadius_antitone patch.base.model.bound_nonnegative
          lastSearch).trans
        exact (Geometric.Search.firstQuarterBelow_accurate patch.base.model.bound
          patch.base.model.bound_nonnegative 0 allowance allowancePositive).le
      have finite := requested_root_distance_le data pointInside (leftLater - 2) patch inside sample
        (aligned (leftLater - 2)) roots request lastFloor rightOrder
      rw [leftEq] at finite
      change Norm.Basic.normSq (data.sample leftLater - sampled.sample rightLater) < target
      rewrite [Norm.Basic.normSq_eq_canonical]
      have quotientSample : sampled.sample rightLater = polynomial.eval point *
          inv ((Name.Sampling.approximation owner.value.name).sample rightLater) := by
        rw [Name.Coherent.Division.Sample.sampledQuotientApproximation_sample]
        change data.parameter / (Name.Sampling.approximation owner.value.name).sample rightLater = _
        rw [data.parameter_eq]
        rfl
      rw [quotientSample]
      apply finite.trans_lt
      have allowanceBound :
          12 * ((model.refine leftLater).bound + (patch.base.refine lastIndex).bound) * data.bound +
            2 * normSq (polynomial.eval point) * allowance ≤ weight * allowance := by
        calc
          _ ≤ 12 * (allowance + allowance) * data.bound +
              2 * normSq (polynomial.eval point) * allowance :=
            Arithmetic.add_le_add_direct
              (Arithmetic.mul_le_mul_of_nonneg_right_direct
                (Arithmetic.mul_le_mul_of_nonneg_left_direct
                  (Arithmetic.add_le_add_direct leftRadius rightRadius) (by decide +kernel)) data.bound_nonnegative)
              (Fraction.Order.Basic.le_refl _)
          _ = _ := by dsimp only [weight]; rw [parameterNormEq]; ring1
      exact allowanceBound.trans_lt
        (Budget.Weighted.mul_allowance_lt positive weightNonnegative) }
  have quotientToSampled := Name.Coherent.Division.Equivalence.coherentDiv_toSampled
    numerator owner.value owner.apart
  have squareToNumerator : NamedEquivalent (owner.value.mul owner.value).name numerator.name :=
    Equivalence.NamedEquivalent.transport rfl
      (congrArg (fun value : Gaussian => (Name.Coherent.CoherentNamed.Coherence.exact value).name)
        data.parameter_eq.symm) owner.square
  have rootToQuotient := Division.Cancellation.coherentDiv_of_mul owner.value owner.value numerator
    owner.apart squareToNumerator
  exact numerical.trans ((Equivalence.Equivalent.toNamed_sampling sampled).symm.trans
    (quotientToSampled.symm.trans rootToQuotient.symm))

end Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
