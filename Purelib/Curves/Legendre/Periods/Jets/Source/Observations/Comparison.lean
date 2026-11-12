module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Same-patch comparison of actual six-channel source queries

The two original source requests and polynomial caches remain independent.
Every bounded query is related through the identical continued-point factory
on the same original neighborhood and physical affine coordinate. The actual
old reading states pay their own errors; selected comparison witnesses are
not substituted for either original displayed reading.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {firstCache lastCache : Cache patch} {firstFloor lastFloor : Nat} {firstTarget lastTarget : Rational}
    {firstRequest : Request firstCache firstFloor firstTarget} {lastRequest : Request lastCache lastFloor lastTarget}
    {start finish : LiftedPoint 2} {lifted : LiftedCell start finish} {firstAllowance lastAllowance : Rational}
    (firstModels : CellModels firstRequest start.coordinate finish.coordinate firstAllowance)
    (lastModels : CellModels lastRequest start.coordinate finish.coordinate lastAllowance)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate)
    (firstQuery : Query (Cell.ofModels firstRequest lifted firstModels startInside finishInside))
    (lastQuery : Query (Cell.ofModels lastRequest lifted lastModels startInside finishInside))
    (frame : Paths.Frame parameter)

/-- The identical acquisition factory at equal affine inputs retains the same original root name across source stages.

The source requests, models and actual query states may differ. The two
coordinate readbacks identify inputs to one original Point.acquire operation;
this does not identify arbitrary owners carrying the same coordinate label.
-/
private theorem acquired_name_eq (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
      (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name =
    (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
      (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name :=
  ContinuedNeighborhood.Point.acquire_name_eq _ _
    ((firstModels.coordinate.point_eq input).trans (lastModels.coordinate.point_eq input).symm)

include firstQuery lastQuery frame

/-- The actual valueZero integrals on two retained same-patch source models obey both original paid allowances. -/
theorem valueZero_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.valueZero.model.integralSample - lastModels.valueZero.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 0) lifted firstModels.valueZero.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).valueZero⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 0) lifted lastModels.valueZero.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).valueZero⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).valueZero.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).valueZero.algebraic.sheetValue.value.name
    rewrite [observe_valueZero_root_name, observe_valueZero_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.valueZero.model.localAllowance + lastModels.valueZero.model.localAllowance := by
    rewrite [firstModels.valueZero.allowance_eq, lastModels.valueZero.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.valueZero.start_eq.trans lastModels.valueZero.start_eq.symm)
    (firstModels.valueZero.finish_eq.trans lastModels.valueZero.finish_eq.symm) roots positive
  have displacement : firstModels.valueZero.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.valueZero.model.finish - firstModels.valueZero.model.start = _
    rewrite [firstModels.valueZero.start_eq, firstModels.valueZero.finish_eq]
    rfl
  rewrite [firstModels.valueZero.allowance_eq, lastModels.valueZero.allowance_eq, displacement] at bound
  exact bound

/-- The actual valueOne integrals on two retained same-patch source models obey both original paid allowances. -/
theorem valueOne_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.valueOne.model.integralSample - lastModels.valueOne.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 1) lifted firstModels.valueOne.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).valueOne⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 1) lifted lastModels.valueOne.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).valueOne⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).valueOne.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).valueOne.algebraic.sheetValue.value.name
    rewrite [observe_valueOne_root_name, observe_valueOne_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.valueOne.model.localAllowance + lastModels.valueOne.model.localAllowance := by
    rewrite [firstModels.valueOne.allowance_eq, lastModels.valueOne.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.valueOne.start_eq.trans lastModels.valueOne.start_eq.symm)
    (firstModels.valueOne.finish_eq.trans lastModels.valueOne.finish_eq.symm) roots positive
  have displacement : firstModels.valueOne.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.valueOne.model.finish - firstModels.valueOne.model.start = _
    rewrite [firstModels.valueOne.start_eq, firstModels.valueOne.finish_eq]
    rfl
  rewrite [firstModels.valueOne.allowance_eq, lastModels.valueOne.allowance_eq, displacement] at bound
  exact bound

/-- The actual firstZero integrals on two retained same-patch source models obey both original paid allowances. -/
theorem firstZero_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.firstZero.model.integralSample - lastModels.firstZero.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter 0) lifted firstModels.firstZero.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).firstZero⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter 0) lifted lastModels.firstZero.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).firstZero⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).firstZero.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).firstZero.algebraic.sheetValue.value.name
    rewrite [observe_firstZero_root_name, observe_firstZero_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.firstZero.model.localAllowance + lastModels.firstZero.model.localAllowance := by
    rewrite [firstModels.firstZero.allowance_eq, lastModels.firstZero.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.firstZero.start_eq.trans lastModels.firstZero.start_eq.symm)
    (firstModels.firstZero.finish_eq.trans lastModels.firstZero.finish_eq.symm) roots positive
  have displacement : firstModels.firstZero.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.firstZero.model.finish - firstModels.firstZero.model.start = _
    rewrite [firstModels.firstZero.start_eq, firstModels.firstZero.finish_eq]
    rfl
  rewrite [firstModels.firstZero.allowance_eq, lastModels.firstZero.allowance_eq, displacement] at bound
  exact bound

/-- The actual firstOne integrals on two retained same-patch source models obey both original paid allowances. -/
theorem firstOne_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.firstOne.model.integralSample - lastModels.firstOne.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter 1) lifted firstModels.firstOne.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).firstOne⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter 1) lifted lastModels.firstOne.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).firstOne⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).firstOne.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).firstOne.algebraic.sheetValue.value.name
    rewrite [observe_firstOne_root_name, observe_firstOne_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.firstOne.model.localAllowance + lastModels.firstOne.model.localAllowance := by
    rewrite [firstModels.firstOne.allowance_eq, lastModels.firstOne.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.firstOne.start_eq.trans lastModels.firstOne.start_eq.symm)
    (firstModels.firstOne.finish_eq.trans lastModels.firstOne.finish_eq.symm) roots positive
  have displacement : firstModels.firstOne.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.firstOne.model.finish - firstModels.firstOne.model.start = _
    rewrite [firstModels.firstOne.start_eq, firstModels.firstOne.finish_eq]
    rfl
  rewrite [firstModels.firstOne.allowance_eq, lastModels.firstOne.allowance_eq, displacement] at bound
  exact bound

/-- The actual secondZero integrals on two retained same-patch source models obey both original paid allowances. -/
theorem secondZero_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.secondZero.model.integralSample - lastModels.secondZero.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter 0) lifted firstModels.secondZero.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).secondZero⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter 0) lifted lastModels.secondZero.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).secondZero⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).secondZero.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).secondZero.algebraic.sheetValue.value.name
    rewrite [observe_secondZero_root_name, observe_secondZero_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.secondZero.model.localAllowance + lastModels.secondZero.model.localAllowance := by
    rewrite [firstModels.secondZero.allowance_eq, lastModels.secondZero.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.secondZero.start_eq.trans lastModels.secondZero.start_eq.symm)
    (firstModels.secondZero.finish_eq.trans lastModels.secondZero.finish_eq.symm) roots positive
  have displacement : firstModels.secondZero.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.secondZero.model.finish - firstModels.secondZero.model.start = _
    rewrite [firstModels.secondZero.start_eq, firstModels.secondZero.finish_eq]
    rfl
  rewrite [firstModels.secondZero.allowance_eq, lastModels.secondZero.allowance_eq, displacement] at bound
  exact bound

/-- The actual secondOne integrals on two retained same-patch source models obey both original paid allowances. -/
theorem secondOne_integral_difference_le (firstPositive : 0 < firstAllowance)
    (lastPositive : 0 < lastAllowance) :
    Norm.Basic.normSq (firstModels.secondOne.model.integralSample - lastModels.secondOne.model.integralSample) ≤
      16 * (firstAllowance + lastAllowance) * Norm.Basic.normSq (finish.coordinate - start.coordinate) := by
  let firstCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter 1) lifted firstModels.secondOne.model :=
    ⟨fun input lower upper => (firstQuery.observe frame input lower upper).secondOne⟩
  let lastCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter 1) lifted lastModels.secondOne.model :=
    ⟨fun input lower upper => (lastQuery.observe frame input lower upper).secondOne⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (firstCertificate.query input lower upper).algebraic.sheetValue.value.name
        (lastCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    change NamedEquivalent (firstQuery.observe frame input lower upper).secondOne.algebraic.sheetValue.value.name
      (lastQuery.observe frame input lower upper).secondOne.algebraic.sheetValue.value.name
    rewrite [observe_secondOne_root_name, observe_secondOne_root_name]
    change NamedEquivalent
      (ContinuedNeighborhood.Point.acquire patch (firstModels.coordinate.point input)
        (firstModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
      (ContinuedNeighborhood.Point.acquire patch (lastModels.coordinate.point input)
        (lastModels.coordinate.point_inside startInside finishInside lower upper)).certificate.value.name
    rewrite [acquired_name_eq firstModels lastModels startInside finishInside input lower upper]
    exact NamedEquivalent.refl _
  have positive : 0 < firstModels.secondOne.model.localAllowance + lastModels.secondOne.model.localAllowance := by
    rewrite [firstModels.secondOne.allowance_eq, lastModels.secondOne.allowance_eq]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le
  have bound := firstCertificate.integral_difference_le lastCertificate
    (firstModels.secondOne.start_eq.trans lastModels.secondOne.start_eq.symm)
    (firstModels.secondOne.finish_eq.trans lastModels.secondOne.finish_eq.symm) roots positive
  have displacement : firstModels.secondOne.model.displacement = finish.coordinate - start.coordinate := by
    change firstModels.secondOne.model.finish - firstModels.secondOne.model.start = _
    rewrite [firstModels.secondOne.start_eq, firstModels.secondOne.finish_eq]
    rfl
  rewrite [firstModels.secondOne.allowance_eq, lastModels.secondOne.allowance_eq, displacement] at bound
  exact bound

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.Query

end
