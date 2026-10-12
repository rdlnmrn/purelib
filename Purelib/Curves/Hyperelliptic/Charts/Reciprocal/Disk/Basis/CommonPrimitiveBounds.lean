module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

public section

/-! Uniform homogeneous slopes for the original and pullback basis paths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (PrimitiveSample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (comparisonLocations PrimitiveRequest)
open Purelib.Riemann.Readings.AffineBasisEnergy (WeightedNormBudget)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

namespace BasisSourceCovers

/-- This slope is selected from the original cover data before any sampling. -/
@[expose] def primitiveSlope (covers : SourceLocations.BasisSourceCovers parent) : Coordinate :=
  (genus : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row => (covers.get row).data.sourceSlope)

/-- The complete original cover's homogeneous primitive slope is nonnegative. -/
theorem primitiveSlope_nonnegative (covers : SourceLocations.BasisSourceCovers parent) : 0 ≤
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    (FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _
      (fun row => (covers.get row).data.sourceSlope_nonnegative)))

end BasisSourceCovers

namespace BasisCommonInterval.PrimitiveSample

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {interval :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

/-- Every original source primitive increment has the retained cover slope bound times squared parameter width and
coefficient norm. -/
theorem source_increment_bound (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last : InverseRootPolynomial.Coordinate}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.sourceValue coefficients last - sample.sourceValue coefficients
      first) ≤
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        covers * (last - first)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let values := fun row => (sample.originals.get row).primitive.value.eval
      (((BasisCommonInterval.comparisonLocations interval regular).owners.get row).parent.edge.point last) -
    (sample.originals.get row).primitive.value.eval
      (((BasisCommonInterval.comparisonLocations interval regular).owners.get row).parent.edge.point first)
  let budget := WeightedNormBudget.build values
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (values row) ≤ (covers.get
    row).data.sourceSlope * (last - first)^2 := by
    have bound := (sample.originals.get row).increment_bound firstInside lastInside
    have scale : ((BasisCommonInterval.comparisonLocations interval regular).owners.get row).data.sourceSlope =
        (covers.get row).data.sourceSlope := by
      rw [BasisSourceLocations.owners_get]
      rfl
    rw [scale] at bound
    exact bound
  have paid : budget.scale ≤
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers *
    (last - first)^2 := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.sumFin_mul_right] at bound
    exact bound.trans_eq (by
        unfold Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope;
        ring1)
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have equal : sample.sourceValue coefficients last - sample.sourceValue coefficients first =
      FiniteSum.Fin.sumFin (fun row => coefficients row * values row) := by
    unfold BasisCommonInterval.PrimitiveSample.sourceValue
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [values]; ring1)
  rw [equal]
  exact (budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid nonnegative).trans_eq (by ring1))

/-- The actual reciprocal pullback increment satisfies the homogeneous original-source slope bound enlarged by the paid
comparison target. -/
theorem pullback_increment_bound (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    {target : InverseRootPolynomial.Coordinate} {floor : Nat} (request : BasisCommonInterval.PrimitiveRequest interval
      regular target floor)
    (later : request.index ≤ index) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last :
      InverseRootPolynomial.Coordinate}
    (firstInside : interval.edge.left.parameter ≤ first ∧ first ≤ interval.edge.right.parameter)
    (lastInside : interval.edge.left.parameter ≤ last ∧ last ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (sample.pullbackValue coefficients last - sample.pullbackValue coefficients
      first) ≤
      2 * (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        covers + target) * (last - first)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have source :=
    source_increment_bound
    sample coefficients
    ⟨interval.edge.left.inside.1.trans firstInside.1, firstInside.2.trans interval.edge.right.inside.2⟩
    ⟨interval.edge.left.inside.1.trans lastInside.1, lastInside.2.trans interval.edge.right.inside.2⟩
  have error := sample.accurate request later coefficients firstInside lastInside
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (sample.sourceValue coefficients last - sample.sourceValue coefficients first)
    ((sample.sourceValue coefficients last - sample.sourceValue coefficients first) -
      (sample.pullbackValue coefficients last - sample.pullbackValue coefficients first))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
        error) (by decide))
  rw [show (sample.sourceValue coefficients last - sample.sourceValue coefficients first) -
    ((sample.sourceValue coefficients last - sample.sourceValue coefficients first) -
      (sample.pullbackValue coefficients last - sample.pullbackValue coefficients first)) =
      sample.pullbackValue coefficients last - sample.pullbackValue coefficients first by ring1] at bound
  exact bound.trans_eq (by ring1)

end BasisCommonInterval.PrimitiveSample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
