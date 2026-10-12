module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

public section

/-! Homogeneous area comparison on the synchronized actual prepared child
increments. The two dyadic count squares cancel exactly. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
  (Acquisition)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition
  (ChildPairs)
open Purelib.Riemann.Readings.AffineBasisEnergy (WeightedNormBudget)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Cover data} {target :
  Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  BasisCommonCover cover covers minimum}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledLocalPlan)

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open _root_.Purelib.Data (Vector)
open _root_.Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace BasisPreparedCommonRequest.Acquisition

variable {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : RegularBasisPolynomials cap
    index box} {originals :
    PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

namespace ChildPairs

variable {acquired :
  Acquisition
  request polynomials originals cells coefficients depth}

/-- The squared norm sum of the retained basis coefficient vector is nonnegative. -/
private theorem norm_nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
  (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
    Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- A scaled quarter-radius is the scale times the unit quarter-radius. -/
private theorem quarter_scale (scale : InverseRootPolynomial.Coordinate) (spatial : Nat) : Geometric.Basic.quarterRadius
  scale spatial = scale * Geometric.Basic.quarterRadius 1 spatial := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- The coefficient-weighted source and integral increments for one actual dyadic child. -/
@[expose] def combination (pairs : Acquisition.ChildPairs acquired) (column : Fin (2 ^ (common.depth +
  acquired.extraDepth))) : InverseRootPolynomial.Gaussian × Gaussian :=
  (FiniteSum.Fin.sumFin (fun row => coefficients row * (pairs.read row column).1),
    FiniteSum.Fin.sumFin (fun row => coefficients row * (pairs.read row column).2))

/-- The combined child discrepancy is bounded by the source target, coefficient norm and actual dyadic scale. -/
theorem combination_error (pairs : Acquisition.ChildPairs acquired) (column : Fin (2 ^ (common.depth +
  acquired.extraDepth))) :
    Data.Gaussian.Norm.Basic.normSq
      ((combination
      pairs column).1 -
      (combination
      pairs column).2) ≤
      sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients * Geometric.Basic.quarterRadius 1
        (common.depth + acquired.extraDepth) := by
  let errors := fun row => (pairs.read row column).1 - (pairs.read row column).2
  let budget := WeightedNormBudget.build errors
  have qNonnegative := Geometric.Basic.quarterRadius_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    (common.depth + acquired.extraDepth)
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (errors row) ≤ request.sourceTolerance *
    Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth) :=
    (pairs.errors row _ (pairs.read_mem row column)).trans_eq
      (quarter_scale
      _ _)
  have paid : budget.scale ≤ sourceTarget * Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth) := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [Purelib.Algebra.FiniteSum.Fin.Rational.sum_constant] at bound
    have allowance := Aggregate.count_mul_perTerm_lt request.source_positive genus
    rw [← request.sourceTolerance_eq] at allowance
    exact bound.trans ((show (genus : InverseRootPolynomial.Coordinate) * ((genus : InverseRootPolynomial.Coordinate) *
      (request.sourceTolerance * Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth))) =
      ((genus : InverseRootPolynomial.Coordinate) * ((genus : InverseRootPolynomial.Coordinate) *
        request.sourceTolerance)) * Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth) by
        ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct allowance.le qNonnegative))
  have equal :
    (combination
    pairs column).1 -
    (combination
    pairs column).2 = FiniteSum.Fin.sumFin (fun row => coefficients row * errors row) := by
    change FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _ = _
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [errors]; ring1)
  rw [equal]
  exact (budget.bound coefficients).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    norm_nonnegative).trans_eq
    (by ring1))

/-- The combined source child satisfies the original common primitive-slope bound. -/
theorem combination_source_bound (pairs : Acquisition.ChildPairs acquired) (column : Fin (2 ^ (common.depth +
  acquired.extraDepth))) :
    Data.Gaussian.Norm.Basic.normSq
      (combination
      pairs column).1 ≤
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        covers * PreparedObservationCoercivity.coefficientNormSq coefficients * Geometric.Basic.quarterRadius 1
        (common.depth + acquired.extraDepth) := by
  let values := fun row => (pairs.read row column).1
  let budget := WeightedNormBudget.build values
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (values row) ≤ (covers.get
    row).data.sourceSlope * Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth) :=
    (pairs.source_bound row _ (pairs.read_mem row column)).trans_eq
      (quarter_scale
      _ _)
  have paid : budget.scale ≤ BasisSourceCovers.primitiveSlope covers * Geometric.Basic.quarterRadius 1 (common.depth +
    acquired.extraDepth) := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.sumFin_mul_right] at bound
    exact bound.trans_eq (by unfold BasisSourceCovers.primitiveSlope; ring1)
  exact (budget.bound coefficients).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    norm_nonnegative).trans_eq
    (by ring1))

/-- Both combined child increments satisfy the same enlarged homogeneous bound. -/
theorem combination_bounds (pairs : Acquisition.ChildPairs acquired) (column : Fin (2 ^ (common.depth +
  acquired.extraDepth))) :
    Data.Gaussian.Norm.Basic.normSq
      (combination
      pairs column).1 ≤ 2 * (BasisSourceCovers.primitiveSlope covers + sourceTarget) *
      PreparedObservationCoercivity.coefficientNormSq coefficients * Geometric.Basic.quarterRadius 1 (common.depth +
        acquired.extraDepth) ∧
    Data.Gaussian.Norm.Basic.normSq
      (combination
      pairs column).2 ≤ 2 * (BasisSourceCovers.primitiveSlope covers + sourceTarget) *
      PreparedObservationCoercivity.coefficientNormSq coefficients * Geometric.Basic.quarterRadius 1 (common.depth +
        acquired.extraDepth) := by
  have slope := BasisSourceCovers.primitiveSlope_nonnegative covers
  have qNonnegative := Geometric.Basic.quarterRadius_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    (common.depth + acquired.extraDepth)
  have source :=
    combination_source_bound
    pairs column
  have error :=
    combination_error
    pairs column
  have enlarged : BasisSourceCovers.primitiveSlope covers ≤ 2 * (BasisSourceCovers.primitiveSlope covers + sourceTarget)
    :=
    (show BasisSourceCovers.primitiveSlope covers = BasisSourceCovers.primitiveSlope covers + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl (add_nonneg slope
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        request.source_positive.le))).trans_eq (by ring1))
  have right := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (combination
    pairs column).1
    ((combination
    pairs column).1 -
    (combination
    pairs column).2)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
      error) (by decide))
  rw [show
    (combination
    pairs column).1 -
    ((combination
    pairs column).1 -
    (combination
    pairs column).2) =
    (combination
    pairs column).2 by ring1] at right
  exact ⟨source.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged
    norm_nonnegative)
    qNonnegative),
    right.trans_eq (by ring1)⟩

set_option genInjectivity false in
/-- Retain the complete combined pair list and both one-pass summaries. -/
structure Weighted (pairs : Acquisition.ChildPairs acquired) where
  /-- The retained complete list of coefficient-weighted source and integral increment pairs. -/ values : List
    (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)
  /-- The retained pair list is exactly the finite enumeration of combined dyadic children. -/ values_eq : values =
    List.ofFn
    (combination
    pairs)
  /-- The cached one-pass area summary of the source increments. -/ source : IncrementArea.Summary (values.map Prod.fst)
  /-- The cached one-pass area summary of the integral increments. -/ integral : IncrementArea.Summary (values.map
    Prod.snd)
  /-- The cached signed difference between the two actual increment areas. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The cached difference is exactly the source area minus the integral area. -/ difference_eq : difference =
    source.area - integral.area

constructive_injectivity Weighted

/-- Cache the complete weighted child-pair list and its two one-pass area summaries. -/
@[expose] def weighted (pairs : Acquisition.ChildPairs acquired) :
  Weighted
  pairs :=
  let values := List.ofFn
    (combination
    pairs)
  let source := IncrementArea.Summary.build (values.map Prod.fst)
  let integral := IncrementArea.Summary.build (values.map Prod.snd)
  ⟨values, rfl, source, integral, source.area - integral.area, rfl⟩

open
  Acquisition.ChildPairs
  in
/-- The actual weighted area discrepancy satisfies a depth-independent homogeneous bound.

The retained child count and quarter-radius cancel exactly, leaving the source target, primitive slope and squared
coefficient norm. -/
theorem Weighted.area_error {pairs : Acquisition.ChildPairs acquired} (weighted :
  Weighted
  pairs) :
    Data.Gaussian.Norm.Basic.normSq weighted.difference ≤ 32 * sourceTarget * (BasisSourceCovers.primitiveSlope
      covers + sourceTarget) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have qNonnegative := Geometric.Basic.quarterRadius_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    (common.depth + acquired.extraDepth)
  have sourceNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct request.source_positive.le
    (norm_nonnegative
    (coefficients := coefficients))
  have commonNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) (add_nonneg
      (BasisSourceCovers.primitiveSlope_nonnegative covers) request.source_positive.le))
      (norm_nonnegative
      (coefficients := coefficients))
  have every (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈ weighted.values)
    : ∃ column, pair =
    combination
    pairs column := by
    rw [weighted.values_eq] at member
    obtain ⟨column, equal⟩ := Purelib.Data.List.OfFn.Basic.mem_ofFn.mp member
    exact ⟨column, equal.symm⟩
  have bound := IncrementAreaComparison.pathArea_difference_bound weighted.values
    (Fraction.Order.Arithmetic.mul_nonneg_direct sourceNonnegative qNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct commonNonnegative qNonnegative)
    (by
        intro pair member;
        obtain ⟨column, equal⟩ := every pair member;
        rw [equal];
        exact combination_error pairs column)
    (by
        intro pair member;
        obtain ⟨column, equal⟩ := every pair member;
        rw [equal];
        exact (combination_bounds pairs column).1)
    (by
        intro pair member;
        obtain ⟨column, equal⟩ := every pair member;
        rw [equal];
        exact (combination_bounds pairs column).2)
  have countEq : weighted.values.length = 2 ^ (common.depth + acquired.extraDepth) := by rw [weighted.values_eq,
    Purelib.Data.List.OfFn.Basic.length_ofFn]
  rw [countEq, ← weighted.source.area_eq, ← weighted.integral.area_eq, ← weighted.difference_eq] at bound
  apply bound.trans_eq
  calc
    _ = 32 * sourceTarget * (BasisSourceCovers.primitiveSlope covers + sourceTarget) *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 *
      ((((2 ^ (common.depth + acquired.extraDepth) : Nat) : InverseRootPolynomial.Coordinate) *
        (((2 ^ (common.depth + acquired.extraDepth) : Nat) : InverseRootPolynomial.Coordinate) *
          Geometric.Basic.quarterRadius 1 (common.depth + acquired.extraDepth)))^2) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel]; ring1

end ChildPairs
end BasisPreparedCommonRequest.Acquisition
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
