module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Riemann

public section

/-! Homogeneous comparison with the original source primitives on a common
subinterval of the retained basis cells. The squared width is preserved. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison

open Purelib.Data.Rat.Fraction.Order

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {model : UniformReciprocalRootChannels.RootModel cell} {parameter :
    InverseRootPolynomial.Coordinate} {anchor : ArcOwners.Point cap
    model parameter}
  {regular : RegularBounds.Data cap}

open Purelib.Data.Rat.Fraction.Compatibility

variable {owners : SourceRequests.BasisSourceOwners regular anchor} {target :
  InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- Select every source-to-pullback threshold before sampling the basis bank. -/
structure BasisPrimitiveRequest (owners : SourceRequests.BasisSourceOwners
  regular anchor) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The requested whole-basis primitive comparison target is positive. -/ positive : 0 < target
  /-- The retained local source-row tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The local tolerance is the original genus-based target allocation. -/ tolerance_eq : tolerance =
    Rational.Budget.Aggregate.perTerm target genus
  /-- The actual per-row source-to-pullback requests on their retained original owners. -/ entries :
    Data.Vector.DependentVector (fun row => ArcComparison.Request (owners.get
    row).comparison tolerance floor)
  /-- The cached common sufficient primitive comparison stage. -/ index : Nat
  /-- The stage is the maximum of the original floor and retained row indices. -/ index_eq : index = max floor
    (entries.maximum fun _ request => request.index)

constructive_injectivity BasisPrimitiveRequest

namespace BasisPrimitiveRequest

/-- Allocate the original basis target and retain all source-to-pullback thresholds before sampling. -/
@[expose] def build (owners : SourceRequests.BasisSourceOwners regular
  anchor) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    BasisPrimitiveRequest owners target floor :=
  let tolerance := Rational.Budget.Aggregate.perTerm target genus
  let entries := Data.Vector.DependentVector.ofFn fun row =>
    ArcComparison.Request.build (owners.get row).comparison tolerance
      (Rational.Budget.Aggregate.perTerm_positive positive genus) floor
  ⟨positive, tolerance, rfl, entries, max floor (entries.maximum fun _ request => request.index), rfl⟩

variable {index : Nat} {box : Rational.Box} {polynomials :
  Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- These are the original cached source polynomials, one for each basis parent. -/
@[expose] def Sources (owners : SourceRequests.BasisSourceOwners regular
  anchor) (index : Nat) :=
  Data.Vector.DependentVector (fun row => UniformReciprocalPrimitives.SourcePrimitive
    (owners.get row).data index)

/-- The bound compares actual original primitive increments with the acquired
pullback increments. Constant primitive origins cancel within each retained
cell; no equality of origins across different cells is asserted. -/
theorem accurate (request : BasisPrimitiveRequest owners
  target floor)
    (sources : Sources owners
      index) (samples : SourceRequests.BasisSourceRequest.Samples owners
      polynomials)
    (later : request.index ≤ index) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {first last : InverseRootPolynomial.Coordinate}
    (firstInside : ∀ row, (owners.get row).edge.left.parameter ≤ first ∧ first ≤ (owners.get row).edge.right.parameter)
    (lastInside : ∀ row, (owners.get row).edge.left.parameter ≤ last ∧ last ≤ (owners.get row).edge.right.parameter) :
    Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => coefficients row *
      ((sources.get row).primitive.value.eval ((owners.get row).parent.edge.point last) -
        (sources.get row).primitive.value.eval ((owners.get row).parent.edge.point first))) -
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        ((samples.get row).pullback.value.eval ((owners.get row).parent.edge.point last)⁻¹ -
          (samples.get row).pullback.value.eval ((owners.get row).parent.edge.point first)⁻¹))) ≤
      target * (last - first)^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
        Purelib.Data.Rat in by
  let errors := fun row => ArcComparison.Sample.comparisonValue (samples.get row)
    (sources.get row) last -
    ArcComparison.Sample.comparisonValue (samples.get row) (sources.get row) first
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build errors
  have each (row : Fin genus) : Gaussian.Norm.Basic.normSq (errors row) ≤ request.tolerance * (last - first)^2
    := by
    have after := (request.entries.get_le_maximum (fun _ entry => entry.index) row).trans
      ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq.symm.trans_le later))
    have smaller := (quarterRadius_antitone
      (owners.get row).comparison.scale_nonnegative after).trans_eq (request.entries.get row).error_eq.symm
    exact (ArcComparison.Sample.comparison_error (samples.get row) (sources.get
      row) (firstInside row) (lastInside row)).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct (smaller.trans (request.entries.get row).error_lt.le)
        (Arithmetic.sq_nonneg_direct (last - first)))
  have paid : budget.scale ≤ target * (last - first)^2 := by
    rw [budget.scale_eq]
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.Rational.sum_constant] at bound
    have allowance := Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive genus
    rw [← request.tolerance_eq] at allowance
    exact bound.trans ((show (genus : InverseRootPolynomial.Coordinate) * ((genus :
      InverseRootPolynomial.Coordinate) * (request.tolerance * (last - first)^2)) =
      ((genus : InverseRootPolynomial.Coordinate) * ((genus :
        InverseRootPolynomial.Coordinate) * request.tolerance)) * (last - first)^2 by ring1).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_right_direct allowance.le
        (Arithmetic.sq_nonneg_direct (last - first))))
  have readback : (FiniteSum.Fin.sumFin (fun row => coefficients row *
      ((sources.get row).primitive.value.eval ((owners.get row).parent.edge.point last) -
        (sources.get row).primitive.value.eval ((owners.get row).parent.edge.point first))) -
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        ((samples.get row).pullback.value.eval ((owners.get row).parent.edge.point last)⁻¹ -
          (samples.get row).pullback.value.eval ((owners.get row).parent.edge.point first)⁻¹))) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * errors row) := by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [errors, ArcComparison.Sample.comparisonValue]
    ring1
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg
      (coefficients row)))
  rw [readback]
  exact (budget.bound coefficients).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct paid nonnegative).trans_eq (by ring1))

end BasisPrimitiveRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
