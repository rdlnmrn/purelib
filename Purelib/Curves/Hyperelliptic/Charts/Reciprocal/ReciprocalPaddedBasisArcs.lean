module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Stage-independent chord and area bounds for the complete reciprocal basis. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.RootContinuation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {data : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap}

namespace BasisBounds

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds data}

variable {index : Nat} {box : Rational.Box}

/-- Every coefficient vector consumes the same retained uniform ceilings. -/
theorem chord_increment (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) {first last :
      Normalization.InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last))
    {left right : Normalization.InverseRootPolynomial.Coordinate} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤
      right ∧ right ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients (RootContinuation.RootRadialGeometry.chord first
      last right) -
      polynomials.value coefficients (RootContinuation.RootRadialGeometry.chord first last left)) ≤
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (2 * basis.coefficient *
          Data.Gaussian.Norm.Basic.normSq (last - first)) * (right - left)^2 := open Purelib.Algebra in open
          Purelib.Data.Rat in by
  let increments := fun row : Fin genus =>
    (polynomials.get row).primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last right) -
      (polynomials.get row).primitive.value.eval (RootContinuation.RootRadialGeometry.chord first last left)
  have readback : polynomials.value coefficients (RootContinuation.RootRadialGeometry.chord first last right) -
      polynomials.value coefficients (RootContinuation.RootRadialGeometry.chord first last left) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * increments row) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [increments]; ring1)
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (increments row) ≤
      basis.entries row * (2 * Data.Gaussian.Norm.Basic.normSq (last - first) * (right - left)^2) :=
    (bounds.chord_increment (polynomials.get row) branch firstInside lastInside leftUnit rightUnit).trans_eq
      (by rw [basis.entries_eq]; ring1)
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build increments
  have scale : budget.scale ≤ 2 * basis.coefficient * Data.Gaussian.Norm.Basic.normSq (last - first) * (right -
    left)^2 := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.sumFin_mul_right] at bound
    exact bound.trans_eq (by rw [basis.coefficient_eq]; ring1)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  rw [readback]
  exact (budget.bound coefficients).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scale
    nonnegative).trans_eq (by ring1))

/-- Refinement error is quadratic in the coefficient norm, uniformly in
both the polynomial stage and the later radial refinement depth. -/
theorem arc_refinement (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) {first last :
      Normalization.InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.arcArea (polynomials.value coefficients)
      depth first last -
      Path.BoundaryRibbon.area (polynomials.value coefficients first) (polynomials.value coefficients last)) ≤
        16 * basis.coefficient^2 * Data.Gaussian.Norm.Basic.normSq (last - first)^2 *
          (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Algebra in open
          Purelib.Data.Rat in by
  let slope := Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (2 * basis.coefficient *
    Data.Gaussian.Norm.Basic.normSq (last - first))
  have coefficientNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have nonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct coefficientNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      basis.coefficient_nonnegative) (Gaussian.Norm.Basic.normSq_nonneg _))
  have estimate := Path.Dyadic.DyadicAreaRefinement.dyadicArea_chord_bound
    (fun parameter => polynomials.value coefficients (RootContinuation.RootRadialGeometry.chord first last parameter))
    (lower := 0) (upper := 1) nonnegative
    (fun _ _ leftUnit rightUnit => Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs.BasisBounds.chord_increment
      basis polynomials coefficients branch firstInside lastInside leftUnit rightUnit)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : RootContinuation.RootRadialGeometry.chord first last 0 = first := by
    apply Gaussian.Basic.ext <;> simp only [RootContinuation.RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have atOne : RootContinuation.RootRadialGeometry.chord first last 1 = last := by
    apply Gaussian.Basic.ext <;> simp only [RootContinuation.RootRadialGeometry.chord, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    dsimp only [slope];
    rw [
      show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0)^4 = 1 by decide];
    ring1)

end BasisBounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
