module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Cached coefficient-uniform Taylor bounds on a supplied reciprocal coordinate box. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- Cached polynomial bounds for the actual reciprocal basis, independent
of any later coefficient vector or geometric refinement. -/
structure RegularBasisBounds (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (domain : Rational.Box := Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox) where
  /-- The actual polynomial bounds for every original reciprocal basis entry. -/ entries : Data.Vector.DependentVector
    (fun row => Charts.Reciprocal.Cap.EnergyBounds (polynomials.get row) domain)
  /-- The cached genus-weighted aggregate derivative ceiling. -/ coefficient : Fraction.Rational
  /-- The coefficient is the genus times the finite sum of the original entry coefficients. -/ coefficient_eq :
    coefficient = (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => (entries.get row).coefficient)
  /-- The cached genus-weighted aggregate Taylor remainder ceiling. -/ remainder : Fraction.Rational
  /-- The remainder is the genus times the finite sum of the original entry remainders. -/ remainder_eq : remainder =
    (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => (entries.get row).remainder)

constructive_injectivity RegularBasisBounds

namespace RegularBasisBounds
variable {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box} {domain : Rational.Box}

/-- Cache the original reciprocal basis bounds once and sum their derivative and Taylor ceilings with the genus factor.
-/
def build (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box)
    (domain : Rational.Box := Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials domain :=
  let entries := Data.Vector.DependentVector.ofFn (fun row =>
    Charts.Reciprocal.Cap.EnergyBounds.build (polynomials.get row) domain)
  ⟨entries, Rational.Budget.Aggregate.countCoordinate genus * FiniteSum.Fin.sumFin (fun row => (entries.get
    row).coefficient), by
      rw [Rational.Budget.Aggregate.countCoordinate_eq],
    Rational.Budget.Aggregate.countCoordinate genus * FiniteSum.Fin.sumFin (fun row => (entries.get row).remainder), by
      rw [Rational.Budget.Aggregate.countCoordinate_eq]⟩

/-- The retained aggregate derivative coefficient is nonnegative. -/
theorem coefficient_nonnegative (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials domain) : 0 ≤ bounds.coefficient := by
  rw [bounds.coefficient_eq]
  apply Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  exact FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 :
    Fraction.Rational)) _
    (fun row => (bounds.entries.get row).coefficient_nonnegative))

/-- The retained aggregate Taylor remainder coefficient is nonnegative. -/
theorem remainder_nonnegative (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials domain) : 0 ≤ bounds.remainder := by
  rw [bounds.remainder_eq]
  apply Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  exact FiniteSum.Fin.sumFin_zero.symm.trans_le (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 :
    Fraction.Rational)) _
    (fun row => (bounds.entries.get row).remainder_nonnegative))

/-- The homogeneous affine scale uses the cached derivative ceilings. -/
theorem affine_scale_bound (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials domain) {first last : Gaussian.Basic.Canonical}
    (inside : domain.Contains first) {distance : Fraction.Rational}
    (close : Data.Gaussian.Norm.Basic.normSq (last - first) ≤ distance) :
    (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrement ((polynomials.get row).coefficient.eval first) first last)) ≤
        bounds.coefficient * distance := by
  have pointwise (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrement ((polynomials.get row).coefficient.eval first) first last) ≤
        (bounds.entries.get row).coefficient * distance := by
    rw [Energy.AffineTriangle.affinePrimitiveIncrement, ← mul_sub, Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct ((bounds.entries.get row).coefficient_box_le inside) close
      (Gaussian.Norm.Basic.normSq_nonneg _) (bounds.entries.get row).coefficient_nonnegative
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ pointwise)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  rw [FiniteSum.Fin.sumFin_mul_right] at bound
  exact bound.trans_eq (by rw [bounds.coefficient_eq]; ring1)

/-- The same cached Taylor ceilings control the complete basis error scale. -/
theorem error_scale_bound (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials domain) {first last : Gaussian.Basic.Canonical}
    (firstInside : domain.Contains first)
    (lastInside : domain.Contains last) {distance : Fraction.Rational}
    (close : Data.Gaussian.Norm.Basic.normSq (last - first) ≤ distance) :
    (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrementError ((polynomials.get row).coefficient.eval first) first last
        ((polynomials.get row).primitive.value.eval first) ((polynomials.get row).primitive.value.eval last))) ≤
      bounds.remainder * distance^2 := by
  have pointwise (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrementError ((polynomials.get row).coefficient.eval first) first last
        ((polynomials.get row).primitive.value.eval first) ((polynomials.get row).primitive.value.eval last)) ≤
          (bounds.entries.get row).remainder * distance^2 := by
    have equal : Energy.AffineTriangle.affinePrimitiveIncrementError ((polynomials.get row).coefficient.eval first)
      first last
        ((polynomials.get row).primitive.value.eval first) ((polynomials.get row).primitive.value.eval last) =
        (polynomials.get row).primitive.value.eval last - (polynomials.get row).primitive.value.eval first -
          (polynomials.get row).coefficient.eval first * (last - first) := by
      unfold Energy.AffineTriangle.affinePrimitiveIncrementError Energy.AffineTriangle.affinePrimitiveIncrement
      ring1
    rw [equal]
    exact ((bounds.entries.get row).increment_box_le firstInside lastInside).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.pow_le_pow_direct
        (Gaussian.Norm.Basic.normSq_nonneg _) close 2)
        (bounds.entries.get row).remainder_nonnegative)
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ pointwise)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
  rw [FiniteSum.Fin.sumFin_mul_right] at bound
  exact bound.trans_eq (by rw [bounds.remainder_eq]; ring1)

end RegularBasisBounds
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
