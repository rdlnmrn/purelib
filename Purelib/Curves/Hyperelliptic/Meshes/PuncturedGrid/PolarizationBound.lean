module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

@[expose] public section

/-!
# Quantitative polarization of the ordered bilinear residual

`GridPairedBilinearIdentity.BilinearPolarization.extract` recovers the ordered
determinant from the Hermitian surface residual at four mixed directions. This
module bounds the extracted value by the four residual norms, so bounding the
mixed residual at the four points bounds the ordered first-bilinear residual.
-/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization

open Purelib.Data.Gaussian.Basic.Canonical (normSq)

section BilinearPolarization

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

/-- The extracted polarization is bounded by four times the sum of the four
squared residual norms. -/
theorem
  extract_normSq_le
  {value : Gaussian.Basic.Canonical -> Gaussian.Basic.Canonical}
    (one : Gaussian.Basic.Canonical) (negOne : Gaussian.Basic.Canonical) (im : Gaussian.Basic.Canonical) (negIm :
      Gaussian.Basic.Canonical)
    (one_eq : value 1 = one) (negOne_eq : value (-1) = negOne)
    (im_eq : value Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary = im)
      (negIm_eq : value (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) =
      negIm) :
    normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract value) <=
      4 * (normSq one + normSq negOne + normSq im + normSq negIm) := by
  have imaginaryNorm : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary
    : Gaussian.Basic.Canonical) = 1 := by decide
  have quarterNorm : normSq (⟨(1 / 4 : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) = (1 / 16 : Fraction.Rational)
    := by
    decide
  have first : normSq (one - negOne) <= 2 * (normSq one + normSq negOne) :=
    by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_two one negOne
  have second : normSq (im - negIm) <= 2 * (normSq im + normSq negIm) :=
    by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_sub_le_two im negIm
  have product : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (im
    - negIm)) <=
      2 * (normSq im + normSq negIm) := by
    rw [Gaussian.Basic.Canonical.normSq_mul, imaginaryNorm]
    simpa using second
  have combined : normSq ((one - negOne) -
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (im - negIm)) <=
      4 * (normSq one + normSq negOne + normSq im + normSq negIm) := by
    have triangle := Gaussian.Norm.Bounds.normSq_sub_le_two (one - negOne)
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (im - negIm))
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
    exact triangle.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
        product) (by decide)).trans_eq
        (by ring1))
  have extractEq : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract value =
      (⟨(1 / 4 : Fraction.Rational), 0⟩ : Gaussian.Basic.Canonical) *
        (one - negOne - Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (im
          - negIm)) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    rw [one_eq, negOne_eq, im_eq, negIm_eq]
  rw [extractEq, Gaussian.Basic.Canonical.normSq_mul, quarterNorm]
  have nonnegative : 0 <= normSq one + normSq negOne + normSq im + normSq negIm :=
    add_nonneg (add_nonneg (add_nonneg (Gaussian.Basic.Canonical.normSq_nonneg one)
      (Gaussian.Basic.Canonical.normSq_nonneg negOne))
      (Gaussian.Basic.Canonical.normSq_nonneg im)) (Gaussian.Basic.Canonical.normSq_nonneg negIm)
  calc
    (1 / 16 : Fraction.Rational) *
        normSq (one - negOne - Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary
          * (im - negIm)) <=
      (1 / 16 : Fraction.Rational) *
        (4 * (normSq one + normSq negOne + normSq im + normSq negIm)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct combined (by decide)
    _ = 4 * (normSq one + normSq negOne + normSq im + normSq negIm) * (1 / 16) := by ring1
    _ <= 4 * (normSq one + normSq negOne + normSq im + normSq negIm) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 / 16 : Fraction.Rational) <= 1)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
    _ = 4 * (normSq one + normSq negOne + normSq im + normSq negIm) :=
      Fraction.Field.mul_one_direct _

/-- Bounding the mixed Hermitian surface residual at the four polarization
directions bounds the ordered first-bilinear determinant. -/
theorem
  bilinearResidual_normSq_le
  {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {base : FramedPuncturedGrid curve branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
      2} {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
      sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (first second : OrientedEdge lifted.vertices.count -> Gaussian.Basic.Canonical) {bound : Fraction.Rational}
    (oneB : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second 1)) <= bound)
    (negOneB : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second (-1))) <= bound)
    (imB : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) <= bound)
    (negImB : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) <= bound) :
    normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared first second) <= 16 *
      bound := by
  have extracted := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_normSq_le
    (value := fun coefficient => Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
    (one := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second 1))
    (negOne := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second (-1)))
    (im := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))
    (negIm := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))
    rfl rfl rfl rfl
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual
  refine extracted.trans ?_
  have nonnegative : 0 <= bound := (Gaussian.Basic.Canonical.normSq_nonneg _).trans oneB
  have sumBound : normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second 1)) +
      normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second (-1))) +
      normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) +
      normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) <=
      4 * bound := by
    calc
      _ <= ((bound + bound) + bound) + bound :=
        Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Arithmetic.add_le_add_direct oneB negOneB) imB) negImB
      _ = 4 * bound := by ring1
  calc
    4 * (normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second 1)) +
        normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second (-1))) +
        normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) +
        normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) <=
      4 * (4 * bound) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (by decide)
    _ = 16 * bound := by ring1

end BilinearPolarization
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
