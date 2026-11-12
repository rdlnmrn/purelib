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

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian

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
  {value : Basic.Canonical -> Basic.Canonical}
    (one : Basic.Canonical) (negOne : Basic.Canonical) (im : Basic.Canonical) (negIm :
      Basic.Canonical)
    (one_eq : value 1 = one) (negOne_eq : value (-1) = negOne)
    (im_eq : value BilinearPolarization.imaginary = im)
      (negIm_eq : value (-BilinearPolarization.imaginary) =
      negIm) :
    normSq (BilinearPolarization.extract value) <=
      4 * (normSq one + normSq negOne + normSq im + normSq negIm) := by
  have imaginaryNorm : normSq (BilinearPolarization.imaginary
    : Basic.Canonical) = 1 := by decide
  have quarterNorm : normSq (⟨(1 / 4 : Fraction.Rational), 0⟩ : Basic.Canonical) = (1 / 16 : Fraction.Rational)
    := by
    decide
  have first : normSq (one - negOne) <= 2 * (normSq one + normSq negOne) :=
    by simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Bounds.normSq_sub_le_two one negOne
  have second : normSq (im - negIm) <= 2 * (normSq im + normSq negIm) :=
    by simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Bounds.normSq_sub_le_two im negIm
  have product : normSq (BilinearPolarization.imaginary * (im
    - negIm)) <=
      2 * (normSq im + normSq negIm) := by
    rw [Basic.Canonical.normSq_mul, imaginaryNorm]
    simpa using second
  have combined : normSq ((one - negOne) -
    BilinearPolarization.imaginary * (im - negIm)) <=
      4 * (normSq one + normSq negOne + normSq im + normSq negIm) := by
    have triangle := Norm.Bounds.normSq_sub_le_two (one - negOne)
      (BilinearPolarization.imaginary * (im - negIm))
    simp only [Norm.Basic.normSq_eq_canonical] at triangle
    exact triangle.trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct first
        product) (by decide)).trans_eq
        (by ring1))
  have extractEq : BilinearPolarization.extract value =
      (⟨(1 / 4 : Fraction.Rational), 0⟩ : Basic.Canonical) *
        (one - negOne - BilinearPolarization.imaginary * (im
          - negIm)) := by
    unfold BilinearPolarization.extract
    rw [one_eq, negOne_eq, im_eq, negIm_eq]
  rw [extractEq, Basic.Canonical.normSq_mul, quarterNorm]
  have nonnegative : 0 <= normSq one + normSq negOne + normSq im + normSq negIm :=
    add_nonneg (add_nonneg (add_nonneg (Basic.Canonical.normSq_nonneg one)
      (Basic.Canonical.normSq_nonneg negOne))
      (Basic.Canonical.normSq_nonneg im)) (Basic.Canonical.normSq_nonneg negIm)
  calc
    (1 / 16 : Fraction.Rational) *
        normSq (one - negOne - BilinearPolarization.imaginary
          * (im - negIm)) <=
      (1 / 16 : Fraction.Rational) *
        (4 * (normSq one + normSq negOne + normSq im + normSq negIm)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct combined (by decide)
    _ = 4 * (normSq one + normSq negOne + normSq im + normSq negIm) * (1 / 16) := by ring1
    _ <= 4 * (normSq one + normSq negOne + normSq im + normSq negIm) * 1 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 / 16 : Fraction.Rational) <= 1)
        (Arithmetic.mul_nonneg_direct (by decide) nonnegative)
    _ = 4 * (normSq one + normSq negOne + normSq im + normSq negIm) :=
      Fraction.Field.mul_one_direct _

/-- Bounding the mixed Hermitian surface residual at the four polarization
directions bounds the ordered first-bilinear determinant. -/
theorem
  bilinearResidual_normSq_le
  {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {branches : Branches.BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {base : FramedPuncturedGrid curve branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
      2} {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
      sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} (prepared :
      PeriodPrograms.Prepared paired)
    (first second : OrientedEdge lifted.vertices.count -> Basic.Canonical) {bound : Fraction.Rational}
    (oneB : normSq (BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second 1)) <= bound)
    (negOneB : normSq (BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second (-1))) <= bound)
    (imB : normSq (BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second
      BilinearPolarization.imaginary)) <= bound)
    (negImB : normSq (BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second
      (-BilinearPolarization.imaginary))) <= bound) :
    normSq (BilinearIdentity.bilinearResidual prepared first second) <= 16 *
      bound := by
  have extracted := BilinearPolarization.extract_normSq_le
    (value := fun coefficient => BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second coefficient))
    (one := BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second 1))
    (negOne := BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second (-1)))
    (im := BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second
      BilinearPolarization.imaginary))
    (negIm := BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second
      (-BilinearPolarization.imaginary)))
    rfl rfl rfl rfl
  unfold BilinearIdentity.bilinearResidual
  refine extracted.trans ?_
  have nonnegative : 0 <= bound := (Basic.Canonical.normSq_nonneg _).trans oneB
  have sumBound : normSq (BilinearIdentity.surfaceResidual prepared
    (BilinearPolarization.mix first second 1)) +
      normSq (BilinearIdentity.surfaceResidual prepared
        (BilinearPolarization.mix first second (-1))) +
      normSq (BilinearIdentity.surfaceResidual prepared
        (BilinearPolarization.mix first second
        BilinearPolarization.imaginary)) +
      normSq (BilinearIdentity.surfaceResidual prepared
        (BilinearPolarization.mix first second
        (-BilinearPolarization.imaginary))) <=
      4 * bound := by
    calc
      _ <= ((bound + bound) + bound) + bound :=
        Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct
          (Arithmetic.add_le_add_direct oneB negOneB) imB) negImB
      _ = 4 * bound := by ring1
  calc
    4 * (normSq (BilinearIdentity.surfaceResidual prepared
      (BilinearPolarization.mix first second 1)) +
        normSq (BilinearIdentity.surfaceResidual prepared
          (BilinearPolarization.mix first second (-1))) +
        normSq (BilinearIdentity.surfaceResidual prepared
          (BilinearPolarization.mix first second
          BilinearPolarization.imaginary)) +
        normSq (BilinearIdentity.surfaceResidual prepared
          (BilinearPolarization.mix first second
          (-BilinearPolarization.imaginary)))) <=
      4 * (4 * bound) := Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (by decide)
    _ = 16 * bound := by ring1

end BilinearPolarization
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
