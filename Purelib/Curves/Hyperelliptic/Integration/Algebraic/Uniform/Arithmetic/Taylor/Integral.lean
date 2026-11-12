module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor
public import Purelib.Integration.Polynomial.Gaussian.Cell.ParameterVariation
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Arithmetic Taylor certificates for actual uniformly observed cell integrals

The three original cells may have different curve and differential owners.
Every query retains its independently constructed numerical Taylor evidence
and operational comparisons. Paid model allowances and a uniform numerical
factor ceiling give an explicit finite remainder on the same actual integrals.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

open Purelib
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {genus : Nat} {curves : Data.Vector (HyperellipticCurve genus) 3}
    {differentials : (entry : Fin 3) → OddPowerDifferential (curves entry).polynomial}
    {starts finishes : Data.Vector (LiftedPoint 2) 3}
    {lifted : (entry : Fin 3) → LiftedCell (starts entry) (finishes entry)}
    {cells : Data.Vector CellModel 3}
    (uniforms : (entry : Fin 3) → UniformCellCertificate (curves entry) (differentials entry)
      (lifted entry) (cells entry))
    {points : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter } →
      Data.Vector Canonical 3}
    {sheets : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter } →
      Data.Vector CoherentNamed 3}
    {apart : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      (entry : Fin 3) → Named.Apart (sheets time entry).name}
    {states : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      (entry : Fin 3) → (sheets time entry).name.process.State}
    {rootObservations : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter } →
      Data.Vector RootObservation 3}
    {accuracy : Approximation.AccuracyRequest}
    (numerics : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      (entry : Fin 3) → Reading (differentials entry) (points time entry) (sheets time entry) (apart time entry)
        (states time entry) (rootObservations time entry) accuracy)
    (identities : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      (entry : Fin 3) → PowerIdentity (sheets time entry) 2
        ((curves entry).polynomial.eval (points time entry)))
    (comparisons : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      TaylorComparisons (cells := cells) (lifted := lifted)
        (times := Data.Vector.Basic.vectorOfFn (fun _ : Fin 3 => time.val))
        (uniforms := fun entry => Eq.mpr
          (congrArg (UniformObservation (curves entry) (differentials entry) (lifted entry) (cells entry))
            (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time.val) entry))
          ((uniforms entry).query time.val time.property.1 time.property.2))
        (numerics := numerics time) (identities := identities time))
    {increment : Canonical}
    (certificates : (time : { parameter : Fraction.Rational // Cell.Primitive.unitInterval.Contains parameter }) →
      Quadratic.Basic.Certificate increment)
    (base_eq : ∀ time, (certificates time).base = (numerics time 0).reading)
    (output_eq : ∀ time, (certificates time).output = (numerics time 1).reading)
    (slope_eq : ∀ time, (certificates time).slope = (numerics time 2).reading)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (allowancesPaid : ∀ entry, (cells entry).localAllowance ≤ accuracy.tolerance)
    (parameterPaid : accuracy.tolerance ≤ Norm.Basic.normSq increment ^ 2)
    (base_start : (cells 0).start = (cells 1).start)
    (base_finish : (cells 0).finish = (cells 1).finish)
    (slope_start : (cells 2).start = (cells 1).start)
    (slope_finish : (cells 2).finish = (cells 1).finish)
    (factor : Fraction.Rational) (factor_nonneg : 0 ≤ factor)
    (factor_le : ∀ time, (certificates time).factor ≤ factor)

/-- Derive a parameter Taylor certificate for the actual three original uniformly observed cell integrals.

The numeric certificates are constructed before this operation. At each
original unit query, the stored comparisons derive the polynomial remainder
and its factor, paying all three actual model discrepancies. Integration then
computes the residual and factor from the same unchanged polynomial tables.
No desired integral remainder is an input.
-/
def integralCertificate : Quadratic.Basic.Certificate increment :=
  let pointwise := fun parameter (inside : Cell.Primitive.unitInterval.Contains parameter) =>
    polynomialCertificate (comparisons ⟨parameter, inside⟩) (certificates ⟨parameter, inside⟩)
      (base_eq ⟨parameter, inside⟩) (output_eq ⟨parameter, inside⟩) (slope_eq ⟨parameter, inside⟩)
      unit allowancesPaid parameterPaid
  Cell.ParameterVariation.certificate (cells 0) (cells 1) (cells 2) increment
    base_start base_finish slope_start slope_finish
    (4 * (factor + 7 / 2 + 7 / 2 + 7 / 2))
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.add_le_add_direct
          (Arithmetic.add_le_add_direct factor_nonneg
            (by decide +kernel : (0 : Fraction.Rational) ≤ 7 / 2))
          (by decide +kernel : (0 : Fraction.Rational) ≤ 7 / 2))
        (by decide +kernel : (0 : Fraction.Rational) ≤ 7 / 2)))
    pointwise
    (by
      intro parameter inside
      have reading := polynomialCertificate_base (comparisons ⟨parameter, inside⟩)
        (certificates ⟨parameter, inside⟩) (base_eq ⟨parameter, inside⟩)
        (output_eq ⟨parameter, inside⟩) (slope_eq ⟨parameter, inside⟩) unit allowancesPaid parameterPaid
      rewrite [Data.Vector.Basic.vectorOfFn_apply] at reading
      exact reading)
    (by
      intro parameter inside
      have reading := polynomialCertificate_output (comparisons ⟨parameter, inside⟩)
        (certificates ⟨parameter, inside⟩) (base_eq ⟨parameter, inside⟩)
        (output_eq ⟨parameter, inside⟩) (slope_eq ⟨parameter, inside⟩) unit allowancesPaid parameterPaid
      rewrite [Data.Vector.Basic.vectorOfFn_apply] at reading
      exact reading)
    (by
      intro parameter inside
      have reading := polynomialCertificate_slope (comparisons ⟨parameter, inside⟩)
        (certificates ⟨parameter, inside⟩) (base_eq ⟨parameter, inside⟩)
        (output_eq ⟨parameter, inside⟩) (slope_eq ⟨parameter, inside⟩) unit allowancesPaid parameterPaid
      rewrite [Data.Vector.Basic.vectorOfFn_apply] at reading
      exact reading)
    (by
      intro parameter inside
      change (polynomialCertificate _ _ _ _ _ _ _ _).factor ≤ _
      rewrite [polynomialCertificate_factor]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          (Arithmetic.add_le_add_direct
            (Arithmetic.add_le_add_direct (factor_le ⟨parameter, inside⟩)
              (Fraction.Order.Basic.le_refl (7 / 2)))
            (Fraction.Order.Basic.le_refl (7 / 2)))
          (Fraction.Order.Basic.le_refl (7 / 2))) (by decide +kernel))

/-- The constructed base retains the actual original base-cell integral. -/
theorem integralCertificate_base :
    (integralCertificate uniforms numerics identities comparisons certificates
      base_eq output_eq slope_eq unit allowancesPaid parameterPaid
      base_start base_finish slope_start slope_finish factor factor_nonneg factor_le).base =
        (cells 0).integralSample := by
  unfold integralCertificate
  rewrite [Cell.ParameterVariation.certificate_base]
  rfl

/-- The output retains the actual original changed-parameter cell integral and its curve owner. -/
theorem integralCertificate_output :
    (integralCertificate uniforms numerics identities comparisons certificates
      base_eq output_eq slope_eq unit allowancesPaid parameterPaid
      base_start base_finish slope_start slope_finish factor factor_nonneg factor_le).output =
        (cells 1).integralSample := by
  unfold integralCertificate
  rewrite [Cell.ParameterVariation.certificate_output]
  rfl

/-- The slope retains the actual independent derivative-cell integral. -/
theorem integralCertificate_slope :
    (integralCertificate uniforms numerics identities comparisons certificates
      base_eq output_eq slope_eq unit allowancesPaid parameterPaid
      base_start base_finish slope_start slope_finish factor factor_nonneg factor_le).slope =
        (cells 2).integralSample := by
  unfold integralCertificate
  rewrite [Cell.ParameterVariation.certificate_slope]
  rfl

/-- The computed integral factor pays the numerical ceiling and all three original query comparisons. -/
theorem integralCertificate_factor :
    (integralCertificate uniforms numerics identities comparisons certificates
      base_eq output_eq slope_eq unit allowancesPaid parameterPaid
      base_start base_finish slope_start slope_finish factor factor_nonneg factor_le).factor =
        2 * (4 * (factor + 7 / 2 + 7 / 2 + 7 / 2)) * Norm.Basic.normSq (cells 1).displacement := by
  unfold integralCertificate
  rewrite [Cell.ParameterVariation.certificate_factor]
  rfl

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison
