module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Perturbation
public import Purelib.Data.Vector.Dependent
public import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Transport
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Parameter Taylor certificates on actual uniformly observed cell polynomials

Three retained arithmetic/uniform comparisons identify the prescribed base,
output and slope polynomials with the SAME original numerical certificate.
The curve and differential indices remain independent at each entry, so the
changed-parameter output keeps its actual changed polynomial owner. Genuine
joint spatial and parameter request payments derive the new Taylor remainder.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

open Purelib
open Purelib.Approximation.Gaussian
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
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curves : Data.Vector (HyperellipticCurve genus) 3}
    {differentials : (entry : Fin 3) → OddPowerDifferential (curves entry).polynomial}
    {starts finishes : Data.Vector (LiftedPoint 2) 3}
    {lifted : (entry : Fin 3) → LiftedCell (starts entry) (finishes entry)}
    {cells : Data.Vector CellModel 3} {times : Data.Vector Fraction.Rational 3}
    {uniforms : (entry : Fin 3) → UniformObservation (curves entry) (differentials entry)
      (lifted entry) (cells entry) (times entry)}
    {points : Data.Vector Canonical 3} {sheets : Data.Vector CoherentNamed 3}
    {apart : (entry : Fin 3) → Named.Apart (sheets entry).name}
    {states : (entry : Fin 3) → (sheets entry).name.process.State}
    {rootObservations : Data.Vector RootObservation 3} {accuracy : Approximation.AccuracyRequest}
    {numerics : (entry : Fin 3) → Reading (differentials entry) (points entry) (sheets entry) (apart entry)
      (states entry) (rootObservations entry) accuracy}
    {identities : (entry : Fin 3) → PowerIdentity (sheets entry) 2
      ((curves entry).polynomial.eval (points entry))}

/-- Three exact stored comparisons for base, changed-parameter output and independent source slope.

Each entry keeps its actual curve, differential, sheet, query, numerical
reading and selected comparison samples. The dependent vector materializes
those already constructed comparisons without copying their owners.
-/
abbrev TaylorComparisons := Vector.DependentVector (fun entry =>
  ArithmeticComparison (uniforms entry) (numerics entry) (identities entry))

namespace TaylorComparisons

section ConstantTime

variable (time : Fraction.Rational)
    (observed : (entry : Fin 3) → UniformObservation (curves entry) (differentials entry)
      (lifted entry) (cells entry) time)
    (base : ArithmeticComparison (observed 0) (numerics 0) (identities 0))
    (output : ArithmeticComparison (observed 1) (numerics 1) (identities 1))
    (slope : ArithmeticComparison (observed 2) (numerics 2) (identities 2))

/-- Pack three retained comparisons at one original query time into their exact constant-time Taylor family.

The actual curve, differential, cell, root, state and numerical Reading
indices remain independent at each entry. Existing castTime operations
transport the original whole comparisons along the exact vector lookup
identities. Materialization selects these three supplied caches once;
no observation, interpretation or comparison constructor executes.
-/
def atTime : TaylorComparisons (cells := cells) (lifted := lifted)
    (times := Data.Vector.Basic.vectorOfFn (fun _ : Fin 3 => time))
    (uniforms := fun entry => Eq.mpr
      (congrArg (UniformObservation (curves entry) (differentials entry) (lifted entry) (cells entry))
        (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) entry)) (observed entry))
    (numerics := numerics) (identities := identities) :=
  Data.Vector.DependentVector.ofFn
    (Data.Fin.casesDependent
      (castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 0) base)
      (Data.Fin.casesDependent
        (castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 1) output)
        (Data.Fin.casesDependent
          (castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 2) slope)
          (fun entry => Fin.elim0 entry))))

/-- The base entry is exactly the original supplied comparison after its original query-time transport. -/
private theorem atTime_base : (atTime time observed base output slope).get 0 =
    castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 0) base := by
  unfold atTime
  rfl

/-- The output entry is exactly the independent original target comparison under its query-time transport. -/
private theorem atTime_output : (atTime time observed base output slope).get 1 =
    castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 1) output := by
  unfold atTime
  rfl

/-- The slope entry is exactly the independent original derivative comparison under its query-time transport. -/
private theorem atTime_slope : (atTime time observed base output slope).get 2 =
    castTime (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 2) slope := by
  unfold atTime
  rfl

/-- Constant-time packing retains the entire original base interpretation/comparison cache. -/
theorem atTime_base_heq : HEq ((atTime time observed base output slope).get 0) base := by
  rewrite [atTime_base]
  exact castTime_heq (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 0) base

/-- Constant-time packing retains the complete independent original output comparison cache. -/
theorem atTime_output_heq : HEq ((atTime time observed base output slope).get 1) output := by
  rewrite [atTime_output]
  exact castTime_heq (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 1) output

/-- Constant-time packing retains the complete independent original slope comparison cache. -/
theorem atTime_slope_heq : HEq ((atTime time observed base output slope).get 2) slope := by
  rewrite [atTime_slope]
  exact castTime_heq (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 2) slope

/-- The base cache keeps both original selected comparison indices after constant-time packing. -/
theorem atTime_base_indices :
    ((atTime time observed base output slope).get 0).comparison.tail.leftIndex =
        base.comparison.tail.leftIndex ∧
      ((atTime time observed base output slope).get 0).comparison.tail.rightIndex =
        base.comparison.tail.rightIndex := by
  rewrite [atTime_base]
  exact castTime_indices (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 0) base

/-- The output cache keeps both independently selected original comparison indices. -/
theorem atTime_output_indices :
    ((atTime time observed base output slope).get 1).comparison.tail.leftIndex =
        output.comparison.tail.leftIndex ∧
      ((atTime time observed base output slope).get 1).comparison.tail.rightIndex =
        output.comparison.tail.rightIndex := by
  rewrite [atTime_output]
  exact castTime_indices (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 1) output

/-- The slope cache keeps both independent original comparison indices without comparison replay. -/
theorem atTime_slope_indices :
    ((atTime time observed base output slope).get 2).comparison.tail.leftIndex =
        slope.comparison.tail.leftIndex ∧
      ((atTime time observed base output slope).get 2).comparison.tail.rightIndex =
        slope.comparison.tail.rightIndex := by
  rewrite [atTime_slope]
  exact castTime_indices (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time) 2) slope

end ConstantTime

end TaylorComparisons

/-- Construct the Taylor certificate on the actual three original polynomial queries.

The input certificate is the previously constructed numerical Taylor
certificate, with exact readbacks to its actual numerical readings. The
three real model allowances and the numerical request each pay the same
parameter-fourth tolerance. Their discrepancies are derived from the
stored operational comparisons, rather than supplied as Taylor bounds.
-/
def polynomialCertificate
    (comparisons : TaylorComparisons (uniforms := uniforms) (numerics := numerics) (identities := identities))
    {increment : Canonical} (certificate : Quadratic.Basic.Certificate increment)
    (base_eq : certificate.base = (numerics 0).reading)
    (output_eq : certificate.output = (numerics 1).reading)
    (slope_eq : certificate.slope = (numerics 2).reading)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (allowancesPaid : ∀ entry, (cells entry).localAllowance ≤ accuracy.tolerance)
    (parameterPaid : accuracy.tolerance ≤ Norm.Basic.normSq increment ^ 2) :
    Quadratic.Basic.Certificate increment :=
  certificate.perturb
    (Evaluation.eval (cells 0).polynomial ⟨times 0, 0⟩)
    (Evaluation.eval (cells 1).polynomial ⟨times 1, 0⟩)
    (Evaluation.eval (cells 2).polynomial ⟨times 2, 0⟩)
    (7 / 2) (7 / 2) (7 / 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) unit
    (by
      rewrite [base_eq, Norm.Bounds.normSq_sub_symm]
      exact (comparisons.get 0).polynomial_error_le_fourth increment (allowancesPaid 0) parameterPaid)
    (by
      rewrite [output_eq, Norm.Bounds.normSq_sub_symm]
      exact (comparisons.get 1).polynomial_error_le_fourth increment (allowancesPaid 1) parameterPaid)
    (by
      rewrite [slope_eq, Norm.Bounds.normSq_sub_symm]
      exact (comparisons.get 2).polynomial_error_le_fourth increment (allowancesPaid 2) parameterPaid)

variable (comparisons : TaylorComparisons (uniforms := uniforms) (numerics := numerics) (identities := identities))
    {increment : Canonical} (certificate : Quadratic.Basic.Certificate increment)
    (base_eq : certificate.base = (numerics 0).reading)
    (output_eq : certificate.output = (numerics 1).reading)
    (slope_eq : certificate.slope = (numerics 2).reading)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (allowancesPaid : ∀ entry, (cells entry).localAllowance ≤ accuracy.tolerance)
    (parameterPaid : accuracy.tolerance ≤ Norm.Basic.normSq increment ^ 2)

/-- The constructed base is the SAME original base-cell polynomial query at its retained parameter. -/
theorem polynomialCertificate_base :
    (polynomialCertificate comparisons certificate base_eq output_eq slope_eq unit
      allowancesPaid parameterPaid).base =
      Evaluation.eval (cells 0).polynomial ⟨times 0, 0⟩ := by
  unfold polynomialCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_base]
  rfl

/-- The output retains the SAME actual changed-polynomial cell query, including its original curve index. -/
theorem polynomialCertificate_output :
    (polynomialCertificate comparisons certificate base_eq output_eq slope_eq unit
      allowancesPaid parameterPaid).output =
      Evaluation.eval (cells 1).polynomial ⟨times 1, 0⟩ := by
  unfold polynomialCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_output]
  rfl

/-- The slope is the SAME independent original source derivative-cell polynomial query. -/
theorem polynomialCertificate_slope :
    (polynomialCertificate comparisons certificate base_eq output_eq slope_eq unit
      allowancesPaid parameterPaid).slope =
      Evaluation.eval (cells 2).polynomial ⟨times 2, 0⟩ := by
  unfold polynomialCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_slope]
  rfl

/-- The internally computed factor pays the numerical remainder and all three actual query discrepancies. -/
theorem polynomialCertificate_factor :
    (polynomialCertificate comparisons certificate base_eq output_eq slope_eq unit
      allowancesPaid parameterPaid).factor =
      4 * (certificate.factor + 7 / 2 + 7 / 2 + 7 / 2) := by
  unfold polynomialCertificate
  rewrite [Quadratic.Basic.Certificate.perturb_factor]
  rfl

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

end
