module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
public import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Name.Coherent.Request
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive endpoint readings on an original continued sheet

A shared finite root witness is retained at the original point owner's
reading state. The same cached inverse model and odd powers bound its primitive
readings against the retained quadratic expression. The root witness need not
satisfy the exact square equation; its actual residual remains in the bound.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation.Rational
open Purelib.Approximation.Gaussian

variable {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

/-- The exact state carrier of the original continued point's selected root process. -/
@[expose] def RootState (sample : Point patch point) : Type := sample.certificate.value.name.process.State

/-- Possibility of an actual scalar reading at the original continued point's selected process state. -/
@[expose] def RootPossible (sample : Point patch point) (state : RootState sample) (root : Canonical) : Prop :=
  sample.certificate.value.name.process.Possible state root

set_option genInjectivity false in
/-- A shared original root witness with cached scalar readings of one actual inverse-model stage.

The model, its odd-power cache and the original point owner are retained. Both
state and reading certificates concern the same root witness, so adjacent
cells may reuse it through their explicit original-owner transports. -/
structure PrimitiveReading (sample : Point patch point) (depth : Nat)
    (model : Model polynomial patch.base.box) (powers : OddPowers model.value) where
  /-- The actual original point owner retained with its selected sheet. -/
  owner : Point patch point
  /-- The retained point is the original owner. -/
  owner_eq : owner = sample
  /-- This actual cached model is the original selected refinement stage. -/
  model_eq : model = patch.base.refine depth
  /-- The actual root process state from which the shared witness was read. -/
  state : RootState sample
  /-- The retained scalar root witness. -/
  root : Canonical
  /-- The shared witness is possible at that exact retained root state. -/
  possible : RootPossible sample state root
  /-- The same shared witness persists at the original scheduled residual-reading state. -/
  atReading : RootPossible sample (sample.readingState depth) root
  /-- The cached scalar inverse-model evaluation. -/
  inverse : Canonical
  /-- The scalar inverse reading belongs to this same actual cached model. -/
  inverse_eq : inverse = model.value.eval point
  /-- The cached scalar cube reads the original shared odd-power cache. -/
  cube : Canonical
  /-- The scalar cube belongs to this same actual retained polynomial power cache. -/
  cube_eq : cube = powers.cube.eval point
  /-- The cached scalar fifth power reads the same original shared odd-power cache. -/
  fifth : Canonical
  /-- The scalar fifth power belongs to that original retained power cache. -/
  fifth_eq : fifth = powers.fifth.eval point
  /-- The cached scalar residual of the same inverse model. -/
  residual : Canonical
  /-- The residual reading belongs to the same actual cached model. -/
  residual_eq : residual = model.residual.eval point

constructive_injectivity PrimitiveReading

/-- Retain an externally shared root witness and read the same original model and odd-power caches once.

The supplied possibilities concern the actual retained witness and source
states. No independent root or primitive endpoint comparison is supplied. -/
@[expose] def retainPrimitiveReading (sample : Point patch point) (depth : Nat)
    (model : Model polynomial patch.base.box) (sameModel : model = patch.base.refine depth)
    (powers : OddPowers model.value) (state : RootState sample) (root : Canonical)
    (possible : RootPossible sample state root)
    (atReading : RootPossible sample (sample.readingState depth) root) :
    PrimitiveReading sample depth model powers :=
  let inverse := model.value.eval point
  let cube := powers.cube.eval point
  let fifth := powers.fifth.eval point
  let residual := model.residual.eval point
  ⟨sample, rfl, sameModel, state, root, possible, atReading, inverse, rfl, cube, rfl, fifth, rfl, residual, rfl⟩

namespace PrimitiveReading

variable {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
    {powers : OddPowers model.value}

/-- View the same actual primitive-root state and witness as an original finite root observation.

Only the existing Reading container caches its visible radius. The supplied
primitive reading, original Point, inverse model and power caches are not
rebuilt, and no process is sampled to form this view.
-/
def rootReading (reading : PrimitiveReading sample depth model powers) :
    Equivalence.Observation.Reading sample.certificate.value :=
  Equivalence.Observation.Reading.retain sample.certificate.value
    reading.state reading.root reading.possible

/-- The actual finite root observation keeps the identical primitive witness. -/
theorem rootReading_value (reading : PrimitiveReading sample depth model powers) :
    reading.rootReading.value = reading.root := (rfl)

/-- The finite root observation's radius is the radius of its identical actual retained primitive state. -/
theorem rootReading_radius (reading : PrimitiveReading sample depth model powers) :
    reading.rootReading.radius = (sample.certificate.value.name.process.ball reading.state).radiusSq := (rfl)

/-- The actual shared root witness has positive squared norm and is therefore nonzero. -/
theorem root_nonzero (reading : PrimitiveReading sample depth model powers) : reading.root ≠ 0 := by
  have positive := patch.rootLower_positive.trans_le (sample.candidate_lower _ reading.possible)
  intro zero
  rewrite [zero, Data.Gaussian.Basic.Canonical.normSq_zero] at positive
  exact (lt_irrefl _) positive

/-- The cached inverse reading satisfies the original same-depth inverse-root error bound. -/
theorem inverse_error_le (reading : PrimitiveReading sample depth model powers) (inside : patch.box.Contains point) :
    Norm.Basic.normSq (reading.inverse - reading.root⁻¹) ≤
      Geometric.Basic.quarterRadius patch.inverseErrorScale depth := by
  rewrite [Norm.Basic.normSq_eq_canonical, reading.inverse_eq]
  have stageReading := congrArg (fun stage : Model polynomial patch.base.box => stage.value.eval point) reading.model_eq
  rewrite [stageReading]
  exact sample.reading_inverse_error inside depth reading.atReading

/-- The original shared root witness's square residual obeys the actual scheduled relative bound. -/
theorem root_residual_le (reading : PrimitiveReading sample depth model powers) :
    Norm.Basic.normSq (reading.root ^ 2 - polynomial.eval point) ≤
      relativeRootError depth * sample.parameterNorm := by
  rewrite [Norm.Basic.normSq_eq_canonical, sample.parameterNorm_eq]
  exact sample.candidate_residual (relativeRootError depth) (relativeRootError_positive depth) reading.atReading

/-- The cached inverse-model residual obeys the original model's geometric refinement bound. -/
theorem residual_le (reading : PrimitiveReading sample depth model powers) (inside : patch.box.Contains point) :
    Norm.Basic.normSq reading.residual ≤ Geometric.Basic.quarterRadius patch.base.model.bound depth := by
  rewrite [Norm.Basic.normSq_eq_canonical, reading.residual_eq, model.residual_eq]
  have stageReading := congrArg (fun stage : Model polynomial patch.base.box => stage.value.eval point) reading.model_eq
  rewrite [stageReading]
  exact patch.base.model.refine_residualBound depth point (patch.box_refines.contains inside)

/-- The reciprocal squared norm of the actual shared root is bounded by the retained positive source root floor. -/
theorem inverse_root_norm_le (reading : PrimitiveReading sample depth model powers) :
    Norm.Basic.normSq (reading.root⁻¹) ≤ patch.rootLower⁻¹ := by
  rewrite [Norm.Basic.normSq_eq_canonical,
    Data.Gaussian.Basic.Canonical.normSq_inv reading.root reading.root_nonzero]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct patch.rootLower_positive
    (sample.candidate_lower _ reading.possible)

/-- The same actual cached inverse reading has a uniform ceiling obtained from the original root and error bounds. -/
theorem inverse_norm_le (reading : PrimitiveReading sample depth model powers) (inside : patch.box.Contains point) :
    Norm.Basic.normSq reading.inverse ≤ 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) := by
  have identity : reading.inverse = (reading.inverse - reading.root⁻¹) + reading.root⁻¹ := by ring1
  have norm := Norm.Bounds.normSq_add_le_two (reading.inverse - reading.root⁻¹) (reading.root⁻¹)
  rewrite [← identity] at norm
  exact norm.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add ((reading.inverse_error_le inside).trans
      (Geometric.Basic.quarterRadius_le_scale patch.inverseErrorScale_positive.le depth)) reading.inverse_root_norm_le)
    (by decide))

/-- The same root and original parameter relate the reciprocal reading to the quadratic generator coefficient. -/
private theorem inverse_generator_difference (root parameter : Canonical) (rootNonzero : root ≠ 0)
    (parameterNonzero : parameter ≠ 0) :
    root⁻¹ - root * parameter⁻¹ = root⁻¹ * (parameter - root ^ 2) * parameter⁻¹ := by
  have rootUnit := Algebra.Field.ExplicitField.mul_inv_cancel root rootNonzero
  have parameterUnit := Algebra.Field.ExplicitField.mul_inv_cancel parameter parameterNonzero
  calc
    _ = root⁻¹ * (parameter * parameter⁻¹) - (root * root⁻¹) * root * parameter⁻¹ := by
      rewrite [rootUnit, parameterUnit]
      ring1
    _ = _ := by ring1

/-- The retained ceiling comparing an actual inverse reading with the same root's exact divided generator reading. -/
@[expose] def generatorBound (_reading : PrimitiveReading sample depth model powers) : Fraction.Rational :=
  2 * (Geometric.Basic.quarterRadius patch.inverseErrorScale depth +
    patch.rootLower⁻¹ * (relativeRootError depth * sample.parameterNorm) *
      Norm.Basic.normSq ((polynomial.eval point)⁻¹))

/-- The inverse reading is quantitatively close to the original quadratic generator divided by the actual parameter.

The root's approximate-square residual is charged explicitly. The exact
coefficient denominator remains the original polynomial parameter. -/
theorem generator_error_le (reading : PrimitiveReading sample depth model powers) (inside : patch.box.Contains point) :
    Norm.Basic.normSq (reading.inverse - reading.root * (polynomial.eval point)⁻¹) ≤ reading.generatorBound := by
  have identity : reading.inverse - reading.root * (polynomial.eval point)⁻¹ =
      (reading.inverse - reading.root⁻¹) +
        reading.root⁻¹ * (polynomial.eval point - reading.root ^ 2) * (polynomial.eval point)⁻¹ := by
    rewrite [← inverse_generator_difference reading.root (polynomial.eval point) reading.root_nonzero
      sample.owner.parameterNonzero]
    ring1
  have rootResidual := reading.root_residual_le
  have productBound : Norm.Basic.normSq
      (reading.root⁻¹ * (polynomial.eval point - reading.root ^ 2) * (polynomial.eval point)⁻¹) ≤
      patch.rootLower⁻¹ * (relativeRootError depth * sample.parameterNorm) *
        Norm.Basic.normSq ((polynomial.eval point)⁻¹) := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Norm.Bounds.normSq_sub_symm]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_direct reading.inverse_root_norm_le rootResidual
        (Norm.Basic.normSq_nonneg _) (Fraction.Order.Field.inv_pos_direct patch.rootLower_positive).le)
      (Norm.Basic.normSq_nonneg _)
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (reading.inverse_error_le inside) productBound) (by decide))

end PrimitiveReading

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
