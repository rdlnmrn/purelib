module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual cofactor readings and constant waist integration cells

A cell samples the supplied original lift's cached cofactor channel once.
Its parameter endpoints, coefficient cache and allowance are retained with
exact equations. Every residual-certified in-window cofactor candidate at an
in-span parameter satisfies the uniform cell bound. These are chart-time
integration cells; geometric lifted-cycle attachments remain separate evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Cells

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {span : Interval.Bounds}
variable {unit : Owner ((unitPolynomial site).eval
  (point site parameter (direction quarter span.lower) regular bound).base)}

set_option genInjectivity false in
/-- One constant parameter-integration cell retaining the original differential, span and actual starting cubic lift.

The complete supplied lift remains an index. Its cached cofactor channel
determines the sampled root and window, and the same numerical budget pays
the chart-width and root-window contributions separately.
-/
structure Model (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit) where
  /-- The actual supplied cofactor owner's retained original root window. -/
  rootBox : Box
  /-- The window belongs to the complete original cached cofactor owner. -/
  rootBox_eq : rootBox = lift.unitOwner.track.initial.box
  /-- The retained state of the original cached cofactor process from which sampling starts. -/
  state : lift.unitRoot.value.name.process.State
  /-- The finite sampling index on the actual supplied cofactor channel. -/
  sampleIndex : Nat
  /-- The actual root reading computed once at the retained index. -/
  centerRoot : Canonical
  /-- The reading is the original cached cofactor name's exact indexed witness. -/
  centerRoot_eq : centerRoot = Process.Sampling.witnessAt lift.unitRoot.value.name.process
    state sampleIndex
  /-- The cached root reading remains in that original owner's window. -/
  centerRoot_inside : rootBox.Contains centerRoot
  /-- The cached root reading meets the original cofactor's square-residual threshold. -/
  centerResidual : normSq (centerRoot * centerRoot - (unitPolynomial site).eval
    (point site parameter (direction quarter span.lower) regular bound).base) ≤
    SquareRootSheets.residualTarget ((unitPolynomial site).eval
      (point site parameter (direction quarter span.lower) regular bound).base)
  /-- The coefficient computed once from this same original root reading. -/
  center : Canonical
  /-- The cached coefficient uses the original differential and parameter chart. -/
  center_eq : center = data.coefficient quarter regular bound span.lower centerRoot
  /-- The retained local squared-error allowance. -/
  allowance : Fraction.Rational
  /-- The allowance pays the same chart span and original root-window diagonal. -/
  allowance_eq : allowance = data.parameterSlope * (span.upper - span.lower) ^ 2 +
    data.rootSlope * rootBox.diagonalSq
  /-- The retained local allowance is nonnegative. -/
  allowance_nonnegative : 0 ≤ allowance

constructive_injectivity Model

namespace Model

open Purelib.Data.Rat.Fraction.Order

/-- Sample one retained state of the actual supplied cofactor channel and construct its constant cell cache. -/
@[expose] def ofState (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit)
    (state : lift.unitRoot.value.name.process.State)
    (index : Nat) : Model data simple lift := by
  let name := lift.unitRoot.value.name
  let centerRoot := Process.Sampling.witnessAt name.process state index
  have possible := Process.Sampling.witnessAt_possible_start name.process state index
  change lift.unitRoot.value.name.process.Possible state centerRoot at possible
  have ownerEq : lift.unitRoot.value.name.process =
      (lift.unitOwner.certificate lift.unitOwner.parameterNonzero).value.name.process := by
    rewrite [lift.unitRoot_eq]
    rfl
  have original := Process.Sampling.possible_castState ownerEq state possible
  have inside := Owner.certificate_candidate_in_initial_box lift.unitOwner lift.unitOwner.parameterNonzero _ original
  have residual := CertifiedSquareRoot.root_candidate_residual_lt lift.unitOwner.parameterNonzero
    lift.unitOwner.track _ original
  rewrite [← Norm.Basic.normSq_eq_canonical] at residual
  let rootBox := lift.unitOwner.track.initial.box
  let center := data.coefficient quarter regular bound span.lower centerRoot
  let allowance := data.parameterSlope * (span.upper - span.lower) ^ 2 + data.rootSlope * rootBox.diagonalSq
  have nonnegative : 0 ≤ allowance :=
    (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct data.slopes_nonnegative.1
          (Arithmetic.sq_nonneg_direct _))
        (Arithmetic.mul_nonneg_direct data.slopes_nonnegative.2 rootBox.diagonalSq_nonneg))
  exact
    { rootBox, rootBox_eq := rfl
      state := state
      sampleIndex := index
      centerRoot, centerRoot_eq := rfl
      centerRoot_inside := inside
      centerResidual := residual.le
      center, center_eq := rfl
      allowance, allowance_eq := rfl
      allowance_nonnegative := nonnegative }

/-- Sample the original supplied cofactor name from its unchanged retained starting state. -/
@[expose] def build (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit)
    (index : Nat) : Model data simple lift :=
  ofState data simple lift lift.unitRoot.value.name.state index

variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit}

/-- Change the original differential while reusing the identical actual root reading, window and sampling index.

Only the new coefficient and its numerical budget are computed. Both models
retain the same original cubic lift and its cached signed cofactor channel.
-/
@[expose] def reweight (model : Model data simple lift) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Bounds.Data site parameter nextDifferential) (nextSimple : nextDifferential.denominatorPairs = 0) :
    Model nextData nextSimple lift :=
  let center := nextData.coefficient quarter regular bound span.lower model.centerRoot
  let allowance := nextData.parameterSlope * (span.upper - span.lower) ^ 2 +
    nextData.rootSlope * model.rootBox.diagonalSq
  { rootBox := model.rootBox, rootBox_eq := model.rootBox_eq
    state := model.state
    sampleIndex := model.sampleIndex
    centerRoot := model.centerRoot, centerRoot_eq := model.centerRoot_eq
    centerRoot_inside := model.centerRoot_inside
    centerResidual := model.centerResidual
    center, center_eq := rfl
    allowance, allowance_eq := rfl
    allowance_nonnegative :=
      (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct nextData.slopes_nonnegative.1
            (Arithmetic.sq_nonneg_direct _))
          (Arithmetic.mul_nonneg_direct nextData.slopes_nonnegative.2 model.rootBox.diagonalSq_nonneg)) }

/-- Differential reweighting retains the exact original root window, reading and sampling index. -/
theorem reweight_root (model : Model data simple lift) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Bounds.Data site parameter nextDifferential) (nextSimple : nextDifferential.denominatorPairs = 0) :
    (model.reweight nextData nextSimple).rootBox = model.rootBox ∧
      (model.reweight nextData nextSimple).centerRoot = model.centerRoot ∧
      (model.reweight nextData nextSimple).sampleIndex = model.sampleIndex := ⟨rfl, rfl, rfl⟩

/-- The cell's starting observation reuses its actual original coefficient cache with zero polynomial residual. -/
@[expose] def centerObservation (model : Model data simple lift) :
    Integration.Polynomial.Gaussian.Cell.Basic.LocalObservation
      (Gaussian.Basic.constant model.center) model.allowance :=
  { parameter := 0
    integrandReading := model.center
    error := 0
    decomposition := by
      rewrite [Gaussian.Evaluation.eval_constant]
      exact Basic.sub_self _
    error_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_zero]
      exact model.allowance_nonnegative }

/-- Read the same retained coefficient and allowance as a constant chart-parameter integration cell. -/
@[expose] def cell (model : Model data simple lift) : CellModel where
  start := ⟨span.lower, 0⟩
  finish := ⟨span.upper, 0⟩
  polynomial := Gaussian.Basic.constant model.center
  localAllowance := model.allowance
  localAllowance_nonneg := model.allowance_nonnegative
  observations := [model.centerObservation]

/-- The actual cell integral sample is the original parameter width times its identical cached coefficient. -/
theorem integralSample (model : Model data simple lift) :
    model.cell.integralSample = (⟨span.upper - span.lower, 0⟩ : Canonical) * model.center := by
  have displacement : model.cell.finish - model.cell.start = (⟨span.upper - span.lower, 0⟩ : Canonical) := by
    apply Basic.ext
    · rfl
    · change (0 : Fraction.Rational) - 0 = 0
      ring1
  calc
    _ = (model.cell.finish - model.cell.start) * model.center := CellModel.integralSample_constant _ _ rfl
    _ = _ := congrArg (fun value => value * model.center) displacement

/-- Every residual-certified in-window cofactor reading on the original span meets the retained cell allowance. -/
theorem candidate_error_le (model : Model data simple lift) {time : Fraction.Rational}
    (inside : span.Contains time) {root : Canonical} (rootInside : model.rootBox.Contains root)
    (residual : normSq (root * root - (unitPolynomial site).eval
      (point site parameter (direction quarter time) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter time) regular bound).base)) :
    normSq (data.coefficient quarter regular bound time root - model.center) ≤ model.allowance := by
  have parameterBound := Interval.Radius.sub_sq_le_sampleRadiusSq span (sample := span.lower) inside
  rewrite [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at parameterBound
  have rootBound := Box.normSq_sub_le_diagonalSq model.centerRoot_inside rootInside
  have comparison := data.coefficient_distance_le quarter regular bound time span.lower
    residual model.centerResidual rootBound
  rewrite [model.center_eq, model.allowance_eq]
  exact comparison.trans (Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct parameterBound data.slopes_nonnegative.1)
    (Fraction.Order.Basic.le_refl _))

/-- Map one local cell fraction to its exact original chart parameter. -/
@[expose] def time (_model : Model data simple lift) (fraction : Fraction.Rational) : Fraction.Rational :=
  span.lower + (span.upper - span.lower) * fraction

/-- Every local unit fraction maps into the same retained original chart span. -/
theorem time_inside (model : Model data simple lift) {fraction : Fraction.Rational}
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) : span.Contains (model.time fraction) := by
  have widthNonnegative := Arithmetic.sub_nonneg_direct span.valid
  constructor
  · have product := Arithmetic.mul_nonneg_direct widthNonnegative inside.1
    exact (show span.lower = span.lower + 0 by ring1).trans_le
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) product)
  · calc
      _ ≤ span.lower + (span.upper - span.lower) * 1 :=
        Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2 widthNonnegative)
      _ = _ := by ring1

/-- Build a local observation from an actual in-window cofactor candidate at the original mapped chart parameter. -/
@[expose] def observation (model : Model data simple lift) (fraction : Fraction.Rational)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (root : Canonical) (rootInside : model.rootBox.Contains root)
    (residual : normSq (root * root - (unitPolynomial site).eval
      (point site parameter (direction quarter (model.time fraction)) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter (model.time fraction)) regular bound).base)) :
    Integration.Polynomial.Gaussian.Cell.Basic.LocalObservation model.cell.polynomial model.cell.localAllowance :=
  let reading := data.coefficient quarter regular bound (model.time fraction) root
  { parameter := fraction
    integrandReading := reading
    error := reading - model.center
    decomposition := by
      rewrite [cell, Gaussian.Evaluation.eval_constant]
      rfl
    error_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact model.candidate_error_le (model.time_inside inside) rootInside residual }

end Model

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Cells
