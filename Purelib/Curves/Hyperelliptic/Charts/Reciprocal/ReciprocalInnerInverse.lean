module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
public import Purelib.Riemann.Normalization.InverseModelRootSamples
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootComparison

public section

/-!
# A regular inverse-root polynomial across the whole reciprocal inner box

The reversed polynomial has no zero in this box for either degree parity.
The existing coefficient radius gives a uniform initial residual. Seven finite
Newton steps enter the sheet-consistent inverse-root model interface. The root seed,
polynomial and residual caches are retained with their exact specifications.
The odd-degree coordinate factor remains separate from this regular factor.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Seed)
open Purelib.Riemann.Normalization.InverseModelRootSamples (refineValue)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model correction residualStep)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar (innerBox innerRadius radius)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian.Reciprocal (reversed)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Exact rational residual and geometric bounds. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational inverse-root samples. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A finite dense polynomial over exact Gaussian rationals. -/
abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A closed rational coordinate rectangle. -/
abbrev Box := Rational.Box

/-- An inverse-root correction with residual squared norm at most one has new residual squared norm at most five
quarters of the old bound squared. -/
theorem residual_step_bound {residual : Gaussian} {bound :
  Coordinate}
    (bounded : Data.Gaussian.Norm.Basic.normSq residual ≤ bound) (small : bound ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Riemann.Normalization.InverseRootPolynomial.residualStep residual)
      ≤ (5 / 4) * bound ^ 2 := by
  have factor : Data.Gaussian.Norm.Basic.normSq ((3 :
    Gaussian) + residual) ≤ 20 := by
    calc
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (3 :
        Gaussian) +
        Data.Gaussian.Norm.Basic.normSq residual) := Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (9 + 1) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_of_eq (by decide)) (bounded.trans small)) (by decide)
      _ = _ := by decide
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg residual) bounded 2
  calc
    _ = Data.Gaussian.Norm.Basic.normSq residual ^ 2 * Data.Gaussian.Norm.Basic.normSq (3 + residual)
      * (1 / 16) := by
      unfold InverseRootPolynomial.residualStep
      rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow, Power.normSq_pow,
        show Data.Gaussian.Norm.Basic.normSq InverseRootPolynomial.half ^ 2 = (1 / 16 :
          Coordinate) by decide]
    _ ≤ bound ^ 2 * 20 * (1 / 16) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_direct square factor (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (by decide)
    _ = (5 / 4) * bound ^ 2 := by
      rw [show bound ^ 2 * 20 * (1 / 16) = bound ^ 2 * (20 * (1 / 16)) by ring1,
        show (20 : Coordinate) * (1 / 16) = 5 / 4 by
          decide]
      ring1

set_option genInjectivity false in
/-- A cached finite inverse-root polynomial and residual with a uniform box bound.

Their pointwise specifications retain the original polynomial, seed and exact finite Newton step count. -/
structure Candidate (polynomial : Polynomial) (box :
  Box) (seed :
  Gaussian) (steps : Nat) (bound :
  Coordinate) where
  /-- The cached inverse-root approximation polynomial. -/ value :
    Polynomial
  /-- At every point, the cached polynomial is the exact retained-seed Newton refinement at the indexed step count. -/
    value_eq : ∀ point, value.eval point = InverseModelRootSamples.refineValue (polynomial.eval point) seed steps
  /-- The cached residual polynomial for the retained inverse-root approximation. -/ residual :
    Polynomial
  /-- The cached residual evaluates to one minus the original polynomial times the cached approximation squared. -/
    residual_eq : ∀ point, residual.eval point = 1 - polynomial.eval point * (value.eval point) ^ 2
  /-- The retained residual squared norm satisfies its indexed bound throughout the original box. -/ bounded : ∀ point,
    box.Contains point → Data.Gaussian.Norm.Basic.normSq (residual.eval point) ≤ bound

constructive_injectivity Candidate

/-- Initialize the cached constant inverse-root polynomial and its exact residual from a uniform two-thirds seed bound.

The supplied pointwise bound certifies the original constant polynomial
and its retained residual throughout the same indexed box. -/
@[expose] def initial (polynomial : Polynomial) (box :
  Box) (seed :
  Gaussian)
    (bounded : ∀ point, box.Contains point → Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * seed
      ^ 2) ≤ 2 / 3) :
    Candidate polynomial box seed 0 (2 / 3) where
  value := DensePolynomial.constant seed
  value_eq := fun _ => by rw [DensePolynomial.eval_constant]; rfl
  residual := DensePolynomial.constant 1 - polynomial * DensePolynomial.constant (seed ^ 2)
  residual_eq := fun point => by
    rw [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_constant,
      DensePolynomial.eval_constant, DensePolynomial.eval_constant]
  bounded := fun point inside => by
    simpa only [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_constant] using bounded point
      inside

/-- Perform one polynomial inverse-root correction while retaining exact evaluation and residual identities.

The supplied next bound must pay five quarters of the old bound squared, and the old bound must be at most one. -/
@[expose] def step {polynomial : Polynomial} {box :
  Box} {seed :
  Gaussian} {steps : Nat} {bound :
  Coordinate}
    (candidate : Candidate polynomial box seed steps
      bound) (small : bound ≤ 1)
    (next : Coordinate) (paid : (5 / 4) * bound ^ 2 ≤
      next) : Candidate polynomial box seed (steps + 1)
      next where
  value := candidate.value * (DensePolynomial.constant 1 + candidate.residual.scale InverseRootPolynomial.half)
  value_eq := fun point => by
    simp only [DensePolynomial.eval_mul, DensePolynomial.eval_add, DensePolynomial.eval_constant,
      DensePolynomial.eval_scale, candidate.residual_eq, candidate.value_eq,
      InverseModelRootSamples.refineValue, Purelib.Riemann.Normalization.InverseRootPolynomial.correction, -eq_self,
        -iff_self]
    rfl
  residual := (candidate.residual * candidate.residual * (DensePolynomial.constant 3 + candidate.residual)).scale
    (InverseRootPolynomial.half ^ 2)
  residual_eq := fun point => by
    simp only [DensePolynomial.eval_scale, DensePolynomial.eval_mul, DensePolynomial.eval_add,
      DensePolynomial.eval_constant]
    have identity := InverseRootPolynomial.correction_residual (polynomial.eval point) (candidate.value.eval point)
      (candidate.residual.eval point) (candidate.residual_eq point)
    unfold Purelib.Riemann.Normalization.InverseRootPolynomial.correction
      Purelib.Riemann.Normalization.InverseRootPolynomial.residualStep at identity
    exact (by ring1 : InverseRootPolynomial.half ^ 2 *
      (candidate.residual.eval point * candidate.residual.eval point * (3 + candidate.residual.eval point)) =
        candidate.residual.eval point ^ 2 * (3 + candidate.residual.eval point) * InverseRootPolynomial.half ^ 2).trans
          identity.symm
  bounded := fun point inside => by
    have evaluation : ((candidate.residual * candidate.residual * (DensePolynomial.constant 3 +
      candidate.residual)).scale
        (InverseRootPolynomial.half ^ 2)).eval point = Purelib.Riemann.Normalization.InverseRootPolynomial.residualStep
          (candidate.residual.eval point) := by
      simp only [DensePolynomial.eval_scale, DensePolynomial.eval_mul, DensePolynomial.eval_add,
        DensePolynomial.eval_constant, Purelib.Riemann.Normalization.InverseRootPolynomial.residualStep]
      ring1
    rw [evaluation]
    exact (residual_step_bound (candidate.bounded point
      inside) small).trans paid

/-- Perform seven retained polynomial Newton corrections to reach residual bound at most one over 256.

The resulting model keeps the exact original seed and pointwise seven-step specification. -/
@[expose] def bootstrap (polynomial : Polynomial) (box :
  Box) (seed :
  Gaussian)
    (bounded : ∀ point, box.Contains point → Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * seed
      ^ 2) ≤ 2 / 3) :
    { model : InverseRootPolynomial.Model polynomial box // (∀ point, model.value.eval point =
      InverseModelRootSamples.refineValue (polynomial.eval point) seed 7) ∧
      model.bound ≤ 1 / 256 } :=
  let first := step
    (initial polynomial box seed bounded) (by decide) (3 /
    5) (by decide +kernel)
  let second := step first (by decide) (1 / 2) (by decide +kernel)
  let third := step second (by decide) (1 / 3) (by decide +kernel)
  let fourth := step third (by decide) (1 / 6) (by decide +kernel)
  let fifth := step fourth (by decide) (1 / 16) (by decide +kernel)
  let sixth := step fifth (by decide) (1 / 64) (by decide +kernel)
  let seventh := step sixth (by decide +kernel) (1 / 256)
    (by decide +kernel)
  ⟨⟨seventh.value, seventh.residual, seventh.residual_eq, 1 / 256, by decide +kernel,
    by decide +kernel, fun point inside => by
      have scalar := seventh.bounded point inside
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar⟩, seventh.value_eq, le_rfl⟩

variable {genus : Nat} {curve : HyperellipticCurve genus}

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
/-- A coordinate in a symmetric rational interval has square bounded by the radius squared. -/
private theorem square_bound {radius value : Coordinate}
  (bounds : -radius ≤ value ∧ value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  have estimate := Rational.Box.sq_le_endpoint_max bounds.1 bounds.2
  simpa only [show (-radius) ^ 2 = radius ^ 2 by ring1, Fraction.Order.Basic.max_self] using estimate

/-- Every point of the reciprocal inner box satisfies the original radius-weighted squared-norm bound of one half. -/
private theorem inner_disk_half {point : Gaussian} (inside
  : (ReciprocalExteriorCollar.innerBox curve).Contains point) :
    radius curve ^ 2 * Data.Gaussian.Norm.Basic.normSq point ≤ 1 / 2 := by
  have upper : Data.Gaussian.Norm.Basic.normSq point ≤ 2 * ReciprocalExteriorCollar.innerRadius curve ^ 2 :=
    (add_le_add (square_bound ⟨inside.1, inside.2.1⟩)
      (square_bound ⟨inside.2.2.1,
      inside.2.2.2⟩)).trans_eq (by ring1)
  calc
    _ ≤ radius curve ^ 2 * (2 * ReciprocalExteriorCollar.innerRadius curve ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct upper (ReciprocalExteriorCollar.radius_square_positive
        curve).le
    _ = 2 * (radius curve ^ 2 * ReciprocalExteriorCollar.innerRadius curve ^ 2) := by ring1
    _ = _ := by rw [ReciprocalExteriorCollar.innerRadius_identity]; decide

/-- The reversed-polynomial tail in the reciprocal inner box has squared norm at most one eighth of the original
leading-coefficient squared norm. -/
theorem tail_bound {point : Gaussian} (inside :
  (ReciprocalExteriorCollar.innerBox curve).Contains point) :
    8 * Data.Gaussian.Norm.Basic.normSq ((Reciprocal.reversed curve.polynomial).eval point -
      curve.polynomial.leadingCoeff) ≤ Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff := by
  have tail := Reciprocal.Bounds.tail_bound curve.polynomial (BranchIsolation.degreePositive curve) point
    (Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.innerBox_inDisk curve inside))
  have weight := Reciprocal.Bounds.four_weight_le curve.polynomial curve.nonzero
  calc
    _ ≤ 8 * (RootRadius.denseLowerCoefficientWeight curve.polynomial * Data.Gaussian.Norm.Basic.normSq point)
      :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tail (by decide)
    _ = 2 * (4 * RootRadius.denseLowerCoefficientWeight curve.polynomial) * Data.Gaussian.Norm.Basic.normSq
      point := by
      ring1
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * radius curve ^ 2) *
      Data.Gaussian.Norm.Basic.normSq point :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weight (by decide))
          (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ = 2 * Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * (radius curve ^ 2 *
      Data.Gaussian.Norm.Basic.normSq point) := by
      ring1
    _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * (1 / 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (inner_disk_half inside)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    _ = _ := by
      rw [show 2 * Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * (1 / 2) =
        Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * (2 * (1 / 2)) by ring1,
        show (2 : Coordinate) * (1 / 2) = 1 by decide,
          _root_.mul_one]

end

/-- The retained leading-coefficient inverse-root seed has residual squared norm at most two thirds throughout the
reciprocal inner box. -/
public theorem initial_bound (seed : OwnerSeededInverseRoot.Seed curve.polynomial.leadingCoeff) {point :
  Gaussian}
    (inside : (ReciprocalExteriorCollar.innerBox curve).Contains point) :
    Data.Gaussian.Norm.Basic.normSq (1 - (Reciprocal.reversed curve.polynomial).eval point * seed.value ^ 2) ≤
      2 / 3 := by
  have seedScalar := seed.residual_small
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at seedScalar
  have normalized : Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff *
    Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 ≤ 65 / 32 := by
    calc
      _ = Data.Gaussian.Norm.Basic.normSq (1 - (1 - curve.polynomial.leadingCoeff * seed.value ^ 2)) := by
        rw [show 1 - (1 - curve.polynomial.leadingCoeff * seed.value ^ 2) = curve.polynomial.leadingCoeff * seed.value ^
          2 by ring1,
          Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
      _ ≤ 2 * (1 + 1 / 64) := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (by
            rw [Data.Gaussian.Norm.Basic.normSq_one]) seedScalar) (by decide))
      _ = _ := by decide +kernel
  have perturbation : Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - (Reciprocal.reversed
    curve.polynomial).eval point) * seed.value ^ 2) ≤ 65 / 256 := by
    have scaled : 8 * Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - (Reciprocal.reversed
      curve.polynomial).eval point) * seed.value ^ 2) ≤ 65 / 32 := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow, show curve.polynomial.leadingCoeff -
        (Reciprocal.reversed curve.polynomial).eval point =
        -((Reciprocal.reversed curve.polynomial).eval point - curve.polynomial.leadingCoeff) by ring1,
          Data.Gaussian.Norm.Basic.normSq_neg]
      calc
        _ = (8 * Data.Gaussian.Norm.Basic.normSq ((Reciprocal.reversed curve.polynomial).eval point -
          curve.polynomial.leadingCoeff)) * Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 := by
          ring1
        _ ≤ Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff *
          Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (tail_bound inside)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ ≤ _ := normalized
    have divided := (Fraction.Order.Field.le_div_iff_pos (by
        decide : (0 : Coordinate) < 8)).mpr
      ((show Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - (Reciprocal.reversed
        curve.polynomial).eval point) * seed.value ^ 2) * 8 =
        8 * Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - (Reciprocal.reversed
          curve.polynomial).eval point) * seed.value ^ 2) by ring1).trans_le scaled)
    exact divided.trans (by decide +kernel)
  rw [show 1 - (Reciprocal.reversed curve.polynomial).eval point * seed.value ^ 2 =
    (1 - curve.polynomial.leadingCoeff * seed.value ^ 2) +
      (curve.polynomial.leadingCoeff - (Reciprocal.reversed curve.polynomial).eval point) * seed.value ^ 2 by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add seedScalar perturbation) (by decide)).trans (by decide +kernel))

set_option genInjectivity false in
/-- A retained regular inverse-root model across the original reciprocal inner box.

The reversed polynomial, leading-coefficient owner, seeded seven-step model and clearance retain their exact original
specifications. -/
structure Data (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (collar : ReciprocalExteriorCollar.Data curve)
  where
  /-- The cached original reversed curve polynomial. -/ polynomial :
    Polynomial
  /-- The cached polynomial is exactly the reversal of the original curve polynomial. -/ polynomial_eq : polynomial =
    Reciprocal.reversed curve.polynomial
  /-- The retained square-root owner of the original leading coefficient. -/ owner : SquareRootContinuationChain.Owner
    curve.polynomial.leadingCoeff
  /-- The retained inverse-root seed for the original leading coefficient. -/ seed : OwnerSeededInverseRoot.Seed
    curve.polynomial.leadingCoeff
  /-- The seed retains exactly the displayed original square-root owner. -/ seed_owner : seed.owner = owner
  /-- The cached reversed polynomial has uniform positive clearance on the original collar box. -/ clearance :
    Region.RegionClearance polynomial collar.box
  /-- The retained clearance bound is exactly the original collar radicand bound. -/ clearance_bound : clearance.bound =
    collar.radicandBound
  /-- The cached polynomial inverse-root model on the original collar box. -/ model : InverseRootPolynomial.Model
    polynomial collar.box
  /-- Every cached model value equals seven Newton refinements from the retained original seed. -/ model_eq : ∀ point,
    model.value.eval point = InverseModelRootSamples.refineValue (polynomial.eval point) seed.value 7
  /-- The retained model residual bound is at most one over 256. -/ model_small : model.bound ≤ 1 / 256

constructive_injectivity Data

/-- Build the reciprocal inner-box model from the supplied original leading-coefficient seed.

The original owner, reversed polynomial, box clearance and seven-step model are cached with exact specifications. -/
@[expose] def Data.ofSeed (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (collar : ReciprocalExteriorCollar.Data
  curve)
    (seed : OwnerSeededInverseRoot.Seed curve.polynomial.leadingCoeff) :
      Data curve collar :=
  let polynomial := Reciprocal.reversed curve.polynomial
  let clearance : Region.RegionClearance polynomial collar.box :=
    { bound := collar.radicandBound
      positive := collar.radicandBound_positive
      lower := fun point inside => by
        have lower := Reciprocal.Bounds.disk_lower curve.polynomial (BranchIsolation.degreePositive curve) point
          (ReciprocalExteriorCollar.innerBox_inDisk curve (collar.box_eq ▸ inside))
        rw [collar.radicandBound_eq, ReciprocalExteriorCollar.radicandLower]
        exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (ReciprocalExteriorCollar.coordinateLower_le_one curve)
          (Fraction.Order.Field.div_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide))).trans
            (by simpa only [_root_.mul_one] using lower) }
  let built := bootstrap polynomial collar.box seed.value
    (fun _ inside =>
    initial_bound seed (collar.box_eq ▸ inside))
  ⟨polynomial, rfl, seed.owner, seed, rfl, clearance, rfl, built.val, built.property.1, built.property.2⟩

/-- Choose the requested leading-coefficient sheet once and build its retained reciprocal inner-box inverse-root model.
-/
@[expose] def Data.build (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (collar : ReciprocalExteriorCollar.Data
  curve) (sheet : Fin 2) : Data curve collar :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data.ofSeed curve collar (Seed.ofOwner
    (Owner.independent
    (DensePolynomial.leadingCoeff_ne_zero curve.nonzero) sheet))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
