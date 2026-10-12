module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Tactic.Ring

public section

/-!
# Requested inverse models on retained root owners

A single residual state of the continued owner supplies a cached root reading.
Its comparison with the supplied equivalent owner and the polynomial Newton
bound give independent floors for all later model and canonical root readings.
No root is reselected and no refined polynomial is needed to choose the floors.
-/

namespace Purelib.Riemann.Normalization.ContinuedInverseRootRequests

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Comparison)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {polynomial : Polynomial} {count : Nat}
  {patch : ContinuedNeighborhood polynomial count} {point : Gaussian}

open Purelib.Data in
/-- Transport a root-distance estimate through inversion using positive squared-norm lower bounds.

A strict distance bound scaled by the product of the two lower bounds yields the requested strict inverse-distance
bound. -/
private theorem inverse_difference {left right : Gaussian} {leftLower rightLower target : Coordinate}
    (leftPositive : 0 < leftLower) (rightPositive : 0 < rightLower)
    (leftBound : leftLower ≤ normSq left) (rightBound : rightLower ≤ normSq right)
    (close : normSq (right - left) < target * (leftLower * rightLower)) :
    normSq (inv left - inv right) < target := by
  have leftNonzero : left ≠ 0 := by
    intro zero
    exact (leftPositive.trans_le leftBound).ne' (zero ▸ Gaussian.Basic.Canonical.normSq_zero)
  have rightNonzero : right ≠ 0 := by
    intro zero
    exact (rightPositive.trans_le rightBound).ne' (zero ▸ Gaussian.Basic.Canonical.normSq_zero)
  have identity : (inv left - inv right) * (left * right) = right - left := by
    calc
      _ = (inv left * left) * right - (inv right * right) * left := by ring1
      _ = _ := by
        have leftCancel : inv left * left = 1 := by
          with_unfolding_all exact Gaussian.Basic.Canonical.inv_mul_cancel left leftNonzero
        have rightCancel : inv right * right = 1 := by
          with_unfolding_all exact Gaussian.Basic.Canonical.inv_mul_cancel right rightNonzero
        rw [leftCancel, rightCancel, Gaussian.Basic.one_mul, Gaussian.Basic.one_mul]
  apply Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := leftLower * rightLower) _
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct leftPositive rightPositive)
  calc
    _ ≤ normSq (inv left - inv right) * (normSq left * normSq right) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct leftBound rightBound rightPositive.le
          (Gaussian.Basic.Canonical.normSq_nonneg _))
        (Gaussian.Basic.Canonical.normSq_nonneg _)
    _ = normSq (right - left) := by
      rw [← Gaussian.Basic.Canonical.normSq_mul, ← Gaussian.Basic.Canonical.normSq_mul, identity]
    _ < _ := close

set_option genInjectivity false in
open Purelib.Approximation in
/-- A finite comparison to one cached witness of a retained process state.

The comparison preserves both requested floors; the witness carries its exact sample equation and possibility
certificate at the original state. -/
structure RebasedReading (value : Gaussian.Name.Coherent.CoherentNamed)
    (state : value.name.process.State) (other : Gaussian.Name.Basic.Named)
    (target : Coordinate) (floor : Nat) where
  /-- The retained comparison of the other owner and the rebased process at the requested floors. -/ comparison :
    Gaussian.Equivalence.Comparison (Gaussian.Name.Sampling.approximation other)
    (Gaussian.Name.Sampling.approximation { process := value.name.process, state := state })
    floor floor target
  /-- The cached witness in the retained process state. -/ reading : Gaussian
  /-- The witness equals the selected process sample at the comparison's right index. -/ reading_eq : reading =
    Gaussian.Process.Sampling.witnessAt value.name.process state comparison.rightIndex
  /-- The cached reading is possible in the retained state. -/ possible : value.name.process.Possible state reading

constructive_injectivity RebasedReading

namespace RebasedReading

open Purelib.Approximation in
/-- Compare an equivalent named process with a retained state and cache its selected witness.

The target is positive and both comparison indices respect the same supplied floor. -/
@[expose] def build (value : Gaussian.Name.Coherent.CoherentNamed) (state : value.name.process.State)
    (other : Gaussian.Name.Basic.Named) (equivalent : Gaussian.Equivalence.NamedEquivalent other value.name)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) : RebasedReading value state other target floor :=
  let comparison := (equivalent.trans (value.rebaseEquivalent state)).compare floor floor target positive
  ⟨comparison, Gaussian.Process.Sampling.witnessAt value.name.process state comparison.rightIndex, rfl,
    Gaussian.Process.Sampling.witnessAt_possible_start _ state comparison.rightIndex⟩

open Purelib.Approximation in
open Purelib.Data in
/-- Every sufficiently late sample of the other owner is within target of the cached reading. -/
theorem close {value : Gaussian.Name.Coherent.CoherentNamed} {state : value.name.process.State}
    {other : Gaussian.Name.Basic.Named} {target : Coordinate} {floor : Nat}
    (observation : RebasedReading value state other target floor) {index : Nat}
    (later : observation.comparison.leftIndex ≤ index) :
    normSq ((Gaussian.Name.Sampling.approximation other).sample index - observation.reading) < target := by
  rw [observation.reading_eq]
  simpa only [Gaussian.Name.Sampling.approximation, Gaussian.Norm.Basic.normSq_eq_canonical] using
    observation.comparison.close later (Nat.le_refl _)

end RebasedReading

set_option genInjectivity false in
open Purelib.Riemann in
open Purelib.Approximation in
/-- A cached residual attempt with independent polynomial and owner-reading floors.

The record retains its positive target, domain evidence, exact scalar budget, residual state and rebased observation,
together with the geometric search result for the polynomial index. -/
structure InverseRequestData (value : Gaussian.Name.Coherent.CoherentNamed)
    (residual : (error : Coordinate) → 0 < error → value.name.process.State)
    (rootLower : Coordinate) {parameter : Gaussian} (owner : RootContinuation.CertifiedSquareRoot.Certificate parameter)
    (domain : Prop) (target : Coordinate) (floor : Nat) where
  /-- The requested squared inverse error is strictly positive. -/ positive : 0 < target
  /-- The requested point satisfies the retained domain condition. -/ inside : domain
  /-- The cached quarter-target comparison budget. -/ budget : Coordinate
  /-- The comparison budget is exactly one quarter of the target. -/ budget_eq : budget = target / 4
  /-- The cached numerator-error target before division by the root lower bound. -/ numeratorTarget : Coordinate
  /-- The numerator target is half the budget times the retained root lower bound. -/ numeratorTarget_eq :
    numeratorTarget = budget * rootLower / 2
  /-- The cached relative root-residual request. -/ error : Coordinate
  /-- The residual request is the minimum of one divided by 4096 and one sixteenth of the numerator target. -/ error_eq
    : error = min (1 / 4096) (numeratorTarget / 16)
  /-- The retained residual request is strictly positive. -/ error_positive : 0 < error
  /-- The retained process state produced by the residual request. -/ state : value.name.process.State
  /-- The state is exactly the result of the supplied residual procedure at the cached request. -/ state_eq : state =
    residual error error_positive
  /-- The cached root witness and comparison scaled by both positive root lower bounds. -/ observation : RebasedReading
    value state owner.value.name
    (budget * (rootLower * owner.apart.certificate.lowerSq)) floor
  /-- The retained polynomial-refinement floor. -/ index : Nat
  /-- The index is the first geometric-quarter search result at or beyond the requested floor. -/ index_eq : index =
    Rational.Geometric.Search.firstQuarterBelow (1 / 256) floor numeratorTarget

constructive_injectivity InverseRequestData

open Purelib.Riemann in
/-- The exact inverse-request interface for a continued point and a specified equivalent root owner. -/
abbrev InverseRequest (sample : Point patch point)
    (owner : RootContinuation.CertifiedSquareRoot.Certificate (polynomial.eval point)) (target : Coordinate) (floor :
      Nat) :=
  InverseRequestData sample.certificate.value sample.residualState patch.rootLower owner
    (patch.box.Contains point) target floor

namespace InverseRequest

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Choose and retain the residual reading and independent inverse-model refinement floor.

The point lies inside the continuation patch and the supplied root owner is operationally equivalent. Scalar budgets and
geometric search use the same positive target and requested floor. -/
@[expose] def build (sample : Point patch point) (inside : patch.box.Contains point)
    (owner : RootContinuation.CertifiedSquareRoot.Certificate (polynomial.eval point))
    (equivalent : Gaussian.Equivalence.NamedEquivalent owner.value.name sample.certificate.value.name)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) : InverseRequest sample owner target floor :=
  let budget := target / 4
  have budgetPositive : 0 < budget := Rat.Fraction.Order.Field.div_pos_direct positive (by decide)
  let numeratorTarget := budget * patch.rootLower / 2
  have numeratorPositive : 0 < numeratorTarget := Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct budgetPositive patch.rootLower_positive) (by decide)
  let error := min (1 / 4096) (numeratorTarget / 16)
  have errorPositive : 0 < error := Fraction.Order.Basic.lt_min (by decide +kernel)
    (Rat.Fraction.Order.Field.div_pos_direct numeratorPositive (by decide))
  let state := sample.residualState error errorPositive
  let observation := RebasedReading.build sample.certificate.value state owner.value.name equivalent
    (budget * (patch.rootLower * owner.apart.certificate.lowerSq))
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct budgetPositive
      (Rat.Fraction.Order.Arithmetic.mul_pos_direct patch.rootLower_positive owner.apart.certificate.positive)) floor
  ⟨positive, inside, budget, rfl, numeratorTarget, rfl, error, rfl, errorPositive, state, rfl,
    observation, Rational.Geometric.Search.firstQuarterBelow (1 / 256) floor numeratorTarget, rfl⟩

variable {sample : Point patch point} {owner : Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Certificate
  (polynomial.eval point)}
  {target : Coordinate} {floor : Nat}

open Purelib.Approximation in
/-- The retained polynomial index respects the requested floor. -/
theorem floor_le (request : InverseRequest sample owner target floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact Rational.Geometric.Search.firstQuarterBelow_ge _ _ _

section
open Purelib.Data
/-- The cached inverse-comparison budget is positive. -/
theorem budget_positive (request : InverseRequest sample owner target floor) : 0 < request.budget := by
  rw [request.budget_eq]
  exact Rat.Fraction.Order.Field.div_pos_direct request.positive (by decide)

/-- The cached numerator-error target is positive. -/
theorem numeratorTarget_positive (request : InverseRequest sample owner target floor) : 0 < request.numeratorTarget :=
  by
  rw [request.numeratorTarget_eq]
  exact Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct request.budget_positive patch.rootLower_positive) (by decide)

end

open Purelib.Approximation
open Purelib.Data
/-- Every later polynomial refinement approximates the inverse of the cached residual reading.

Its squared error is strictly below the retained quarter-target budget, using the same residual state and witness. -/
theorem reading_accurate (request : InverseRequest sample owner target floor) {index : Nat}
    (later : request.index ≤ index) :
    normSq ((patch.base.refine index).value.eval point - inv request.observation.reading) < request.budget := by
  have possible := (congrArg (fun state => sample.certificate.value.name.process.Possible
    state request.observation.reading) request.state_eq).mp request.observation.possible
  have small : request.error ≤ 1 / 4096 := by rw [request.error_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have comparison := sample.polynomial_inverse_error request.inside request.error request.error_positive small possible
    index
  have residual : Rational.Geometric.Basic.quarterRadius (1 / 256) index < request.numeratorTarget := by
    rw [request.index_eq] at later
    exact (quarterRadius_antitone (by decide +kernel) later).trans_lt
      (Rational.Geometric.Search.firstQuarterBelow_accurate _ (by decide +kernel) floor _
        request.numeratorTarget_positive)
  have allowance : 16 * request.error ≤ request.numeratorTarget := by
    have bound : request.error ≤ request.numeratorTarget / 16 := by
      rw [request.error_eq]; exact
        Fraction.Order.Basic.min_le_right _ _
    apply (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound (by
        decide : (0 : Coordinate) ≤ 16)).trans_eq
    rw [Rat.Fraction.Field.mul_comm]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  apply comparison.trans_lt
  apply (Rat.Fraction.Order.Field.div_lt_iff_pos patch.rootLower_positive).mpr
  calc
    _ < request.numeratorTarget + request.numeratorTarget :=
      (Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct residual _).trans_le
        (add_le_add le_rfl allowance)
    _ = request.budget * patch.rootLower := by
      rw [show request.numeratorTarget + request.numeratorTarget = request.numeratorTarget * 2 by ring1,
        request.numeratorTarget_eq]
      exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- Independently later model and owner readings satisfy the requested inverse-error target.

The polynomial index exceeds its retained floor and the owner sample exceeds the comparison floor; both estimates reuse
the same residual observation. -/
theorem accurate (request : InverseRequest sample owner target floor) {index rootIndex : Nat}
    (later : request.index ≤ index) (rootLater : request.observation.comparison.leftIndex ≤ rootIndex) :
    normSq ((patch.base.refine index).value.eval point -
      inv ((Gaussian.Name.Sampling.approximation owner.value.name).sample rootIndex)) < target := by
  let root := (Gaussian.Name.Sampling.approximation owner.value.name).sample rootIndex
  have close := request.observation.close rootLater
  have inverseClose := inverse_difference patch.rootLower_positive owner.apart.certificate.positive
    (sample.candidate_lower _ request.observation.possible)
    (by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using (Gaussian.Name.Apart.Sampling.sampled_lower owner.value owner.apart rootIndex)) close
  rw [show (patch.base.refine index).value.eval point - inv root =
    ((patch.base.refine index).value.eval point - inv request.observation.reading) + (inv request.observation.reading -
      inv root) by ring1]
  have triangle := Gaussian.Norm.Bounds.normSq_add_le_two
    ((patch.base.refine index).value.eval point - inv request.observation.reading)
    (inv request.observation.reading - inv root)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
  apply triangle.trans_lt
  apply (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
    (Rat.Fraction.Order.Arithmetic.add_lt_add_direct (request.reading_accurate later) inverseClose)).trans_eq
  rw [show 2 * (request.budget + request.budget) = request.budget * 4 by ring1, request.budget_eq]
  exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end InverseRequest
end Purelib.Riemann.Normalization.ContinuedInverseRootRequests
