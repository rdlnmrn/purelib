module

public import Purelib.Polynomial.Geometry.Grid.AxisWalks.Steps
public import Purelib.Integration.Partition.Interval.Chain
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-! # Original axis steps in their retained unit parameter

The same oriented endpoint pairs determine a finite parameter chain.
Nonstationary normalization uses the original endpoint difference;
stationary walks retain an empty inner chain without creating a step.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.AxisWalks.Walk

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Partition (Interval)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

universe u

variable {Alpha : Type u} {key : Alpha → Rational} {intervals : List (ClearGrid.Interval key)}
    {first last : Rational} (walk : Walk intervals first last)

/-- Normalize a scalar point using this same retained walk's original oriented endpoints. -/
@[expose] def parameter (_walk : Walk intervals first last) (value : Rational) : Rational :=
  (value - first) / (last - first)

/-- Distinct original endpoints give a nonzero oriented width. -/
private theorem width_nonzero {first last : Rational} (different : first ≠ last) : last - first ≠ 0 := by
  intro equal
  apply different
  calc
    first = last - (last - first) := by ring1
    _ = last := by rewrite [equal]; ring1

/-- The original starting coordinate has parameter zero, including a stationary walk. -/
theorem parameter_first : walk.parameter first = 0 := by
  change (first - first) / (last - first) = 0
  rewrite [show first - first = 0 by ring1]
  exact Field.zero_div_direct _

/-- The original nonstationary finishing coordinate has parameter one. -/
theorem parameter_last (different : first ≠ last) : walk.parameter last = 1 := by
  change (last - first) * (last - first)⁻¹ = 1
  exact Purelib.Data.Rat.Fraction.Field.mul_inv_cancel _ (width_nonzero different)

/-- Interpolating the same original endpoints recovers the supplied scalar coordinate. -/
theorem parameter_coordinate (different : first ≠ last) (value : Rational) :
    first + walk.parameter value * (last - first) = value := by
  change first + ((value - first) / (last - first)) * (last - first) = value
  rewrite [Field.div_mul_cancel_of_ne _ _ (width_nonzero different)]
  ring1

/-- Coordinates between the original endpoints have unit parameters in either retained traversal direction. -/
theorem parameter_inside (different : first ≠ last) {value : Rational}
    (between : (first ≤ value ∧ value ≤ last) ∨ (last ≤ value ∧ value ≤ first)) :
    0 ≤ walk.parameter value ∧ walk.parameter value ≤ 1 := by
  cases walk with
  | forward path =>
      have ordered : first < last :=
        ⟨path.ordered, fun reverse => different (Order.Basic.le_antisymm _ _ path.ordered reverse)⟩
      have inside : first ≤ value ∧ value ≤ last := between.elim (fun kept => kept)
        (fun kept => ⟨path.ordered.trans kept.1, kept.2.trans path.ordered⟩)
      exact Order.Field.fraction_inside ordered inside
  | backward path =>
      have ordered : last < first :=
        ⟨path.ordered, fun reverse => different (Order.Basic.le_antisymm _ _ reverse path.ordered)⟩
      have inside : last ≤ value ∧ value ≤ first := between.elim
        (fun kept => ⟨path.ordered.trans kept.1, kept.2.trans path.ordered⟩) (fun kept => kept)
      have positive := Order.Arithmetic.sub_pos_direct ordered
      have forward : 0 ≤ (first - value) / (first - last) ∧
          (first - value) / (first - last) ≤ 1 := by
        refine ⟨Order.Field.div_nonneg_direct (Order.Arithmetic.sub_nonneg_direct inside.2) positive.le, ?_⟩
        apply (Order.Field.div_le_iff_pos positive).mpr
        exact (Order.Arithmetic.sub_le_sub_left_direct inside.1 first).trans_eq (by ring1)
      have same : (value - first) / (last - first) = (first - value) / (first - last) :=
        Field.div_eq_div_of_cross_mul (width_nonzero different) (width_nonzero different.symm) (by ring1)
      exact Eq.mpr (congrArg (fun fraction : Rational => 0 ≤ fraction ∧ fraction ≤ 1) same) forward

/-- Both endpoints of each same original step have unit parameters, retaining its source occurrence. -/
theorem step_parameters_inside (different : first ≠ last) {step : Rational × Rational}
    (present : step ∈ walk.steps) :
    (0 ≤ walk.parameter step.1 ∧ walk.parameter step.1 ≤ 1) ∧
      (0 ≤ walk.parameter step.2 ∧ walk.parameter step.2 ≤ 1) := by
  rcases walk.steps_bounds present with forward | backward
  · exact ⟨walk.parameter_inside different (Or.inl ⟨forward.1, forward.2.1.le.trans forward.2.2⟩),
      walk.parameter_inside different (Or.inl ⟨forward.1.trans forward.2.1.le, forward.2.2⟩)⟩
  · exact ⟨walk.parameter_inside different (Or.inr ⟨backward.1.trans backward.2.1.le, backward.2.2⟩),
      walk.parameter_inside different (Or.inr ⟨backward.1, backward.2.1.le.trans backward.2.2⟩)⟩

/-- Read one interval per same original oriented step, preserving order and repeated vertices. -/
@[expose] def parameters : List Interval :=
  walk.steps.map (fun step => ⟨walk.parameter step.1, walk.parameter step.2⟩)

/-- Mapping an original exact endpoint path gives its same ordered parameter interval chain. -/
private theorem mapped_chain (read : Rational → Rational) {steps : List (Rational × Rational)}
    {first last : Rational} (path : PathEndpoints Prod.fst Prod.snd steps first last) :
    Interval.Chain (read first) (read last) (steps.map (fun step => ⟨read step.1, read step.2⟩)) := by
  induction path with
  | nil point => exact .nil (read point)
  | cons _ previous => exact .cons previous

/-- The same normalized nonstationary step list chains exactly from zero to one. -/
theorem parameters_chain (different : first ≠ last) : Interval.Chain 0 1 walk.parameters :=
  Eq.mp (congrArg₂ (fun start finish => Interval.Chain start finish walk.parameters)
    walk.parameter_first (walk.parameter_last different)) (mapped_chain walk.parameter walk.steps_path)

/-- Equal endpoints leave the same parameter list empty, preserving any enclosing outer role. -/
theorem parameters_nil (same : first = last) : walk.parameters = [] :=
  congrArg (fun steps => steps.map (fun step =>
    (⟨walk.parameter step.1, walk.parameter step.2⟩ : Interval))) (walk.steps_nil_of_eq same)

end Purelib.Polynomial.Geometry.Grid.AxisWalks.Walk

end
