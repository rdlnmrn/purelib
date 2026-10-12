module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Exponential.Cell.Allowance
public import Purelib.Integration.Exponential.Cell.Observation
import Purelib.Integration.Exponential.Polynomial.Source
public import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Child
public import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Partition.Interval
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Retained finite exponential selection and observations

The original ordered geometry, positive-stride requests and polynomial depth
remain attached to their cached values and exact scalar readback certificates.
-/

public section
namespace Purelib.Integration.Exponential.Path

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial

/-- Build observed exponential cells from the exact ordered child restrictions and their retained interval-validity
witnesses.

The same extra observation depth is used for each original child, while every polynomial restriction and interval owner
is preserved. -/
@[expose] def cells {depth : Nat} (extraDepth : Nat) : (children : List (Polynomial.Gaussian.Partition.Child
  (Polynomial.Source.source depth))) →
    (∀ child ∈ children, child.interval.Valid) → List Gaussian.Cell.Basic.CellModel
  | [], _ => []
  | child :: tail, valid =>
      Cell.Observation.cell child (valid child List.mem_cons_self) extraDepth ::
        Purelib.Integration.Exponential.Path.cells extraDepth tail (fun other member => valid other
          (List.mem_cons_of_mem child member))

/-- The observed exponential cell list has the original retained child count.

Each retained source child contributes one observed cell, and the unchanged tail contributes its original finite count.
-/
theorem cells_length {depth : Nat} (extraDepth : Nat) :
    ∀ (children : List (Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))) (valid : ∀ child ∈
      children,
      child.interval.Valid),
      (Path.cells extraDepth children valid).length = children.length
  | [], _ => rfl
  | child :: tail, valid => by
      change (Path.cells extraDepth tail _).length + 1 = tail.length + 1
      rw [Purelib.Integration.Exponential.Path.cells_length extraDepth tail]

/-- The observed cell path's integral sample is the exact sum of the original retained child samples.

The head observation cell reads the same retained child sample; ordered tail recursion preserves the rest of the exact
sample sum. -/
theorem cells_integralSample {depth : Nat} (extraDepth : Nat) :
    ∀ (children : List (Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))) (valid : ∀ child ∈
      children,
      child.interval.Valid),
      (⟨Path.cells extraDepth children valid⟩ : Gaussian.Path.Basic.PathModel).integralSample =
        Gaussian.Partition.Child.childSum children
  | [], _ => rfl
  | child :: tail, valid => by
      change (Cell.Observation.cell child (valid child List.mem_cons_self) extraDepth).integralSample +
        (⟨Path.cells extraDepth tail _⟩ : Gaussian.Path.Basic.PathModel).integralSample = child.sample +
          Gaussian.Partition.Child.childSum tail
      rw [Cell.Observation.cell_sample, Purelib.Integration.Exponential.Path.cells_integralSample extraDepth tail]

/-- Total weighted allowance is the original interval weight sum times the polynomial-depth quarter radius.

Each observed child retains its squared interval displacement and the same polynomial-depth quarter radius. Their
original ordered finite sum distributes that common scalar factor. -/
theorem cells_totalAllowance {depth : Nat} (extraDepth : Nat) :
    ∀ (children : List (Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))) (valid : ∀ child ∈
      children,
      child.interval.Valid),
      (⟨Path.cells extraDepth children valid⟩ : Gaussian.Path.Basic.PathModel).totalWeightedAllowance =
        QuadraticWeight.weightSum (children.map Polynomial.Gaussian.Partition.Child.interval) *
          Geometric.Basic.quarterRadius
          10 depth
  | [], _ => by
      change 0 = 0 * Geometric.Basic.quarterRadius 10 depth
      rw [Fraction.Field.zero_mul_direct]
  | child :: tail, valid => by
      change (Cell.Observation.cell child (valid child List.mem_cons_self) extraDepth).weightedAllowance +
        (⟨Path.cells extraDepth tail _⟩ : Gaussian.Path.Basic.PathModel).totalWeightedAllowance =
          (QuadraticWeight.intervalWeight child.interval + QuadraticWeight.weightSum (tail.map
            Polynomial.Gaussian.Partition.Child.interval)) * Geometric.Basic.quarterRadius 10 depth
      rw [Cell.Allowance.cell_weightedAllowance, Purelib.Integration.Exponential.Path.cells_totalAllowance extraDepth
        tail]
      ring1

/-- Every cell in the original constructed exponential path has exactly two endpoint observations.

Every retained head cell stores the two endpoint observations, and the same property is established recursively for its
unchanged tail. -/
theorem cells_observations {depth : Nat} (extraDepth : Nat) :
    ∀ (children : List (Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))) (valid : ∀ child ∈
      children,
      child.interval.Valid),
      ∀ model ∈ Path.cells extraDepth children valid, model.observations.length = 2
  | [], _, _, member => by nomatch member
  | child :: tail, valid, model, member => by
      rcases Membership.mem_cons.mp member with atHead | inTail
      · subst model
        rfl
      · exact Purelib.Integration.Exponential.Path.cells_observations extraDepth tail _ model inTail

/-- Read the retained compiled exponential partition as an observed polynomial path at the supplied extra observation
depth.

The observed cells consume the exact cached children and their retained interval-validity witnesses; the original order
and extra observation depth stay fixed. -/
@[expose] def path {depth : Nat} (compiled : Gaussian.Partition.Segment.CompiledSegment (Polynomial.Source.source
  depth)) (extraDepth : Nat) : Gaussian.Path.Basic.PathModel :=
  ⟨Path.cells extraDepth compiled.children compiled.children_valid⟩

/-- The observed exponential path's sample equals the exact retained compiled sample.

The ordered observed cells read back to the same cached child samples whose sum defines the retained compilation sample.
-/
theorem path_sample {depth : Nat} (compiled : Gaussian.Partition.Segment.CompiledSegment (Polynomial.Source.source
  depth)) (extraDepth : Nat) :
    (Path.path compiled extraDepth).integralSample = compiled.sample := by
  rw [Path.path, Path.cells_integralSample, ← compiled.sample_eq]

/-- The observed path's aggregate allowance is the original partition amplification times its polynomial-depth quarter
radius.

The original child count and interval weights recover the exact partition amplification; the same depth-dependent radius
multiplies that retained factor. -/
theorem path_allowance {depth : Nat} (compiled : Gaussian.Partition.Segment.CompiledSegment (Polynomial.Source.source
  depth)) (extraDepth : Nat) :
    (Path.path compiled extraDepth).aggregateAllowance = QuadraticWeight.amplification compiled.partition *
      Geometric.Basic.quarterRadius 10 depth := by
  change ((Path.cells extraDepth compiled.children compiled.children_valid).length : Fraction.Rational) *
    (Path.path compiled extraDepth).totalWeightedAllowance = _
  rw [Path.cells_length]
  change (compiled.children.length : Fraction.Rational) *
    (⟨Path.cells extraDepth compiled.children compiled.children_valid⟩ :
      Gaussian.Path.Basic.PathModel).totalWeightedAllowance = _
  rw [Path.cells_totalAllowance, compiled.children_intervals]
  have lengths := congrArg List.length compiled.children_intervals
  rw [Map.length_map] at lengths
  rw [lengths]
  unfold QuadraticWeight.amplification
  ring1

end Purelib.Integration.Exponential.Path
end
