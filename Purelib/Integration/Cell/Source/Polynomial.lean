module
public import Purelib.Integration.Cell.Source
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Real
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Source-frontier bounds for finite polynomial primitive increments

Each original cell range bounds the same Gaussian polynomial's real
coordinate on its rational domain. The finite primitive increment theorem
turns those bounds into weighted endpoint estimates; the exact original
partition then telescopes those estimates into one integral enclosure.
-/

public section

namespace Purelib.Integration.SourceFrontier.Polynomial

open Purelib.Data.Gaussian
open Purelib.Data.List.Rat.Linear
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration.Partition
open Purelib.Polynomial.Dense.Gaussian.Primitive

/-- The original finite lower integral is its same ordered list of weighted lower terms. -/
private theorem lower_eq_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    lowerIntegral cells = (cells.map (fun cell => cell.weight * cell.lower)).sum
  | [] => rfl
  | first :: remaining => by
      change first.weight * first.lower + lowerIntegral remaining =
        first.weight * first.lower + (remaining.map (fun cell => cell.weight * cell.lower)).sum
      rw [lower_eq_sum remaining]

/-- The original finite upper integral is its same ordered list of weighted upper terms. -/
private theorem upper_eq_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    upperIntegral cells = (cells.map (fun cell => cell.weight * cell.upper)).sum
  | [] => rfl
  | first :: remaining => by
      change first.weight * first.upper + upperIntegral remaining =
        first.weight * first.upper + (remaining.map (fun cell => cell.weight * cell.upper)).sum
      rw [upper_eq_sum remaining]

/-- Every original source cell brackets the matching finite polynomial primitive increment. -/
private theorem cell_increment {source : Fraction.Rational → Fraction.Rational}
    {coefficient : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (primitive : Certificate.DensePrimitive coefficient box) (frontier : SourceFrontier source)
    (boxInside : ∀ point, 0 ≤ point → point ≤ 1 → box.Contains (RationalEmbedding.realPoint point))
    (same : ∀ point, 0 ≤ point → point ≤ 1 →
      source point = (coefficient.eval (RationalEmbedding.realPoint point)).re)
    (cell : IntegrationCell (SourcePoint source)) (member : cell ∈ frontier.cells) :
    cell.weight * cell.lower ≤
        (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.finish)).re -
          (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.start)).re ∧
      (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.finish)).re -
          (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.start)).re ≤
        cell.weight * cell.upper := by
  have domainMember : cell.item.interval ∈ frontier.partition.intervals := by
    rw [← frontier.domains_eq]
    exact Purelib.Data.List.Map.mem_map_of_mem member
  have valid := frontier.partition.valid cell.item.interval domainMember
  let interval : Purelib.Data.Rat.Interval := ⟨cell.item.interval.start, cell.item.interval.finish, valid.2.1.le⟩
  have insideBox : ∀ point, interval.Contains point → box.Contains (RationalEmbedding.realPoint point) := by
    intro point inside
    exact boxInside point (valid.1.trans inside.1) (inside.2.trans valid.2.2)
  have range : ∀ point, interval.Contains point →
      cell.lower ≤ (coefficient.eval (RationalEmbedding.realPoint point)).re ∧
        (coefficient.eval (RationalEmbedding.realPoint point)).re ≤ cell.upper := by
    intro point inside
    have observed := frontier.source_range cell member point inside.1 inside.2
    rw [same point (valid.1.trans inside.1) (inside.2.trans valid.2.2)] at observed
    exact observed
  have lower := Segment.Real.increment_lower primitive interval insideBox 1 cell.lower (by decide)
    (fun point inside => by
      have retained := (range point inside).1
      rw [Fraction.Field.one_mul]
      exact retained) (first := cell.item.interval.finish) (last := cell.item.interval.start)
      ⟨valid.2.1.le, le_rfl⟩ ⟨le_rfl, valid.2.1.le⟩ valid.2.1.le
  have upper := Segment.Real.increment_lower primitive interval insideBox (-1) (-cell.upper) (by decide)
    (fun point inside => by
      have retained := Fraction.Order.Arithmetic.neg_le_neg_direct (range point inside).2
      have identity : (-1 : Fraction.Rational) * (coefficient.eval (RationalEmbedding.realPoint point)).re =
          -(coefficient.eval (RationalEmbedding.realPoint point)).re := by ring1
      rw [identity]
      exact retained) (first := cell.item.interval.finish) (last := cell.item.interval.start)
      ⟨valid.2.1.le, le_rfl⟩ ⟨le_rfl, valid.2.1.le⟩ valid.2.1.le
  have weight := frontier.weight_eq cell member
  have lowerIdentity : cell.lower * (cell.item.interval.finish - cell.item.interval.start) =
      cell.weight * cell.lower := by rw [weight]; unfold Partition.Interval.signedLength; ring1
  have upperIdentity : (-cell.upper) * (cell.item.interval.finish - cell.item.interval.start) =
      -(cell.weight * cell.upper) := by rw [weight]; unfold Partition.Interval.signedLength; ring1
  rw [Fraction.Field.one_mul, Fraction.Field.one_mul, lowerIdentity] at lower
  rw [upperIdentity] at upper
  have upperNeg := Fraction.Order.Arithmetic.neg_le_neg_direct upper
  have upperFinal : -(-(cell.weight * cell.upper)) = cell.weight * cell.upper := by ring1
  have incrementFinal : -((-1 : Fraction.Rational) *
      (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.finish)).re -
        (-1 : Fraction.Rational) * (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.start)).re) =
      (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.finish)).re -
        (primitive.value.eval (RationalEmbedding.realPoint cell.item.interval.start)).re := by ring1
  rw [upperFinal, incrementFinal] at upperNeg
  exact ⟨lower, upperNeg⟩

/-- A source frontier contains the exact real endpoint increment of its original finite polynomial primitive.

The source's rational readings must agree with the original coefficient
polynomial on the unit interval, and the retained primitive box must contain
those same rational points. The proof derives the integral enclosure from
cell source ranges and exact finite endpoint telescoping. -/
theorem integral_contains {source : Fraction.Rational → Fraction.Rational}
    {coefficient : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (primitive : Certificate.DensePrimitive coefficient box) (frontier : SourceFrontier source)
    (boxInside : ∀ point, 0 ≤ point → point ≤ 1 → box.Contains (RationalEmbedding.realPoint point))
    (same : ∀ point, 0 ≤ point → point ≤ 1 →
      source point = (coefficient.eval (RationalEmbedding.realPoint point)).re) :
    (integralBound frontier.cells).Contains
      ((primitive.value.eval (RationalEmbedding.realPoint 1)).re -
        (primitive.value.eval (RationalEmbedding.realPoint 0)).re) := by
  let endpoint := fun point : Fraction.Rational => (primitive.value.eval (RationalEmbedding.realPoint point)).re
  let increment := fun cell : IntegrationCell (SourcePoint source) =>
    endpoint cell.item.interval.finish - endpoint cell.item.interval.start
  have lower := sum_le (fun cell => cell.weight * cell.lower) increment frontier.cells
    (fun cell member => (cell_increment primitive frontier boxInside same cell member).1)
  have upper := sum_le increment (fun cell => cell.weight * cell.upper) frontier.cells
    (fun cell member => (cell_increment primitive frontier boxInside same cell member).2)
  have telescope := frontier.partition.chain.lengthSum_mapEndpoints endpoint
  rw [← frontier.domains_eq, Purelib.Data.List.Map.map_map] at telescope
  change Interval.lengthSum (frontier.cells.map (fun cell =>
    ⟨endpoint cell.item.interval.start, endpoint cell.item.interval.finish⟩)) = endpoint 1 - endpoint 0 at telescope
  have sumEquals : (frontier.cells.map increment).sum =
      Interval.lengthSum (frontier.cells.map (fun cell =>
        ⟨endpoint cell.item.interval.start, endpoint cell.item.interval.finish⟩)) := by
    induction frontier.cells with
    | nil => rfl
    | cons first remaining inductionHypothesis =>
        change increment first + (remaining.map increment).sum =
          (endpoint first.item.interval.finish - endpoint first.item.interval.start) + _
        rw [inductionHypothesis]
  rw [← lower_eq_sum, sumEquals, telescope] at lower
  rw [← upper_eq_sum, sumEquals, telescope] at upper
  exact ⟨lower, upper⟩

end Purelib.Integration.SourceFrontier.Polynomial

end
