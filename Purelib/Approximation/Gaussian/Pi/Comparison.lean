module

public import Purelib.Approximation.Gaussian.Pi.Integral
public import Purelib.Approximation.Gaussian.Pi.Polygon
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
public import Purelib.Data.Rat.Bounds.Abs
public import Purelib.Data.Rat.Bounds.Square
public import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Finite comparison of the two pi constructions

The integral and polygon samplers retain independent original states. A
finite square-radius selection divides the available absolute error between
the actual integral frontier width and the polygon endpoint mesh width.
-/

namespace Purelib.Approximation.Gaussian.Pi.Comparison

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian

/-- Uniformly compare the original polygon and integral names.

Each side starts at its supplied sampling floor. The returned indices are
selected with the same positive squared half-radius budget, and every later
pair pays the actual endpoint-mesh and retained integral-frontier widths. -/
@[expose] public def polygon_equivalent_integral :
    Equivalence.NamedEquivalent Polygon.named.name Integral.named.name where
  compare leftStart rightStart target positive := by
    let radius := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius target
    have radiusPos : 0 < radius := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive target
    have radiusSq : radius ^ 2 < target := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt positive
    let half := radius / 2
    have halfPos : 0 < half := Field.div_pos_direct radiusPos (by decide)
    let budget := half ^ 2
    have budgetPos : 0 < budget := Arithmetic.pow_pos_direct halfPos 2
    let leftIndex := Geometric.Search.firstQuarterBelow 1 leftStart budget
    let rightIndex := Geometric.Search.firstQuarterBelow 1 rightStart budget
    have leftAccurate : Geometric.Basic.quarterRadius 1 leftIndex < budget :=
      Geometric.Search.firstQuarterBelow_accurate 1 (by decide) leftStart budget budgetPos
    have rightAccurate : Geometric.Basic.quarterRadius 1 rightIndex < budget :=
      Geometric.Search.firstQuarterBelow_accurate 1 (by decide) rightStart budget budgetPos
    refine ⟨leftIndex, rightIndex,
      Geometric.Search.firstQuarterBelow_ge 1 leftStart budget,
      Geometric.Search.firstQuarterBelow_ge 1 rightStart budget, ?_⟩
    intro leftLater rightLater leftOrder rightOrder
    let stage := Equivalence.Sampling.emittedSampleIndex Polygon.approximation leftLater
    let state := Process.Sampling.stateAt Integral.process Rational.Pi.Source.boundProcess.initial rightLater
    let area := UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage)
    let width := (Rational.Pi.Source.boundProcess.bound state).width
    let mesh : Fraction.Rational := 2 / ((2 ^ stage : Nat) : Fraction.Rational)
    have polygonAccurate := Process.Sampling.stateAt_accurate Polygon.approximation.toProcess
      (show Polygon.approximation.toProcess.State from (0 : Nat)) leftLater
    change Polygon.approximation.radiusSq stage < Geometric.Basic.quarterRadius 1 leftLater at polygonAccurate
    have meshSq : mesh ^ 2 < budget := by
      change (2 / ((2 ^ stage : Nat) : Fraction.Rational)) ^ 2 < budget
      rw [Rational.Pi.Polygon.dyadic_mesh_width_sq]
      exact (polygonAccurate.trans_le
        (Geometric.Basic.quarterRadius_antitone (by decide) leftOrder)).trans leftAccurate
    have integralAccurate := Process.Sampling.stateAt_accurate Integral.process
      Rational.Pi.Source.boundProcess.initial rightLater
    change width ^ 2 < Geometric.Basic.quarterRadius 1 rightLater at integralAccurate
    have widthSq : width ^ 2 < budget :=
      (integralAccurate.trans_le
        (Geometric.Basic.quarterRadius_antitone (by decide) rightOrder)).trans rightAccurate
    have meshSmall : mesh < half := Bounds.Square.lt_of_sq_lt_sq_of_nonneg halfPos.le meshSq
    have widthSmall : width < half := Bounds.Square.lt_of_sq_lt_sq_of_nonneg halfPos.le widthSq
    have comparison := Integral.answer_endpoint_difference_le_mesh state
      (Rational.Pi.Polygon.dyadicExtra stage) area
      (Rational.Pi.Polygon.area_in_frontier (Rational.Pi.Polygon.dyadicExtra stage))
    rw [Rational.Pi.Polygon.dyadicExtra_cells] at comparison
    have sumSmall : width + mesh < radius := by
      have both := Arithmetic.add_lt_add_direct widthSmall meshSmall
      have halves : half + half = radius := by
        change radius / 2 + radius / 2 = radius
        calc
          _ = (radius / 2) * 2 := by ring1
          _ = radius := Fraction.Field.div_mul_cancel_of_ne radius 2 (by decide)
      rw [halves] at both
      exact both
    have absolute : Fraction.abs (Integral.answer state - area) < radius := comparison.trans_lt sumSmall
    have squared := Fraction.Order.Square.square_lt_square_of_nonneg_of_lt
      (Arithmetic.abs_nonneg_direct (Integral.answer state - area)) absolute
    rw [Bounds.Abs.abs_sq_direct] at squared
    change Norm.Basic.normSq
      ((Name.Sampling.approximation Polygon.named.name).sample leftLater -
        (Name.Sampling.approximation Integral.named.name).sample rightLater) < target
    rw [show Polygon.named.name = Polygon.approximation.toNamed from rfl,
      Equivalence.Sampling.emittedSample_eq]
    change Norm.Basic.normSq (Polygon.sample stage -
      (Name.Sampling.approximation Integral.named.name).sample rightLater) < target
    rw [Polygon.sample_eq_area, Integral.sample_eq,
      RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint,
      show (area - Integral.answer state) ^ 2 = (Integral.answer state - area) ^ 2 by ring1]
    exact squared.trans radiusSq

/-- The pi bridge returns the two stages selected for its actual half-radius budget.

Both searches use the same dyadic radius and retain their independent supplied
starts. This is a readback of the existing comparison, not another search used
to construct its certificate. -/
public theorem polygon_equivalent_integral_indices (leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    let budget := (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius target / 2) ^ 2
    (polygon_equivalent_integral.compare leftStart rightStart target positive).leftIndex =
        Geometric.Search.firstQuarterBelow 1 leftStart budget ∧
      (polygon_equivalent_integral.compare leftStart rightStart target positive).rightIndex =
        Geometric.Search.firstQuarterBelow 1 rightStart budget := ⟨rfl, rfl⟩

end Purelib.Approximation.Gaussian.Pi.Comparison
