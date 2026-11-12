module

public import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Finite payment for the original weighted physical loops

The loop words and integer coefficients are the original physical-cycle
cache. Their literal occurrence count and squared coefficient norms determine
a scalar gain before numerical edge readings are chosen.
-/

public section

namespace Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates.Data

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Algebra.FiniteSum.Rational.Order (weight_sum_nonnegative)
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_mul normSq_nonneg)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (normSq_sumFin_le_count_mul_sumFin sumFin_map)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {count size : Nat} {occurrences : List (OrientedEdge count)}
    {boundary : BoundaryCycleDecomposition occurrences}
    {generators : Fin size → OrientedEdge count} {row : Fin size → Int}
    (data : PhysicalCycleCoordinates.Data boundary generators row)

/-- The original loop occurrences and integer multiplicities determine their complete uniform error gain. -/
@[expose] def loopGain : Rational :=
  (data.rows.length : Rational) * sumFin (fun position : Fin data.rows.length =>
    normSq ((data.rows[position.val]'position.isLt).1 : Canonical))

/-- The retained occurrence count and squared coefficient norms give a nonnegative loop gain. -/
theorem loopGain_nonnegative : 0 ≤ data.loopGain :=
  Order.Arithmetic.mul_nonneg_direct
    (Cast.Order.natCast_le_direct (m := 0) (n := data.rows.length) (Nat.zero_le _))
    (weight_sum_nonnegative _ (fun _ => normSq_nonneg _))

/-- A common bound on the actual original loop words pays their complete weighted sum.

Repeated words keep separate coefficients and occurrences. No assertion that
a closed loop or its primitive increment vanishes is used.
-/
theorem loop_value_le (value : OrientedEdge count → Canonical) (bound : Rational)
    (bounded : ∀ word ∈ boundary.cycles, normSq (wordValue value word) ≤ bound) :
    normSq (gaussianSum (data.rows.map (fun entry =>
      (entry.1 : Canonical) * wordValue value entry.2))) ≤ data.loopGain * bound := by
  let reading := fun entry : Int × List (OrientedEdge count) =>
    (entry.1 : Canonical) * wordValue value entry.2
  have original := normSq_sumFin_le_count_mul_sumFin
    (fun position : Fin data.rows.length => reading (data.rows[position.val]'position.isLt))
    (fun position : Fin data.rows.length =>
      normSq ((data.rows[position.val]'position.isLt).1 : Canonical) * bound)
    (fun position => by
      let entry := data.rows[position.val]'position.isLt
      have member : entry ∈ data.rows := List.getElem_mem position.isLt
      have wordMember : entry.2 ∈ boundary.cycles := by
        have retained : entry.2 ∈ data.rows.map Prod.snd := Map.mem_map_of_mem member
        exact Eq.mp (congrArg (fun words => entry.2 ∈ words) data.words_eq) retained
      change normSq ((entry.1 : Canonical) * wordValue value entry.2) ≤ _
      rewrite [normSq_mul]
      exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (bounded entry.2 wordMember) (normSq_nonneg _))
  have same := sumFin_map data.rows reading
  have scaled := sumFin_mul_right
    (fun position : Fin data.rows.length =>
      normSq ((data.rows[position.val]'position.isLt).1 : Canonical)) bound
  have allowance : (data.rows.length : Rational) * sumFin (fun position : Fin data.rows.length =>
      normSq ((data.rows[position.val]'position.isLt).1 : Canonical) * bound) = data.loopGain * bound := by
    rewrite [scaled]
    exact (Field.mul_assoc _ _ _).symm
  exact (Eq.mp (congrArg (fun actual : Canonical => normSq actual ≤
    (data.rows.length : Rational) * sumFin (fun position : Fin data.rows.length =>
      normSq ((data.rows[position.val]'position.isLt).1 : Canonical) * bound)) same) original).trans_eq allowance

/-- Allocate half the requested whole physical-loop error using its actual finite coefficient gain. -/
@[expose] def loopTarget (target : Rational) : Rational :=
  Weighted.allowance (target / 2) data.loopGain

/-- Every positive whole-loop request gives a positive target for each retained original boundary word. -/
theorem loopTarget_positive {target : Rational} (positive : 0 < target) : 0 < data.loopTarget target :=
  Weighted.allowance_positive (Order.Field.div_pos_direct positive (by decide +kernel)) data.loopGain_nonnegative

/-- The allocated original loop estimates pay the complete weighted physical contribution strictly below the request. -/
theorem loop_requested_lt (value : OrientedEdge count → Canonical) {target : Rational}
    (positive : 0 < target)
    (bounded : ∀ word ∈ boundary.cycles, normSq (wordValue value word) ≤ data.loopTarget target) :
    normSq (gaussianSum (data.rows.map (fun entry =>
      (entry.1 : Canonical) * wordValue value entry.2))) < target := by
  have original := data.loop_value_le value (data.loopTarget target) bounded
  have paid := Weighted.mul_allowance_le
    (Order.Field.div_pos_direct positive (by decide +kernel : (0 : Rational) < 2)).le data.loopGain_nonnegative
  exact (original.trans paid).trans_lt (Order.Field.half_lt_self positive)

end Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates.Data
