module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

public section

/-!
# Aggregate total and area errors for the joined complete parent

The existing finite side budget pays the square and fourth power of the
retained cell count. No estimate depends on the additional fine-path depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedEstimates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea (SideAreaBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)

/-- The sum of the retained block-total differences equals the difference of the two concatenated path totals. -/
private theorem sum_errors (pairs : List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst).flatten -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd).flatten := by
  induction pairs with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      simp only [List.map_cons, List.flatten_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        IncrementArea.sum_append, ih]
      ring1

variable {genus count index depth readingIndex floor : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {edges : List ParameterEdge} {bank :
    Bank regular data edges} {owners :
    Owners bank}
  {bound totalTarget areaTarget : Coordinate} (budget :
    SideAreaBudget bound edges.length totalTarget
    areaTarget)
  {requests : EndpointRequests (budget.tolerance /
    4) floor owners}
  {cells : ComparedCells source capSample depth bank}
  {readings : EndpointRequests.EvaluationData
    (readingIndex := readingIndex) requests cells} {previous :
    Gaussian}

/-- The finite side budget pays the joined complete parent's total discrepancy.

The estimate uses the actual retained cell count and complete corrected paths, including their endpoint connectors. -/
theorem total_close (joined : JoinedCells requests cells readings previous bound) :
    Data.Gaussian.Norm.Basic.normSq (joined.summary.total - cells.capSummary.total) < totalTarget := by
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (joined.pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) budget.tolerance (by
      intro value member
      obtain ⟨pair, member, same⟩ := Map.mem_map.mp member
      rw [← same]
      exact (joined.estimates pair member).2.1)
  rw [sum_errors, Map.length_map, joined.length_eq, ←
    joined.summary.total_eq, joined.original_paths,
    ← cells.capSummary.total_eq] at estimate
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct (edges.length : InverseRootPolynomial.Coordinate)) budget.positive.le
  calc
    _ ≤ (edges.length : InverseRootPolynomial.Coordinate) ^ 2 * budget.tolerance := estimate.trans_eq (by ring1)
    _ ≤ 4 * (edges.length : InverseRootPolynomial.Coordinate) ^ 2 * budget.tolerance := by
      simpa only [_root_.one_mul, Fraction.Field.mul_assoc] using
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
            decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4) nonnegative
    _ < totalTarget := budget.total_paid

/-- The finite side budget pays the joined complete parent's area discrepancy.

Internal block errors and the polygon of block totals use the same cached tolerance and the actual square and fourth
power of the cell count. -/
theorem area_close (joined : JoinedCells requests cells readings previous bound) (boundNonnegative : 0 ≤
  bound) :
    Data.Gaussian.Norm.Basic.normSq (joined.summary.area - cells.capSummary.area) < areaTarget := by
  have toleranceNonnegative := budget.positive.le
  have localArea : 24 * budget.tolerance * bound + 16 * budget.tolerance ^ 2 ≤
      32 * budget.tolerance * (bound + budget.tolerance) := by
    have extra : 0 ≤ 8 * budget.tolerance * bound + 16 * budget.tolerance ^ 2 := add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) toleranceNonnegative) boundNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    calc
      _ ≤ (24 * budget.tolerance * bound + 16 * budget.tolerance ^ 2) +
          (8 * budget.tolerance * bound + 16 * budget.tolerance ^ 2) := le_add_of_nonneg_right extra
      _ = _ := by ring1
  have estimate := IncrementAreaComparison.blocks_area_difference_bound joined.pairs toleranceNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg boundNonnegative toleranceNonnegative))
    (fun pair member => (joined.estimates pair member).1.trans localArea)
    (fun pair member => (joined.estimates pair member).2.1)
    (fun pair member => (joined.estimates pair member).2.2.1)
    (fun pair member => (joined.estimates pair member).2.2.2)
  rw [← joined.summary.area_eq, joined.original_paths, ← cells.capSummary.area_eq, joined.length_eq] at estimate
  have scaleNonnegative : 0 ≤ budget.scale := by
    rw [budget.scale_eq]
    exact add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have slopeLe : bound + budget.tolerance ≤ bound + 3 * budget.tolerance := add_le_add le_rfl (by
    simpa only [_root_.one_mul] using
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 3) toleranceNonnegative)
  calc
    _ ≤ 64 * budget.scale * budget.tolerance * (bound + budget.tolerance) := estimate.trans_eq (by
        rw [budget.scale_eq];
        ring1)
    _ ≤ 64 * budget.scale * budget.tolerance * (bound + 3 * budget.tolerance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct slopeLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) scaleNonnegative) toleranceNonnegative)
    _ ≤ 512 * budget.scale * budget.tolerance * (bound + 3 * budget.tolerance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
              decide +kernel : (64 : InverseRootPolynomial.Coordinate) ≤ 512)
            scaleNonnegative) toleranceNonnegative)
        (add_nonneg boundNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) toleranceNonnegative))
    _ < areaTarget := budget.area_paid

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedEstimates
