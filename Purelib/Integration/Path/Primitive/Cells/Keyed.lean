module

public import Purelib.Integration.Path.Primitive.Cells
public import Purelib.Integration.Path.Primitive.Cells.Targets
public import Purelib.Topology.Chain.PathBoundary
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Primitive comparisons sharing actual finite endpoint keys

The geometric path and its original polynomial cells remain unchanged.
Adjacent cells share an endpoint key independently of their physical point
labels. A closed key path therefore cancels only the same retained reading,
including when repeated coordinates belong to different original owners.
-/

public section

namespace Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

set_option genInjectivity false in
/-- Ordered local primitive comparisons with shared keys on the same original physical lifted path.

A join shares the actual middle key and its retained reading. Keys need
not identify equal coordinates or chart labels. Every source cell,
primitive comparison, physical endpoint and local bound stays original.
-/
inductive KeyedCells {sheets : Nat} {Key : Type} (endpoint : Key → Basic.Canonical)
    (localBound endpointBound : Fraction.Rational) :
    {start finish : LiftedPoint sheets} → List Cell.Basic.CellModel → LiftedPath sheets start finish →
      Key → Key → Type
  /-- An empty original path has the same initial and final endpoint key. -/
  | nil (point : LiftedPoint sheets) (key : Key) :
      KeyedCells endpoint localBound endpointBound [] (.nil point) key key
  /-- Retain an original cell and primitive, sharing its actual final key with the unchanged tail. -/
  | cons {start middle finish : LiftedPoint sheets} {remaining : List Cell.Basic.CellModel}
      {path : LiftedPath sheets middle finish} {firstKey middleKey lastKey : Key}
      (cell : Cell.Basic.CellModel) (lifted : LiftedCell start middle)
      (start_eq : cell.start = start.coordinate) (finish_eq : cell.finish = middle.coordinate)
      (comparison : Cell.Primitive.Comparison cell)
      (local_le : comparison.bound ≤ localBound)
      (start_le : Norm.Basic.normSq (comparison.value.eval 0 - endpoint firstKey) ≤ endpointBound)
      (finish_le : Norm.Basic.normSq (comparison.value.eval 1 - endpoint middleKey) ≤ endpointBound)
      (tail : KeyedCells endpoint localBound endpointBound remaining path middleKey lastKey) :
      KeyedCells endpoint localBound endpointBound (cell :: remaining) (.cons lifted path) firstKey lastKey

constructive_injectivity KeyedCells

namespace KeyedCells

variable {sheets : Nat} {Key : Type} {endpoint : Key → Basic.Canonical}
    {localBound endpointBound : Fraction.Rational} {start finish : LiftedPoint sheets}
    {cells : List Cell.Basic.CellModel} {path : LiftedPath sheets start finish} {firstKey lastKey : Key}

/-- Read the original ordered endpoint-key pairs from the retained cell comparison spine. -/
@[expose] def keys : {start finish : LiftedPoint sheets} → {cells : List Cell.Basic.CellModel} →
    {path : LiftedPath sheets start finish} → {firstKey lastKey : Key} →
    KeyedCells endpoint localBound endpointBound cells path firstKey lastKey → List (Key × Key)
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons (firstKey := left) (middleKey := right) _ _ _ _ _ _ _ _ tail =>
      (left, right) :: tail.keys

/-- The actual retained key word is an original finite endpoint path. -/
theorem keys_path (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    PathEndpoints Prod.fst Prod.snd chain.keys firstKey lastKey := by
  induction chain with
  | nil point key => exact .nil key
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail previous =>
      exact .cons previous

/-- Read one original primitive endpoint defect per retained cell occurrence. -/
@[expose] def errorTerms : {start finish : LiftedPoint sheets} → {cells : List Cell.Basic.CellModel} →
    {path : LiftedPath sheets start finish} → {firstKey lastKey : Key} →
    KeyedCells endpoint localBound endpointBound cells path firstKey lastKey → List Basic.Canonical
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons (firstKey := left) (middleKey := right) cell _ _ _ _ _ _ _ tail =>
      (endpoint right - endpoint left - cell.integralSample) :: tail.errorTerms

/-- The actual keyed defect list has the original source-cell count. -/
theorem errorTerms_length (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    chain.errorTerms.length = cells.length := by
  induction chain with
  | nil point key => rfl
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail previous =>
      exact congrArg Nat.succ previous

/-- The actual ordered defects telescope to the two retained endpoint keys and original whole integral. -/
theorem errorTerms_sum (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    Norm.Sum.Basic.gaussianSum chain.errorTerms = endpoint lastKey - endpoint firstKey -
      (Path.Basic.PathModel.mk cells).integralSample := by
  induction chain with
  | nil point key =>
      change (0 : Basic.Canonical) = endpoint key - endpoint key - 0
      ring1
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail previous =>
      change endpoint _ - endpoint _ - cell.integralSample + Norm.Sum.Basic.gaussianSum tail.errorTerms =
        endpoint _ - endpoint _ - (cell.integralSample + (Path.Basic.PathModel.mk _).integralSample)
      rewrite [previous]
      ring1

/-- The original local residual and endpoint payments bound the mass of actual keyed defects. -/
theorem errorTerms_normMass (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    Norm.Sum.Basic.gaussianNormSqSum chain.errorTerms ≤
      (cells.length : Fraction.Rational) * (4 * localBound + 8 * endpointBound) := by
  induction chain with
  | nil point key =>
      change (0 : Fraction.Rational) ≤ 0 * _
      rewrite [Fraction.Field.zero_mul_direct]
      exact Fraction.Order.Basic.le_refl 0
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail previous =>
      change Basic.Canonical.normSq (endpoint _ - endpoint _ - cell.integralSample) +
        Norm.Sum.Basic.gaussianNormSqSum tail.errorTerms ≤ _
      rewrite [← Norm.Basic.normSq_eq_canonical]
      have bounded := Cells.cell_error_le comparison local_le start_le finish_le
      have combined := Fraction.Order.Arithmetic.add_le_add_direct bounded previous
      rewrite [List.length_cons, Fraction.Cast.natCast_add_direct]
      change _ ≤ ((List.length _ : Fraction.Rational) + 1) * _
      exact combined.trans_eq (by ring1)

/-- Finite Cauchy bounds the original whole integration sample against the same actual endpoint-key difference. -/
theorem integral_error_le (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    Norm.Basic.normSq ((Path.Basic.PathModel.mk cells).integralSample -
      (endpoint lastKey - endpoint firstKey)) ≤
      (cells.length : Fraction.Rational) *
        ((cells.length : Fraction.Rational) * (4 * localBound + 8 * endpointBound)) := by
  have bounded := Norm.Sum.Basic.normSq_gaussianSum_le chain.errorTerms
  rewrite [← Norm.Basic.normSq_eq_canonical, chain.errorTerms_sum, chain.errorTerms_length] at bounded
  rewrite [Norm.Bounds.normSq_sub_symm]
  exact bounded.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    chain.errorTerms_normMass (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

/-- The keyed certificates retain the original physical path and source-cell following witness. -/
theorem follows (chain : KeyedCells endpoint localBound endpointBound cells path firstKey lastKey) :
    LiftedPath.FollowedBy cells path := by
  induction chain with
  | nil point key => exact .nil point
  | cons cell lifted start_eq finish_eq comparison local_le start_le finish_le tail previous =>
      exact .cons start_eq finish_eq previous

end KeyedCells

namespace Targets

/-- The same original count-paid request bounds a keyed primitive chain without changing its physical path. -/
theorem integral_keyed_error_le {sheets : Nat} {start finish : LiftedPoint sheets}
    {original : LiftedPath sheets start finish} {stage : Nat} (targets : Targets original stage)
    {Key : Type} {endpoint : Key → Basic.Canonical} {cells : List Cell.Basic.CellModel}
    {firstKey lastKey : Key}
    (chain : KeyedCells endpoint targets.localBound targets.endpoint cells original firstKey lastKey) :
    Norm.Basic.normSq ((Path.Basic.PathModel.mk cells).integralSample -
      (endpoint lastKey - endpoint firstKey)) ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 stage := by
  have bounded := chain.integral_error_le
  have countEqual := LiftedPath.followedBy_length chain.follows
  rewrite [← targets.count_eq] at countEqual
  rewrite [countEqual] at bounded
  have squareEqual : (targets.count : Fraction.Rational) *
      ((targets.count : Fraction.Rational) * (4 * targets.localBound + 8 * targets.endpoint)) =
        targets.countSquare * (4 * targets.localBound + 8 * targets.endpoint) := by
    rewrite [targets.countSquare_eq]
    ring1
  rewrite [squareEqual] at bounded
  exact bounded.trans (targets.payment.trans_eq targets.budget_eq)

end Targets

end Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints

end
