module
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
public import Purelib.Riemann.Readings.BoundedPreparedBanks
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation
open Purelib.Data.Nat

public section

/-!
# Certified coarser preparation of finite bank families

The sufficient-depth theorem is a finite upper bound, not a mandatory mesh
size.  Try smaller common depths, retain the first completely checked bank
family, and use the existing unconditional constructor at the upper bound.
Each trial uses the bounded checker for source preparation: a coarse miss
advances the mesh after at most two checked source resets, without the recursive
source retry loop.  Accepted edges still use canonical endpoint transport and
retention, which can themselves perform finite resets.
No successful-run, convergence or caller-fuel premise is introduced.

Every task retains its original clear path and initial owner.  The indexed
bank family certifies exactly those paths at its selected common depth.  Use
singleton families for independent pieces and a paired family when opposite
orientations must share a depth.  The sole import is the bounded bank scanner
over the existing cache interface, prepared-path checker and sufficient-depth proof.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive

open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath
open Purelib.Riemann.Readings

/-- The original dense Gaussian polynomial type. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original canonical Gaussian-rational coordinate type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The original constructive rational scalar type. -/
abbrev Coordinate := Fraction.Rational
/-- The original rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner type. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner

set_option genInjectivity false in
/-- One clear polynomial path with its exact endpoints, ambient containment and initial root owner.

All retained banks are indexed by this original geometric task. -/
structure Task (polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial) where
  /-- The original finite ambient box of the path. -/ ambient : SquareRoot.Preparation.Bank.Adaptive.Box
  /-- The retained starting Gaussian coordinate. -/ start : SquareRoot.Preparation.Bank.Adaptive.Gaussian
  /-- The retained finishing Gaussian coordinate. -/ finish : SquareRoot.Preparation.Bank.Adaptive.Gaussian
  /-- The original clear path with these exact endpoints and polynomial. -/ path : Polynomial.Geometry.ClearPath
    polynomial ambient start finish
  /-- Every original path segment lies in the retained ambient box. -/ within : path.WithinAmbient
  /-- The retained square-root owner over the original starting polynomial value. -/ owner :
    SquareRoot.Preparation.Bank.Adaptive.Owner (polynomial.eval start)

constructive_injectivity Task

/-- Package an existing clear path, its containment proof and its actual initial root owner. -/
@[expose] def Task.ofPath {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} {ambient :
  SquareRoot.Preparation.Bank.Adaptive.Box} {start finish : SquareRoot.Preparation.Bank.Adaptive.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : SquareRoot.Preparation.Bank.Adaptive.Owner (polynomial.eval start)) :
      SquareRoot.Preparation.Bank.Adaptive.Task polynomial :=
  ⟨ambient, start, finish, path, within, owner⟩

set_option genInjectivity false in
/-- The heterogeneous paths and owners remain indices of their actual
cached banks; a family cannot silently substitute another geometric task.

Each retained bank is indexed by its original geometric task. The remaining family carries the exact tail of that task
list at the same depth and positive diameter. -/
inductive Banks {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (depth : Nat) (rootDiameter :
  SquareRoot.Preparation.Bank.Adaptive.Coordinate)
    (positive : 0 < rootDiameter) : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial) → Type where
  /-- The empty certified bank family at the displayed depth. -/ | nil :
    Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive []
  /-- Retain one task's bank and the remaining banks, indexed by the same original task list. -/ | cons {task :
    SquareRoot.Preparation.Bank.Adaptive.Task polynomial} {tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task
    polynomial)}
      (bank : Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth rootDiameter positive task.path
        task.owner)
      (rest : Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive tasks) :
      Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive (task :: tasks)

constructive_injectivity Banks

namespace Banks

variable {polynomial : Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} {depth : Nat}
  {rootDiameter : Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Coordinate}
  {positive : 0 < rootDiameter} {task : Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Task polynomial}
    {tasks : List (Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Task polynomial)}

/-- Read the cached bank for the first original task. -/
@[expose] def head (banks : SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive (task :: tasks)) :
    Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth rootDiameter positive task.path task.owner :=
  match banks with | .cons bank _ => bank

/-- Read the cached bank family for the original remaining tasks. -/
@[expose] def tail (banks : SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive (task :: tasks)) :
    SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive tasks :=
  match banks with | .cons _ rest => rest

end Banks

/-- Take the largest coefficient-computed sufficient depth across the finite original task list. -/
@[expose] def maximumDepth {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (rootDiameter :
  SquareRoot.Preparation.Bank.Adaptive.Coordinate) :
    List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial) → Nat
  | [] => 0
  | task :: tasks => max (Riemann.Paths.PreparedClearPathModels.sufficientDepth task.path rootDiameter)
    (Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks)

/-- Attempt the original task banks at one common depth.

The ordered scan retains each exact accepted bank. A failed finite proposal returns no family; it does not establish
impossibility or replace the total certified fallback. -/
@[expose] def tryBanks {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (depth : Nat)
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter) :
    (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) → Option
      (SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive tasks)
  | [] => some .nil
  | task :: tasks =>
      match Readings.BoundedPreparedBanks.attempt depth rootDiameter positive task.path task.within task.owner with
      | .error _report => none
      | .ok accepted =>
          match Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.tryBanks depth rootDiameter positive tasks
            with
          | none => none
          | some rest => some (.cons accepted.bank rest)

/-- Construct the original task banks above their computed sufficient-depth maximum.

The supplied depth bound gives each original task its same certified dyadic cache. Recursion retains the exact task
tail, common diameter and positivity witness. -/
@[expose] def safeBanks {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (depth : Nat)
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter) :
    (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) →
      SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks ≤ depth →
      SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive tasks
  | [], _ => .nil
  | task :: tasks, enough =>
      .cons
        (.certified (SquareRoot.Preparation.Bank.Cache.CertifiedDyadic.totalCachedAt
          depth rootDiameter positive task.path task.within task.owner
          (by
            have headBound : Riemann.Paths.PreparedClearPathModels.sufficientDepth task.path rootDiameter ≤
                max (Riemann.Paths.PreparedClearPathModels.sufficientDepth task.path rootDiameter)
                  (maximumDepth rootDiameter tasks) := by
              rw [Order.max_eq_natMax]
              exact Order.le_max_left _ _
            exact headBound.trans enough)))
        (Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.safeBanks depth rootDiameter positive tasks (by
          have tailBound : maximumDepth rootDiameter tasks ≤
              max (Riemann.Paths.PreparedClearPathModels.sufficientDepth task.path rootDiameter)
                (maximumDepth rootDiameter tasks) := by
            rw [Order.max_eq_natMax]
            exact Order.le_max_right _ _
          exact tailBound.trans enough))

set_option genInjectivity false in
/-- A retained bank family at a common selected depth between the requested minimum and the computed safe upper bound.

The original heterogeneous tasks, diameter and positivity witness remain indices of the successful family. -/
structure Selected {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat
      := 0) where
  /-- The retained common safe upper depth. -/ upperDepth : Nat
  /-- The upper depth is exactly the maximum of the computed task depth and requested minimum. -/ upperDepth_eq :
    upperDepth = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks) minimumDepth
  /-- The actual depth of every retained bank in the family. -/ depth : Nat
  /-- The selected depth respects the original minimum request. -/ minimum_le : minimumDepth ≤ depth
  /-- The selected depth does not exceed the retained safe upper bound. -/ depth_le : depth ≤ upperDepth
  /-- The successfully checked banks for the exact original task list at the selected depth. -/ banks :
    SquareRoot.Preparation.Bank.Adaptive.Banks depth rootDiameter positive tasks

constructive_injectivity Selected

/-- Select the first successful bank family in the original finite depth interval.

Increasing depths are attempted in order. At the exact retained upper bound, the original sufficient-depth caches supply
the same certified fallback and selected bounds. -/
@[expose] def search {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter)
    (minimum upper : Nat) (upper_eq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks)
      minimum)
    (depth : Nat) (minimum_le : minimum ≤ depth) :
    (remaining : Nat) → upper = depth + remaining → SquareRoot.Preparation.Bank.Adaptive.Selected tasks rootDiameter
      positive minimum
  | 0, bound =>
      have enough : SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks ≤ depth := by
        have upperBound : maximumDepth rootDiameter tasks ≤ upper := by
          rw [upper_eq, Order.max_eq_natMax]
          exact Order.le_max_left _ _
        clear upper_eq
        omega0
      { upperDepth := upper, upperDepth_eq := upper_eq, depth, minimum_le, depth_le := by clear upper_eq; omega0
        banks := SquareRoot.Preparation.Bank.Adaptive.safeBanks depth rootDiameter positive tasks enough }
  | remaining + 1, bound =>
      match SquareRoot.Preparation.Bank.Adaptive.tryBanks depth rootDiameter positive tasks with
      | some banks =>
          { upperDepth := upper, upperDepth_eq := upper_eq, depth, minimum_le, depth_le := by clear upper_eq; omega0,
            banks }
      | none => Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.search tasks rootDiameter positive minimum
        upper upper_eq (depth + 1)
          (by clear upper_eq; omega0) remaining (by clear upper_eq; omega0)

/-- Select certified banks while preserving the requested minimum depth.

The safe upper depth remains the exact maximum of the original computed task depth and requested minimum. The original
finite interval is searched without adding a success or fuel premise. -/
@[expose] def selectFrom {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat)
      :
    SquareRoot.Preparation.Bank.Adaptive.Selected tasks rootDiameter positive minimumDepth :=
  let upper := max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks) minimumDepth
  SquareRoot.Preparation.Bank.Adaptive.search tasks rootDiameter positive minimumDepth upper rfl minimumDepth
    (Nat.le_refl _)
    (upper - minimumDepth) (by
      apply Eq.symm
      apply Subtraction.add_sub_of_le
      dsimp only [upper]
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _)

/-- Total finite selection.  The computed bound and successful bank data are
retained once; no caller chooses a fuel budget or certifies a successful run. -/
@[expose] def select {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) (positive : 0 < rootDiameter) :
      SquareRoot.Preparation.Bank.Adaptive.Selected tasks rootDiameter positive :=
  SquareRoot.Preparation.Bank.Adaptive.selectFrom tasks rootDiameter positive 0

/-- A bank selection with minimum depth zero stays below its computed sufficient maximum.

The retained upper-depth identity and selected depth bound give the result for the exact original task family. -/
theorem Selected.depth_le_sufficient {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} {tasks :
  List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)}
    {rootDiameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate} {positive : 0 < rootDiameter}
    (selected : SquareRoot.Preparation.Bank.Adaptive.Selected tasks rootDiameter positive) : selected.depth ≤
      SquareRoot.Preparation.Bank.Adaptive.maximumDepth rootDiameter tasks := by
  have bound := selected.depth_le.trans selected.upperDepth_eq.le
  rewrite [Order.max_eq_natMax, Order.max_zero] at bound
  exact bound

/-- An empty task family selects depth zero. -/
theorem empty_depth {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (rootDiameter :
  SquareRoot.Preparation.Bank.Adaptive.Coordinate)
    (positive : 0 < rootDiameter) : (SquareRoot.Preparation.Bank.Adaptive.select ([] : List
      (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) rootDiameter positive).depth = 0 := rfl

/-- When a common depth is unnecessary, select each original segment
independently and thread its actual terminal root owner into the next one. -/
@[expose] def preparePath {polynomial : SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} {ambient :
  SquareRoot.Preparation.Bank.Adaptive.Box} :
    {start finish : SquareRoot.Preparation.Bank.Adaptive.Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish) →
      path.WithinAmbient → (owner : SquareRoot.Preparation.Bank.Adaptive.Owner (polynomial.eval start)) →
        (diameter : SquareRoot.Preparation.Bank.Adaptive.Coordinate) → 0 < diameter →
          Riemann.Paths.PreparedClearPathModels.PreparedPath path owner
  | _, _, .nil point, _, owner, _, _ => .nil point owner
  | _, _, .cons head tail, within, owner, diameter, positive =>
      let selected := SquareRoot.Preparation.Bank.Adaptive.select
        [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath (.cons head (.nil _)) (.cons within.head (.nil _)) owner]
          diameter positive
      match selected.banks.head.prepared with
      | .cons _ _ _ _ preparedHead _ =>
          .cons head tail owner within.head preparedHead
            (Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.preparePath tail within.tail
              preparedHead.finishOwner diameter positive)

end Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
