module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.Integration.PreparedParentSplitSelection
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Scalar-axis location in consecutive parent caches

The original endpoint chain supplies a crossing witness. Finite search reads
the retained parent cache in order and returns its first certified half-open
crossing with the original index and endpoint bounds.
-/
namespace Purelib.Riemann.Integration.PreparedParentAxisLocation

public section

open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedParentSplitSelection (parentAt)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The query lies between the original projected start, inclusively, and projected finish, strictly. -/
@[expose] def Crosses (project : Basic.Canonical → Fraction.Rational) (query : Fraction.Rational) (parent : CenteredEdge
  curve differential) : Prop :=
  project (parent.edge.point 0) ≤ query ∧ query < project (parent.edge.point 1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Path.Gaussian in
/-- A query between the original chain endpoints is crossed by one retained parent.

Finite chain induction either identifies the original head crossing or transports the same query bounds into the
retained tail. The resulting finite index refers to that original cached list. -/
private theorem chain_crosses (project : Basic.Canonical → Fraction.Rational) (query : Fraction.Rational)
    {parents : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    (lower : project first.coordinate ≤ query) (upper : query < project last.coordinate) :
    ∃ index : Fin parents.length, Crosses project query (parentAt parents index) := by
  induction chain with
  | nil point => exact (not_lt_of_ge lower upper).elim
  | @cons parent remaining finish tail ih =>
    if before : query < project (parent.edge.point 1) then
      refine ⟨0, ?_, before⟩
      change project (parent.edge.point 0) ≤ query
      rw [parent.edge.point_zero]
      exact lower
    else
      have next : project (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter) ≤ query := by
        rw [← parent.edge.point_one]
        exact le_of_not_gt before
      obtain ⟨index, bounds⟩ := ih next upper
      exact ⟨index.succ, bounds⟩

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A finite original parent index with certified projected crossing bounds.

The lower bound includes the parent's start and the upper bound excludes its finish, preserving the exact cached list
and query. -/
structure AxisLocation (parents : List (CenteredEdge curve differential))
    (project : Basic.Canonical → Fraction.Rational) (query : Fraction.Rational) where
  /-- The finite index of the original cached parent crossing this query. -/ index : Fin parents.length
  /-- The selected parent's projected start is at most the original query. -/ lower : project ((parentAt parents
    index).edge.point 0) ≤ query
  /-- The original query is strictly before the selected parent's projected finish. -/ upper : query < project
    ((parentAt parents index).edge.point 1)

constructive_injectivity AxisLocation

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Search the original parent list for its first certified projected crossing.

The supplied existence witness certifies success; the executable recursion checks each retained parent and preserves its
original finite index. -/
@[expose] def search (project : Basic.Canonical → Fraction.Rational) (query : Fraction.Rational) :
    (parents : List (CenteredEdge curve differential)) →
    (∃ index : Fin parents.length, Crosses project query (parentAt parents index)) → AxisLocation parents project query
  | [], covered =>
    have absent : False := by obtain ⟨index, _⟩ := covered; exact Fin.elim0 index
    absent.elim
  | parent :: rest, covered =>
    if found : project (parent.edge.point 0) ≤ query ∧ query < project (parent.edge.point 1) then
      ⟨0, found.1, found.2⟩
    else
      have remaining : ∃ index : Fin rest.length, Crosses project query (parentAt rest index) := by
        obtain ⟨⟨index, bound⟩, bounds⟩ := covered
        cases index with
        | zero => exact (found bounds).elim
        | succ index => exact ⟨⟨index, Nat.lt_of_succ_lt_succ bound⟩, bounds⟩
      let located := search project query rest remaining
      ⟨located.index.succ, located.lower, located.upper⟩

namespace ParentCache
variable {ambient : Purelib.Geometry.Rational.Box} {first last : Purelib.Data.Gaussian.Basic.Canonical}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval first)}
  {prepared : CoveredTracedPath path owner} {sheet : Fin 2}

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Paths in
/-- Locate a projected crossing in the exact cached parent chain from its endpoint bounds.

The cache supplies the original chain existence certificate. Search checks that same parent list and returns the first
half-open crossing with its original projected endpoint bounds. -/
@[expose] def locateAxis (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational) (query : Fraction.Rational)
    (lower : project first ≤ query) (upper : query < project last) : AxisLocation cache.parents project query :=
  search project query cache.parents (by
    obtain ⟨chain⟩ := cache.chain
    exact chain_crosses project query chain lower upper)

section
open Purelib.Geometry.Path.Gaussian
/-- An ordered parent chain's projected start precedes every retained parent start.

The original endpoint identities join consecutive parents. Finite induction combines each supplied parent ordering with
the retained tail chain, keeping the same member and projected start. -/
private theorem chain_start_le (project : Basic.Canonical → Fraction.Rational)
    {parents : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    (ordered : ∀ parent ∈ parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    {parent : CenteredEdge curve differential} (member : parent ∈ parents) :
    project first.coordinate ≤ project (parent.edge.point 0) := by
  induction chain with
  | nil => cases member
  | @cons head tail finish chain ih =>
    rcases Membership.mem_cons.mp member with rfl | member
    · exact (congrArg project parent.edge.point_zero).symm.le
    · have next := ih (fun p present => ordered p (List.mem_cons_of_mem head present)) member
      have step := ordered head List.mem_cons_self
      rw [head.edge.point_zero, head.edge.point_one] at step
      exact step.trans next

/-- An ordered original parent chain has nondecreasing projected endpoints.

The original head ordering transports the projected start to its endpoint. The retained consecutive tail supplies the
remaining bound to the same final point. -/
private theorem chain_total_le (project : Basic.Canonical → Fraction.Rational)
    {parents : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    (ordered : ∀ parent ∈ parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1)) :
    project first.coordinate ≤ project last.coordinate := by
  induction chain with
  | nil => exact le_rfl
  | @cons head tail finish chain ih =>
    have step := ordered head List.mem_cons_self
    rw [head.edge.point_zero, head.edge.point_one] at step
    exact step.trans (ih (fun p member => ordered p (List.mem_cons_of_mem head member)))

/-- Every retained parent finish precedes the ordered chain's projected finish.

The original membership identifies either the head parent or a member of the dependent tail. Its endpoint identity and
retained ordered tail give the bound to the same final point. -/
private theorem chain_end_le (project : Basic.Canonical → Fraction.Rational)
    {parents : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    (ordered : ∀ parent ∈ parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    {parent : CenteredEdge curve differential} (member : parent ∈ parents) :
    project (parent.edge.point 1) ≤ project last.coordinate := by
  induction chain with
  | nil => cases member
  | @cons head tail finish chain ih =>
    have rest := fun p present => ordered p (List.mem_cons_of_mem head present)
    rcases Membership.mem_cons.mp member with rfl | member
    · exact (congrArg project parent.edge.point_one).trans_le (chain_total_le project chain rest)
    · exact ih rest member

end

open Purelib.Riemann.Paths in
/-- Every indexed cached parent lies within the original chain's projected endpoints.

The retained finite index supplies membership in the original cached list. The cache's own consecutive chain and the
given pointwise ordering bound both endpoints of that same parent. -/
theorem parent_bounds (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential sheet)
  (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    (i : Fin cache.parents.length) :
    project first ≤ project ((parentAt cache.parents i).edge.point 0) ∧
      project ((parentAt cache.parents i).edge.point 1) ≤ project last := by
  obtain ⟨chain⟩ := cache.chain
  exact ⟨chain_start_le project chain ordered (List.getElem_mem i.isLt),
    chain_end_le project chain ordered (List.getElem_mem i.isLt)⟩

open Purelib.Geometry.Path.Gaussian in
/-- Earlier parents in an ordered original chain finish before later parents start.

The supplied original finite indices determine the same head or tail occurrences. Their strict index order and retained
endpoint identities establish separation without choosing new parents. -/
private theorem chain_separated (project : Basic.Canonical → Fraction.Rational)
    {parents : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last))
    (ordered : ∀ parent ∈ parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    (i j : Fin parents.length) (before : i.val < j.val) :
    project ((parentAt parents i).edge.point 1) ≤ project ((parentAt parents j).edge.point 0) := by
  induction chain with
  | nil => exact Fin.elim0 i
  | @cons head tail finish chain ih =>
    rcases i with ⟨i, ib⟩
    rcases j with ⟨j, jb⟩
    cases j with
    | zero => exact (Nat.not_lt_zero _ before).elim
    | succ j =>
      have rest := fun p present => ordered p (List.mem_cons_of_mem head present)
      cases i with
      | zero =>
        have bound := chain_start_le project chain rest (List.getElem_mem (Nat.lt_of_succ_lt_succ jb))
        exact (congrArg project head.edge.point_one).trans_le bound
      | succ i =>
        exact ih rest ⟨i, Nat.lt_of_succ_lt_succ ib⟩ ⟨j, Nat.lt_of_succ_lt_succ jb⟩
          (Nat.lt_of_succ_lt_succ before)

open Purelib.Riemann.Paths in
/-- The exact cached indices preserve projected separation of ordered parents.

Both finite indices refer to the retained parent cache. Its consecutive chain and original pointwise endpoint ordering
place every earlier finish before the later start. -/
theorem parents_separated (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    (i j : Fin cache.parents.length) (before : i.val < j.val) :
    project ((parentAt cache.parents i).edge.point 1) ≤ project ((parentAt cache.parents j).edge.point 0) := by
  obtain ⟨chain⟩ := cache.chain
  exact chain_separated project chain ordered i j before

open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
/-- Strictly increasing parents with a shared projected endpoint have adjacent original indices. -/
theorem parents_no_skip (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) < project (parent.edge.point 1))
    (i j : Fin cache.parents.length) (before : i.val < j.val)
    (joint : project ((parentAt cache.parents i).edge.point 1) = project ((parentAt cache.parents j).edge.point 0)) :
    j.val = i.val + 1 := by
  apply Nat.le_antisymm _ (Nat.succ_le_of_lt before)
  if next : j.val ≤ i.val + 1 then exact next
  else
    have gap := Nat.lt_of_not_ge next
    let middle : Fin cache.parents.length := ⟨i.val + 1, gap.trans j.isLt⟩
    have left := PreparedParentAxisLocation.ParentCache.parents_separated cache project (fun p member => (ordered p
      member).le)
      i middle (Nat.lt_succ_self i.val)
    have right := PreparedParentAxisLocation.ParentCache.parents_separated cache project (fun p member => (ordered p
      member).le) middle j gap
    have width := ordered (parentAt cache.parents middle) (List.getElem_mem middle.isLt)
    exact (ne_of_lt (left.trans_lt (width.trans_le right)) joint).elim

/-- A strictly ordered parent's projected start equals the chain start only at index zero. -/
theorem parent_at_start (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) < project (parent.edge.point 1))
    (i : Fin cache.parents.length)
    (endpoint : project ((parentAt cache.parents i).edge.point 0) = project first) : i.val = 0 := by
  cases position : i.val with
  | zero => rfl
  | succ n =>
    let initial : Fin cache.parents.length := ⟨0, (Nat.zero_le i.val).trans_lt i.isLt⟩
    have bounds := PreparedParentAxisLocation.ParentCache.parent_bounds cache project (fun p member => (ordered p
      member).le) initial
    have width := ordered (parentAt cache.parents initial) (List.getElem_mem initial.isLt)
    have separated := PreparedParentAxisLocation.ParentCache.parents_separated cache project (fun p member => (ordered p
      member).le) initial i
      (by change 0 < i.val; rw [position]; exact Nat.zero_lt_succ n)
    exact (ne_of_lt ((bounds.1.trans_lt width).trans_le separated) endpoint.symm).elim

/-- A strictly ordered parent's projected finish equals the chain finish only at the final index. -/
theorem parent_at_finish (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) < project (parent.edge.point 1))
    (i : Fin cache.parents.length)
    (endpoint : project ((parentAt cache.parents i).edge.point 1) = project last) :
    i.val + 1 = cache.parents.length := by
  apply Nat.le_antisymm (Nat.succ_le_of_lt i.isLt)
  if final : cache.parents.length ≤ i.val + 1 then exact final
  else
    let next : Fin cache.parents.length := ⟨i.val + 1, Nat.lt_of_not_ge final⟩
    have separated := PreparedParentAxisLocation.ParentCache.parents_separated cache project (fun p member => (ordered p
      member).le) i next
      (Nat.lt_succ_self i.val)
    have width := ordered (parentAt cache.parents next) (List.getElem_mem next.isLt)
    have bounds := PreparedParentAxisLocation.ParentCache.parent_bounds cache project (fun p member => (ordered p
      member).le) next
    exact (ne_of_lt ((separated.trans_lt width).trans_le bounds.2) endpoint).elim

/-- The selected original parent index is monotone in the projected query on an ordered cache. -/
theorem locateAxis_mono (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared differential
  sheet) (project : Basic.Canonical → Fraction.Rational)
    (ordered : ∀ parent ∈ cache.parents, project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    {a b : Fraction.Rational} (increasing : a ≤ b)
    (aLower : project first ≤ a) (aUpper : a < project last)
    (bLower : project first ≤ b) (bUpper : b < project last) :
    (PreparedParentAxisLocation.ParentCache.locateAxis cache project a aLower aUpper).index.val ≤
      (PreparedParentAxisLocation.ParentCache.locateAxis cache project b bLower bUpper).index.val := by
  let left := PreparedParentAxisLocation.ParentCache.locateAxis cache project a aLower aUpper
  let right := PreparedParentAxisLocation.ParentCache.locateAxis cache project b bLower bUpper
  if before : left.index.val ≤ right.index.val then exact before
  else
    obtain ⟨chain⟩ := cache.chain
    have separated := chain_separated project chain ordered right.index left.index (Nat.lt_of_not_ge before)
    exact (not_lt_of_ge (separated.trans (left.lower.trans increasing)) right.upper).elim

end

end ParentCache
end
end Purelib.Riemann.Integration.PreparedParentAxisLocation
