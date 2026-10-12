module

import Purelib.Approximation.Gaussian.Name.Coherent.State
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

/-!
# Common requests and refinement of retained coefficient tables

Each coefficient uses the same retained full-table request and its original
channel. Structural certificates preserve degree and ordered channels while
bounding allowances and coefficient quadrance differences.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Data.Gaussian

/-- One positive request small enough for every coherence modulus in the
finite table.

The same recursive common request combines the original channel accuracy
requests in their retained order. It introduces no new coefficient states or
changes to the displayed target. -/
@[expose] public def requestTarget : List Approximation.Gaussian.Name.Coherent.State.CoefficientState →
  Fraction.Rational → Fraction.Rational
  | [], target => target
  | entry :: remaining, target =>
      Approximation.Gaussian.Process.Coherence.Basic.Coherent.commonRequest
        (Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.requestTarget remaining
          target)
        (entry.channel.coherent.accuracyRequest target)

/-- A positive target gives a positive common refinement request for the finite table.

Each original channel supplies a positive accuracy request. The retained
common-request operation preserves positivity along the original finite tail. -/
public theorem requestTarget_pos : ∀ (entries : List Approximation.Gaussian.Name.Coherent.State.CoefficientState)
    {target : Fraction.Rational}, 0 < target → 0 < CoefficientTable.requestTarget entries target
  | [], _target, positive => positive
  | entry :: remaining, _target, positive =>
      Approximation.Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
        (Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.requestTarget_pos remaining
          positive)
        (entry.channel.coherent.accuracyRequest_pos positive)

/-- Refine every displayed coefficient by the same finite table request.

The complete table request is computed once and passed with its original
positivity certificate to each retained state. The mapped list keeps the
original channels and coefficient order. -/
@[expose] public def refine (table : CoefficientTable) (target : Fraction.Rational)
    (positive : 0 < target) : CoefficientTable :=
  let request := Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.requestTarget table.entries target
  let requestPositive := Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.requestTarget_pos table.entries
    positive
  ⟨table.entries.map fun entry => entry.refine request requestPositive⟩

/-- Simultaneous coefficient refinement preserves the displayed polynomial degree.

Each retained state contributes exactly one refined entry. Structural map
length preserves the original displayed finite coefficient count. -/
@[simp] public theorem refine_degree (table : CoefficientTable)
    (target : Fraction.Rational) (positive : 0 < target) :
    (table.refine target positive).degree = table.degree := by
  change (table.entries.map fun entry =>
    entry.refine (CoefficientTable.requestTarget table.entries target)
      (CoefficientTable.requestTarget_pos table.entries positive)).length = table.entries.length
  exact List.Map.length_map _ table.entries

/-- The common request is strictly below every retained channel accuracy request.

The selected entry must belong to the finite table and the requested target must be positive. -/
public theorem requestTarget_lt_accuracy_of_mem :
    ∀ (entries : List Approximation.Gaussian.Name.Coherent.State.CoefficientState) {entry :
      Approximation.Gaussian.Name.Coherent.State.CoefficientState},
      entry ∈ entries → ∀ {target : Fraction.Rational}, 0 < target →
        CoefficientTable.requestTarget entries target <
          entry.channel.coherent.accuracyRequest target
  | [], entry, member, target, positive => by
      nomatch member
  | head :: remaining, entry, member, target, positive => by
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · subst head
        exact Approximation.Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right
          (CoefficientTable.requestTarget_pos remaining positive)
          (entry.channel.coherent.accuracyRequest_pos positive)
      · exact
          (Approximation.Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left
            (CoefficientTable.requestTarget_pos remaining positive)
            (head.channel.coherent.accuracyRequest_pos positive)).trans

                (requestTarget_lt_accuracy_of_mem
                remaining tailMember positive)

/-- Refining an included coefficient sublist changes each value by quadrance at most eight times the target.

The original allowances must already be below the positive target; every sublist entry uses the same request computed
from the full table. -/
private theorem coefficientsClose_refine :
    ∀ (allEntries entries : List Approximation.Gaussian.Name.Coherent.State.CoefficientState)
      (target : Fraction.Rational) (positive : 0 < target),
      (∀ entry, entry ∈ entries → entry ∈ allEntries) →
      CoefficientTable.AllowancesLt entries target →
      Gaussian.List.Proximity.CoefficientsClose
        (entries.map Approximation.Gaussian.Name.Coherent.State.CoefficientState.value)
        (entries.map fun entry =>
          (entry.refine (CoefficientTable.requestTarget allEntries target)
            (CoefficientTable.requestTarget_pos allEntries positive)).value)
        (8 * target)
  | allEntries, [], target, positive, _included, _allowances => trivial
  | allEntries, entry :: remaining, target, positive, included, allowances => by
      rcases allowances with ⟨oldSmall, tailSmall⟩
      constructor
      · have member : entry ∈ allEntries :=
          included entry (List.Mem.head remaining)
        have newSmall :
            (entry.refine (CoefficientTable.requestTarget allEntries target)
              (CoefficientTable.requestTarget_pos allEntries positive)).allowance < target :=
          entry.channel.coherent.refine_accurate entry.state target positive
            (CoefficientTable.requestTarget allEntries target)
            (CoefficientTable.requestTarget_pos allEntries positive)
            (CoefficientTable.requestTarget_lt_accuracy_of_mem allEntries member positive)
        have close := entry.channel.coherent.possible_close
          entry.value_possible
          (entry.refine (CoefficientTable.requestTarget allEntries target)
            (CoefficientTable.requestTarget_pos allEntries positive)).value_possible
        exact (calc
            Data.Gaussian.Norm.Basic.normSq
                (entry.value -
                  (entry.refine (CoefficientTable.requestTarget allEntries target)
                    (CoefficientTable.requestTarget_pos allEntries positive)).value) ≤
                4 *
                  (entry.allowance +
                    (entry.refine (CoefficientTable.requestTarget allEntries target)
                      (CoefficientTable.requestTarget_pos allEntries positive)).allowance) := close
            _ < 4 * (target + target) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct oldSmall newSmall)
            _ = 8 * target := by ring1).le
      · exact Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.coefficientsClose_refine
          allEntries remaining target positive
          (by
            intro tailEntry tailMember
            exact included tailEntry
              (List.Mem.tail entry tailMember))
          tailSmall

/-- Every refined coefficient has coherence allowance strictly below the
common visible target.

Membership in the original table bounds the same common request by the
selected channel accuracy request. The original state refinement then meets
the supplied positive target. -/
public theorem refine_allowance_lt
    (table : CoefficientTable) {entry : Approximation.Gaussian.Name.Coherent.State.CoefficientState}
    (member : entry ∈ table.entries) (target : Fraction.Rational)
    (positive : 0 < target) :
    (entry.refine (CoefficientTable.requestTarget table.entries target)
      (CoefficientTable.requestTarget_pos table.entries positive)).allowance < target := by
  exact entry.channel.coherent.refine_accurate entry.state target positive
    (CoefficientTable.requestTarget table.entries target)
    (CoefficientTable.requestTarget_pos table.entries positive)
    (CoefficientTable.requestTarget_lt_accuracy_of_mem table.entries member positive)

/-- A shared full-table request brings every included sublist allowance below the positive target.

Every included state uses the request calculated from the same full table.
Its membership certificate supplies the channel accuracy bound, while
structural recursion preserves the original sublist order. -/
private theorem refine_allowances_lt_list :
    ∀ (allEntries entries : List Approximation.Gaussian.Name.Coherent.State.CoefficientState)
      (target : Fraction.Rational) (positive : 0 < target),
      (∀ entry, entry ∈ entries → entry ∈ allEntries) →
      CoefficientTable.AllowancesLt
        (entries.map fun entry =>
          entry.refine (CoefficientTable.requestTarget allEntries target)
            (CoefficientTable.requestTarget_pos allEntries positive)) target
  | allEntries, [], target, positive, included => trivial
  | allEntries, entry :: remaining, target, positive, included => by
      constructor
      · exact entry.channel.coherent.refine_accurate entry.state target positive
          (CoefficientTable.requestTarget allEntries target)
          (CoefficientTable.requestTarget_pos allEntries positive)
          (CoefficientTable.requestTarget_lt_accuracy_of_mem allEntries
            (included entry (List.Mem.head remaining)) positive)
      · exact Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.refine_allowances_lt_list
          allEntries remaining target positive
          (by
            intro tailEntry tailMember
            exact included tailEntry
              (List.Mem.tail entry tailMember))

/-- Every entry of the refined table has allowance below the requested positive target.

The original common request is supplied to every displayed coefficient
state. Each retained channel accuracy certificate bounds its resulting
allowance strictly below the same positive target. -/
public theorem refine_allowances_lt (table : CoefficientTable)
    (target : Fraction.Rational) (positive : 0 < target) :
    CoefficientTable.AllowancesLt (table.refine target positive).entries target := by
  exact
    CoefficientTable.refine_allowances_lt_list table.entries table.entries target positive
      (fun entry member => member)

/-- Refining each retained state preserves the ordered list of original coefficient channels.

Refinement retains each original channel exactly. Structural induction
pairs the same ordered head and tail channels without equating state values. -/
private theorem sameChannels_map_refine
    (entries : List Approximation.Gaussian.Name.Coherent.State.CoefficientState) (request : Fraction.Rational)
    (positive : 0 < request) :
    CoefficientTable.SameChannels entries (entries.map fun entry =>
      entry.refine request positive) := by
  induction entries with
  | nil => trivial
  | cons entry remaining inductionHypothesis =>
      change entry.channel = (entry.refine request positive).channel ∧
        CoefficientTable.SameChannels remaining
          (remaining.map fun retained => retained.refine request positive)
      exact ⟨(entry.refine_channel request positive).symm, inductionHypothesis⟩

/-- Simultaneous table refinement preserves all original coefficient channels in order.

The same finite table request refines each retained state without changing
its channel. Their original order supplies the complete channel certificate. -/
public theorem sameChannels_refine (table : CoefficientTable)
    (target : Fraction.Rational) (positive : 0 < target) :
    CoefficientTable.SameChannels table.entries (table.refine target positive).entries := by
  exact CoefficientTable.sameChannels_map_refine table.entries
    (CoefficientTable.requestTarget table.entries target)
    (CoefficientTable.requestTarget_pos table.entries positive)

/-- A simultaneous refinement of a table whose current allowances are below
`target` changes every displayed coefficient by quadrance at most
`8 * target`.

The preceding allowances are strictly below the positive target. Original
channel coherence bounds each refined value difference by eight times that
target, retaining the complete ordered coefficient lists. -/
public theorem values_close_refine (table : CoefficientTable)
    (target : Fraction.Rational) (positive : 0 < target)
    (currentSmall : CoefficientTable.AllowancesLt table.entries target) :
    Gaussian.List.Proximity.CoefficientsClose table.values (table.refine target positive).values
      (8 * target) := by
  change Gaussian.List.Proximity.CoefficientsClose
    (table.entries.map Approximation.Gaussian.Name.Coherent.State.CoefficientState.value)
    ((table.entries.map fun entry =>
      entry.refine (CoefficientTable.requestTarget table.entries target)
        (CoefficientTable.requestTarget_pos table.entries positive)).map
      Approximation.Gaussian.Name.Coherent.State.CoefficientState.value)
    (8 * target)
  rewrite [List.Map.map_map]
  exact CoefficientTable.coefficientsClose_refine table.entries table.entries target positive
    (fun entry member => member) currentSmall

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
