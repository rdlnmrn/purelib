module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Table.Basic
public import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Data.List.Map
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Table

open Purelib.Approximation.Gaussian.Table.Basic

open Purelib.Data.List

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Joint finite requests for coherent CCL tables

Higher jets, local polynomial models, and finite-dimensional directional data
all consist of a displayed finite list of coherent CCL channels.  This module
computes one rational request shared by every list entry.  Membership in the
finite list is enough to recover strict enclosure and semantic-allowance
bounds, persistent prefix growth, and exact parser semantics for that entry.

The recursion is over the displayed list.  There is no unbounded coordinate
space, infimum, completed vector, or quantified family of all coefficients.
-/

namespace Purelib.Approximation.Gaussian.Table.Basic
namespace ChannelTable

/-- Embed a finite displayed Gaussian-rational table as terminating coherent CCL channels. -/
def exact (values : List Canonical) :
  Gaussian.Table.Basic.ChannelTable :=
  ⟨values.map Coherence.exact⟩

/-- Embedding a finite exact Gaussian table preserves its length. -/
@[simp] theorem exact_length (values : List
  Canonical) :
    (exact values).length = values.length := by
  simp only [exact, ChannelTable.length, Map.length_map, -eq_self,
    -iff_self]
  rfl

/-- Any shared positive request preserves the center of an exact Gaussian channel. -/
@[simp] theorem sharedName_exact_center (channels : List
  CoherentNamed)
    (value : Canonical) (target : Fraction.Rational) (positive : 0 < target) :
    ((Request.sharedName channels
        (Coherence.exact value)
        target positive).process.ball
      (Request.sharedName channels
        (Coherence.exact value)
        target positive).state).center = value := by
  rfl

/-- Terminating exact tables specialize literally to their displayed input list after any positive shared request. -/
theorem exact_requestCenters (values : List
  Canonical) (target : Fraction.Rational)
    (positive : 0 < target) :
    (exact values).requestCenters target positive = values := by
  simp only [exact, ChannelTable.requestCenters, Map.map_map, -eq_self,
    -iff_self]
  calc
    _ = List.map id values := by
      apply Map.map_congr_left
      intro value _member
      exact sharedName_exact_center
        (List.map
          Coherence.exact values)
        value target positive
    _ = values := by
      induction values with
      | nil => rfl
      | cons value values inductionHypothesis =>
          rw [List.map_cons, inductionHypothesis]
          rfl

end ChannelTable

end Purelib.Approximation.Gaussian.Table.Basic

end
