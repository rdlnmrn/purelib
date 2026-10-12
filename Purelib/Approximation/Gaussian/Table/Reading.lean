module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.Request
public import Purelib.Data.Gaussian.List.Proximity

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Table

open Purelib.Data.Gaussian.List

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite error transport for progressive Taylor tables

The progressive higher-jet layer emits every displayed coefficient.  This
module transports those finitely many coefficient allowances through Horner
evaluation and through an explicit finite truncation.  The bounds are coarse
recursive rational expressions; no omitted infinite tail or formal power
series is introduced.
-/

namespace Purelib.Approximation.Gaussian.Table.Reading

/-! ## Connecting shared progressive requests to the finite relation -/

/-- Read the enclosure center of a channel after the request computed from the retained finite budget list. -/
def sharedCenter (budget : List CoherentNamed) (channel
  : CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) : Canonical :=
  let named := Request.sharedName
    budget channel target positive
  (named.process.ball named.state).center

set_option backward.match.sparseCases false in
/-- Entrywise possibility of a finite reading list after one shared table request.

Each reading belongs to its original channel's refined state, and the recursive relation requires the channel and
reading lists to have the same length. -/
def SharedReadingsPossible (budget : List
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) :
    (channels : List Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) → (readings : List
      Canonical) →
      (target : Purelib.Data.Rat.Fraction.Rational) → 0 < target → Prop
  | [], [], _target, _positive => True
  | channel :: channels, reading :: readings, target, positive =>
      let named := Purelib.Approximation.Gaussian.Table.Request.sharedName
        budget channel target positive
      named.process.Possible named.state reading ∧
        SharedReadingsPossible budget channels readings target positive
  | _, _, _target, _positive => False

/-- Read each displayed channel's enclosure center after the same retained finite-table request. -/
def sharedCenters (budget channels : List
  CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) : List Canonical :=
  channels.map (fun channel => sharedCenter budget channel target positive)

/-- Every possible finite shared reading list is entrywise close to its corresponding cached centers within the
displayed positive target. -/
theorem sharedReadings_close : ∀ (budget channels : List
  CoherentNamed)
    (readings : List Canonical) (target : Fraction.Rational)
    (positive : 0 < target),
    SharedReadingsPossible budget channels readings target positive →
      Proximity.EntriesClose readings (sharedCenters budget channels target
        positive)
        target
  | budget, [], [], target, positive, _possible => trivial
  | budget, [], _ :: _, target, positive, possible => by
      simp only [SharedReadingsPossible] at possible
  | budget, _ :: _, [], target, positive, possible => by
      simp only [SharedReadingsPossible] at possible
  | budget, channel :: channels, reading :: readings, target, positive,
      possible => by
      rcases possible with ⟨headPossible, tailPossible⟩
      constructor
      · let named := Request.sharedName
          budget channel target positive
        exact (named.process.possible_inside headPossible).trans
          (Request.sharedName_radius_lt
            budget channel positive).le
      · exact sharedReadings_close budget channels readings target positive
          tailPossible
end Purelib.Approximation.Gaussian.Table.Reading

end
