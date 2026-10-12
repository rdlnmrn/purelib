module

-- Exposed finite-window builders retain the original subtraction reconstruction.
public import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.List.OfFn.Basic
public import Purelib.Data.List.OfFn.Pairwise
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Cylinder.TwoParameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Parameter
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Transition
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Data.Nat.Basic
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Arbitrarily long finite same-source critical runs

This module reindexes the transported Pell normal forms around one explicitly
chosen rational source.  Given a sharper rational threshold, a requested
scale, and a finite count, it returns exactly that many bad windows.  Their
source is definitionally shared and their upper denominator quadrances are
pairwise strictly increasing in list order.

Only the supplied finite list is constructed.  No completed critical source,
infinite orbit, limit, or almost-everywhere assertion is introduced.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run

set_option genInjectivity false in
/-- A finite list of existing `BadWindow` records indexed by one definitionally
shared source, together with exact length and strict scale-growth data. -/
structure SameSourceBadWindowRun
    (threshold : Fraction.Rational) (requestedScale count : Nat) where
  /-- The common rational Gaussian source of every retained window. -/ source : GaussianInt.Fraction
  /-- The displayed bad windows, each retaining equality with the common source. -/ windows : List
    { window : Sharpness.BadWindow threshold requestedScale // window.source = source }
  /-- The list has exactly the requested number of windows. -/ length_eq : windows.length = count
  /-- Upper endpoint denominator quadrances increase strictly in list order. -/ scalesStrict : windows.Pairwise fun
    earlier later =>
    Best.Error.denominatorQuadrance earlier.1.upper <
      Best.Error.denominatorQuadrance later.1.upper

constructive_injectivity SameSourceBadWindowRun

/-- Earliest error-parameter stage used by the finite run. -/
@[expose] def runBaseStage (threshold : Fraction.Rational) (requestedScale : Nat) : Nat :=
  Dirichlet.Critical.Sharpness.sharpnessStage threshold requestedScale

/-- The common rational source is moved forward by the requested count so
all backward error parameters remain beyond the sharpness stage. -/
@[expose] def runSourceStage
    (threshold : Fraction.Rational) (requestedScale count : Nat) : Nat :=
  Dirichlet.Critical.Run.runBaseStage threshold requestedScale + count

/-- Exact transported normal form underlying one bounded offset of the
same-source run. -/
@[expose] def normalFormAtOffset
    (threshold : Fraction.Rational) (requestedScale count offset : Nat)
    (offsetBound : offset ≤ count) :
    Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
      (Dirichlet.Critical.Pair.criticalSource
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count))
      (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count - offset)
      (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count + offset) := by
  let sourceStage := Dirichlet.Critical.Run.runSourceStage threshold requestedScale count
  have offsetLeSource : offset ≤ sourceStage := by
    dsimp only [sourceStage, Dirichlet.Critical.Run.runSourceStage, Dirichlet.Critical.Run.runBaseStage]
    exact offsetBound.trans (Nat.le_add_left count _)
  have sourceIdentity : (sourceStage - offset) + offset = sourceStage :=
    Subtraction.sub_add_cancel offsetLeSource
  have targetIdentity :
      (sourceStage - offset) + 2 * offset = sourceStage + offset := by
    calc
      (sourceStage - offset) + 2 * offset =
          ((sourceStage - offset) + offset) + offset := by ring1
      _ = sourceStage + offset := by rw [sourceIdentity]
  have normal :=
    Dirichlet.Critical.Adjacent.Tower.transportedNormalForm
      (sourceStage - offset) offset
  rw [sourceIdentity, targetIdentity] at normal
  exact normal

/-- The bad window at one bounded offset of the executable run. -/
@[expose] def badWindowAtOffset
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    { window : Sharpness.BadWindow threshold requestedScale //
      window.source = Dirichlet.Critical.Pair.criticalSource
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count) } := by
  let sourceStage := Dirichlet.Critical.Run.runSourceStage threshold requestedScale count
  let backwardStage := sourceStage - offset.val
  let targetStage := sourceStage + offset.val
  have offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  have normal :
      Dirichlet.Critical.Adjacent.Tower.TransportedNormalForm
        (Dirichlet.Critical.Pair.criticalSource sourceStage)
        backwardStage targetStage := by
    simpa only [sourceStage, backwardStage, targetStage] using
      Dirichlet.Critical.Run.normalFormAtOffset threshold requestedScale count offset.val offsetBound
  have baseLeBackward :
      Dirichlet.Critical.Run.runBaseStage threshold requestedScale ≤ backwardStage := by
    clear certificate normal
    dsimp only [backwardStage, sourceStage, Dirichlet.Critical.Run.runSourceStage]
    omega0
  have backwardLeTarget : backwardStage ≤ targetStage := by
    dsimp only [backwardStage, targetStage]
    exact (Nat.sub_le sourceStage offset.val).trans
      (Nat.le_add_right sourceStage offset.val)
  have gapStrict :
      Dirichlet.Critical.Cylinder.TwoParameter.gap
          (Dirichlet.Critical.Parameter.pellParameter backwardStage)
          (Dirichlet.Critical.Parameter.pellParameter targetStage) <
        threshold := by
    apply Dirichlet.Critical.Adjacent.Tower.transportedGap_lt_sharperThreshold
      certificate requestedScale backwardStage targetStage
    · simpa only [Dirichlet.Critical.Run.runBaseStage] using baseLeBackward
    · exact backwardLeTarget
  have baseLeTarget :
      Dirichlet.Critical.Run.runBaseStage threshold requestedScale ≤ targetStage :=
    baseLeBackward.trans backwardLeTarget
  have beyondScale : requestedScale < Best.Error.denominatorQuadrance
      (Dirichlet.Critical.Pair.criticalUpperPair targetStage) :=
    (Dirichlet.Critical.Sharpness.requestedScale_lt_criticalUpperDenominatorQuadrance
      threshold requestedScale).trans_le
      (Dirichlet.Critical.Transition.criticalUpper_denominatorQuadrance_le_of_le
        (by simpa only [Dirichlet.Critical.Run.runBaseStage] using baseLeTarget))
  exact
    ⟨{ source := Dirichlet.Critical.Pair.criticalSource sourceStage
       lower := Dirichlet.Critical.Pair.criticalLowerPair targetStage
       upper := Dirichlet.Critical.Pair.criticalUpperPair targetStage
       beyondScale := beyondScale
       consecutive := normal.strictExteriorCertificate.areConsecutiveBest
       violates := normal.one_lt_threshold_mul_window threshold gapStrict }, rfl⟩

/-- The offset window retains the critical upper pair at the common source stage plus its offset. -/
@[simp] theorem badWindowAtOffset_upper
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (Dirichlet.Critical.Run.badWindowAtOffset certificate requestedScale count offset).1.upper =
      Dirichlet.Critical.Pair.criticalUpperPair
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count + offset.val) := by
  rfl

/-- The offset window retains the critical lower pair at the common source stage plus its offset. -/
@[simp] theorem badWindowAtOffset_lower
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (Dirichlet.Critical.Run.badWindowAtOffset certificate requestedScale count offset).1.lower =
      Dirichlet.Critical.Pair.criticalLowerPair
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count + offset.val) := by
  rfl

/-- Executable arbitrary-length finite analogue of recurrent critical-window
sharpness: all returned bad windows use one rational source, lie beyond the
requested scale, and have strictly increasing upper scales. -/
@[expose] def criticalBadWindowRun
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    Dirichlet.Critical.Run.SameSourceBadWindowRun threshold requestedScale count := by
  refine
    { source := Dirichlet.Critical.Pair.criticalSource
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count)
      windows := List.ofFn
        (Dirichlet.Critical.Run.badWindowAtOffset certificate requestedScale count)
      length_eq := Data.List.OfFn.Basic.length_ofFn
      scalesStrict := ?_ }
  apply Data.List.OfFn.Pairwise.pairwise_ofFn_direct
  intro first second indexOrder
  rw [Dirichlet.Critical.Run.badWindowAtOffset_upper, Dirichlet.Critical.Run.badWindowAtOffset_upper]
  apply Dirichlet.Critical.Transition.criticalUpper_denominatorQuadrance_lt_of_lt
  exact Nat.add_lt_add_left indexOrder _

/-- The constructed run retains the critical source at its explicitly computed common stage. -/
@[simp] theorem criticalBadWindowRun_source
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (Dirichlet.Critical.Run.criticalBadWindowRun certificate requestedScale count).source =
      Dirichlet.Critical.Pair.criticalSource
        (Dirichlet.Critical.Run.runSourceStage threshold requestedScale count) := by
  rfl

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run

end
