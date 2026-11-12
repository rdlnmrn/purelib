module

public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Requested-time readings of retained root preparations

A reading traverses the original finite preparation. Endpoints and join
parameters reuse their stored owners; an interior leaf point advances that
leaf's original source using its already retained whole-interval payment.
The original first-box comparison certifies every returned owner internally.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.RootContinuation.FixedRootBoxBudget

variable {firstSource secondSource : Gaussian} {firstOwner : Owner firstSource} {secondOwner : Owner secondSource}
variable {first : Budget firstOwner} {second : Budget secondOwner} {path : PathData first second}

namespace Prepared

/-- Every preparation retains the original first-budget source at its exact left parameter. -/
theorem source_eq : ∀ {left right leftInside rightInside source target}
    (_prepared : Prepared path left right leftInside rightInside source target),
    source = path.First left leftInside
  | _, _, _, _, _, _, .step move => move.source_eq
  | _, _, _, _, _, _, .join _ firstHalf _ => firstHalf.source_eq

/-- Every preparation retains the original first-budget target at its exact right parameter. -/
theorem target_eq : ∀ {left right leftInside rightInside source target}
    (_prepared : Prepared path left right leftInside rightInside source target),
    target = path.First right rightInside
  | _, _, _, _, _, _, .step move => move.target_eq
  | _, _, _, _, _, _, .join _ _ secondHalf => secondHalf.target_eq

/-- The actual final advanced owner refines the same original first-source box. -/
theorem finishOwner_refines : ∀ {left right leftInside rightInside source target}
    (prepared : Prepared path left right leftInside rightInside source target),
    prepared.finishOwner.track.initial.box.Refines firstOwner.track.initial.box
  | _, right, _, rightInside, source, _, .step move => by
      have nested := source.advance_initial_box_refines (path.nonzero right rightInside) move.pointSmall
      have sourceBox : source.track.initial.box = firstOwner.track.initial.box := by
        rewrite [move.source_eq, path.first_box]
        rfl
      change move.advanced.track.initial.box.Refines firstOwner.track.initial.box
      rewrite [move.advanced_eq, move_eq_advance]
      exact Eq.mp (congrArg (fun box =>
        (source.advance (path.nonzero right rightInside) move.pointSmall).track.initial.box.Refines box)
          sourceBox) nested
  | _, _, _, _, _, _, .join _ _ secondHalf => secondHalf.finishOwner_refines

end Prepared

set_option genInjectivity false in
/-- A cached actual root reading at one exact requested parameter of the original path.

The returned owner keeps its original refinement witness into the first
source box. This is a trace query result, retaining an owner rather than
replacing its name by a sampler or re-isolating a root.
-/
structure Reading (path : PathData first second) (time : Coordinate) where
  /-- The complete actual owner at the exact requested path parameter. -/ owner : Owner (path.point time)
  /-- Its original initial box refines the retained first-source box. -/
  refines : owner.track.initial.box.Refines firstOwner.track.initial.box

constructive_injectivity Reading

namespace Reading

/-- Reindex one retained owner at an equal requested time, preserving its complete original box witness. -/
private def atOwner {endpoint time : Coordinate} (equal : endpoint = time)
    (owner : Owner (path.point endpoint))
    (refines : owner.track.initial.box.Refines firstOwner.track.initial.box) : Reading path time :=
  { owner := SquareRoot.Owner.Transport.castOwnerParameter (congrArg path.point equal) owner
    refines := by
      rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
      exact refines }

/-- Reuse an exact fixed-budget cache at the requested parameter. -/
private def atCache {endpoint time : Coordinate} (equal : endpoint = time) (inside : Inside endpoint)
    (owner : Owner (path.point endpoint)) (cache_eq : owner = path.First endpoint inside) : Reading path time :=
  atOwner equal owner (by rewrite [cache_eq, path.first_box]; exact Box.refines_refl _)

/-- Compare the retained queried owner with the separate original first-budget owner at the same requested time. -/
def agrees (reading : Reading path time) (inside : Inside time) :
    NamedEquivalent (ownerRootName reading.owner.parameterNonzero reading.owner)
      (ownerRootName (path.First time inside).parameterNonzero (path.First time inside)) :=
  (path.firstRetained time inside reading.owner reading.refines).symm

end Reading

namespace Prepared

/-- Query the original prepared trace, reusing its exact endpoint and middle caches.

Only an interior leaf reading performs an advance. Its displacement is paid
by that leaf's original whole-subinterval movement certificate and source
clearance; no preparation or root isolation is repeated.
-/
def read : ∀ {left right leftInside rightInside source target},
    Prepared path left right leftInside rightInside source target → (time : Coordinate) →
    left ≤ time ∧ time ≤ right → Reading path time
  | left, right, leftInside, rightInside, source, _, .step move, time, between =>
      if left_eq : left = time then
        Reading.atCache left_eq leftInside source move.source_eq
      else if right_eq : right = time then
        Reading.atOwner right_eq move.advanced (Prepared.finishOwner_refines (.step move))
      else
        let inside : Inside time := ⟨leftInside.1.trans between.1, between.2.trans rightInside.2⟩
        let small := (move.movement time between).trans_lt move.small
        let advanced := source.advance (path.nonzero time inside) small
        { owner := advanced
          refines := by
            have sourceBox : source.track.initial.box = firstOwner.track.initial.box := by
              rewrite [move.source_eq, path.first_box]
              rfl
            exact Eq.mp (congrArg (fun box => advanced.track.initial.box.Refines box) sourceBox)
              (source.advance_initial_box_refines (path.nonzero time inside) small) }
  | left, right, leftInside, _, source, _, .join _ firstHalf secondHalf, time, between =>
      if left_eq : left = time then
        Reading.atCache left_eq leftInside source firstHalf.source_eq
      else if right_eq : right = time then
        Reading.atOwner right_eq secondHalf.finishOwner secondHalf.finishOwner_refines
      else if middle_eq : _ = time then
        Reading.atCache middle_eq _ _ firstHalf.target_eq
      else if before : time ≤ _ then
        firstHalf.read time ⟨between.1, before⟩
      else
        secondHalf.read time ⟨(Fraction.Order.Arithmetic.le_of_lt_direct
          (Fraction.Order.Arithmetic.lt_of_not_ge_direct before)), between.2⟩

/-- A left-endpoint trace query returns the identical retained source owner. -/
theorem read_source {left right leftInside rightInside source target}
    (prepared : Prepared path left right leftInside rightInside source target) (ordered : left ≤ right) :
    (prepared.read left ⟨Fraction.Order.Basic.le_refl _, ordered⟩).owner = source := by
  cases prepared with
  | step move => simp only [read, dif_pos rfl, -eq_self, -iff_self]; rfl
  | join middle_eq firstHalf secondHalf => simp only [read, dif_pos rfl, -eq_self, -iff_self]; rfl

/-- A distinct right-endpoint query returns the identical actual final advanced owner before its cached handoff. -/
theorem read_finish {left right leftInside rightInside source target}
    (prepared : Prepared path left right leftInside rightInside source target)
    (ordered : left ≤ right) (different : left ≠ right) :
    (prepared.read right ⟨ordered, Fraction.Order.Basic.le_refl _⟩).owner = prepared.finishOwner := by
  cases prepared with
  | step move => simp only [read, dif_neg different, dif_pos rfl, -eq_self, -iff_self]; rfl
  | join middle_eq firstHalf secondHalf =>
      simp only [read, dif_neg different, dif_pos rfl, -eq_self, -iff_self]
      rfl

end Prepared

namespace Result

/-- Query the retained complete preparation at an exact unit-interval parameter. -/
def read (result : Result path) (time : Coordinate) (inside : Inside time) : Reading path time :=
  result.prepared.read time inside

/-- The complete preparation's starting query retains its original cached source. -/
theorem read_source (result : Result path) :
    (result.read 0 (by decide +kernel)).owner = result.source :=
  result.prepared.read_source (by decide +kernel)

/-- The complete preparation's terminal query retains its actual final advanced owner. -/
theorem read_finish (result : Result path) :
    (result.read 1 (by decide +kernel)).owner = result.finishOwner :=
  result.prepared.read_finish (by decide +kernel) (by decide +kernel)

end Result

end Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
