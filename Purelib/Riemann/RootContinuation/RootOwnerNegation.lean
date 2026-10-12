module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

public import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.RootContinuation.RootOwnerFrames
public import Purelib.Riemann.RootContinuation.SquareRootNegation
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

public section

/-!
# The other retained owner is the negative root

Localize the negative of one actual root channel once and classify its
occurrence in the existing complete frame. Apartness excludes its original
index, so the classification identifies the other retained owner. Both
localization and classification caches remain available to later requests.
-/

namespace Purelib.Riemann.RootContinuation.RootOwnerNegation

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (NameSelection OwnerSelection OccurrenceFrame OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (Coordinate)

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Branches in
set_option genInjectivity false in
/-- A negated source channel attached to an original owner and selected on the opposite sheet.

The retained attachment and name selection share the same original parameter; the stored index equation identifies the
actual opposite-sheet selection. -/
structure NamedNegation (names : Fin 2 → Name.Basic.Named)
    (name : Owner parameter → Name.Basic.Named) (index : Fin 2) where
  /-- The retained root owner attached to the negation of the original selected name. -/ attachment :
    SquareRootChannelOwnership.OwnerNameAttachment parameter name
    (Name.Basic.Named.neg (names index))
  /-- The exact original name-family selection of that attached owner. -/ selection : NameSelection names (name
    attachment.owner)
  /-- The selected original index is the opposite sheet of the source index. -/ index_eq : selection.index =
    BranchCutLifts.otherSheet index

constructive_injectivity NamedNegation

/-- Negation evidence indexed by the original owner frame and source sheet. -/
abbrev Negation (frame : OwnerFrame parameter) (index : Fin 2) :=
  NamedNegation (parameter := parameter) (fun sheet => ownerName (frame.owners sheet))
    (@ownerName parameter) index

open Purelib.Riemann.RootContinuation in
/-- Attach the negated original framed channel and certify selection of the opposite sheet.

The actual attachment and frame selection are retained, and apartness rules out selection of the original sheet. -/
@[expose] def negation (frame : OwnerFrame parameter) (index : Fin 2) : Negation frame index := by
  let source := (frame.owners index).certificate (frame.owners index).parameterNonzero
  let attachment := SquareRootChannelOwnership.attach (SquareRootNegation.Certificate.neg source)
  let selection := frame.select attachment.owner
  have different : selection.index ≠ index := by
    intro same
    have equivalent := attachment.equivalent.trans selection.equivalent
    rw [same] at equivalent
    exact SquareRootNegation.apart_not_neg source.value source.apart equivalent.symm
  have values : selection.index.val ≠ index.val := fun same => different (Fin.ext same)
  have firstBound := index.isLt
  have lastBound := selection.index.isLt
  refine ⟨attachment, selection, ?_⟩
  apply Fin.ext
  change selection.index.val = 1 - index.val
  omega0

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Branches in
/-- The negated original frame owner's name is equivalent to its retained opposite-sheet name. -/
@[expose] def Negation.equivalent {frame : OwnerFrame parameter} {index : Fin 2}
    (data : Negation frame index) :
    Equivalence.NamedEquivalent (Name.Basic.Named.neg (ownerName (frame.owners index)))
      (ownerName (frame.owners (BranchCutLifts.otherSheet index))) := by
  have equivalent := data.attachment.equivalent.trans data.selection.equivalent
  simpa only [data.index_eq] using equivalent

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- A common retained sampling stage controlling the sum of two original names.

All later sample pairs have squared norm below the original target, and the selected stage remains above the supplied
starting index. -/
structure SumRequest (first second : Name.Basic.Named)
    (start : Nat) (target : Coordinate) where
  /-- The retained common sample stage for the two original names. -/ index : Nat
  /-- The selected stage is at least the original requested starting index. -/ later : start ≤ index
  /-- Every pair of samples after that stage has squared sum norm below the original target. -/ accurate : ∀ left right,
    index ≤ left → index ≤ right →
    normSq ((Name.Sampling.approximation first).sample left +
      (Name.Sampling.approximation second).sample right) < target

constructive_injectivity SumRequest

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The negated-channel difference has the same squared norm as the corresponding original-channel sum. -/
public theorem neg_difference_norm (first : Name.Coherent.CoherentNamed)
    (second : Name.Basic.Named) (left right : Nat) :
    normSq ((Name.Sampling.approximation first.neg.name).sample left -
      (Name.Sampling.approximation second).sample right) =
    normSq ((Name.Sampling.approximation first.name).sample left +
      (Name.Sampling.approximation second).sample right) := by
  rw [SquareRootNegation.neg_sample]
  have identity (a b : Basic.Canonical) : -a - b = -(a + b) := by ring1
  rw [identity]
  rw [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_neg, Norm.Basic.normSq_eq_canonical]

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- Acquire a common sample stage from the original negative-name equivalence.

The maximum of the two retained comparison indices meets the requested floor and controls every later sum using the
exact original samples. -/
@[expose] public def requestFromEquivalent (first : Name.Coherent.CoherentNamed)
    (second : Name.Basic.Named)
    (equivalent : Equivalence.NamedEquivalent first.neg.name second)
    (start : Nat) (target : Coordinate) (positive : 0 < target) :
    SumRequest first.name second start target := by
  let comparison := equivalent.compare start start target positive
  refine ⟨max comparison.leftIndex comparison.rightIndex,
    comparison.left_ge.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro left right leftOrder rightOrder
  have close := comparison.close
    ((Nat.Order.le_max_left _ _).trans leftOrder) ((Nat.Order.le_max_right _ _).trans rightOrder)
  rw [Norm.Basic.normSq_eq_canonical] at close
  exact (neg_difference_norm _ _ left right) ▸ close

open Purelib.Curves.Hyperelliptic.Branches in
/-- Request a small sum for the original framed owner and its retained opposite-sheet owner. -/
@[expose] def Negation.request {frame : OwnerFrame parameter} {index : Fin 2}
    (data : Negation frame index) (start : Nat) (target : Coordinate) (positive : 0 < target) :
    SumRequest (ownerName (frame.owners index))
      (ownerName (frame.owners (BranchCutLifts.otherSheet index))) start target :=
  requestFromEquivalent
    ((frame.owners index).certificate (frame.owners index).parameterNonzero).value
    (ownerName (frame.owners (BranchCutLifts.otherSheet index)))
    data.equivalent start target positive

end Purelib.Riemann.RootContinuation.RootOwnerNegation
