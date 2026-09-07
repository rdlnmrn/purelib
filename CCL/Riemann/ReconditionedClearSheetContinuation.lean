import CCL.Riemann.ClearSheetContinuation
import CCL.Riemann.SquareRootTrackEquivalence

/-!
# Reconditioned continuation on a clear segment

The earlier local checker transports an owner by Rouché.  This file adds the
essential endpoint reset: after every accepted edge, the transported owner is
assigned to a fresh independently isolated endpoint owner through an explicit
same-occurrence bridge.  Consequently the next edge uses fresh endpoint
clearance rather than a box nested forever inside the first owner.
-/

namespace CCL.Riemann.ReconditionedClearSheetContinuation

open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint

/-- The same-occurrence target owner before it is reset to the independently
isolated endpoint frame. -/
def transported {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  CCL.Riemann.ClearSheetContinuation.advance segment within left right
    leftInside rightInside owner small

/-- The finite overlap certificate which justifies resetting this transported
owner at the endpoint. -/
def stepBridge {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    CCL.Riemann.SquareRootReconditioning.Bridge
      (segment.pointAt_eval_ne_zero right rightInside)
      (transported segment within left right leftInside rightInside owner
        small) :=
  CCL.Riemann.SquareRootReconditioning.bridge
    (segment.pointAt_eval_ne_zero right rightInside)
    (transported segment within left right leftInside rightInside owner small)

/-- Reset to the globally isolated owner selected by the finite overlap
certificate.  This is the owner inherited by the next edge. -/
def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : CCL.Riemann.ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  CCL.Riemann.SquareRootReconditioning.freshOwner
    (segment.pointAt_eval_ne_zero right rightInside)
    (transported segment within left right leftInside rightInside owner small)

/-- A finite continuation whose every recursive tail starts from a fresh
global endpoint owner.  `stepBridge` computes the finite proof that each reset
does not change the analytic sheet. -/
inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Coordinate) →
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1) →
      Owner (polynomial.eval (segment.pointAt left)) → Type
  | stop (left : Coordinate)
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
      (owner : Owner (polynomial.eval (segment.pointAt left))) :
      Subdivision segment within left leftInside owner
  | next (left : Coordinate)
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
      (owner : Owner (polynomial.eval (segment.pointAt left)))
      (right : Coordinate)
      (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
      (small : CCL.Riemann.ClearSheetContinuation.variationBound
        segment left right < owner.track.initial.clearance.bound)
      (remaining : Subdivision segment within right rightInside
        (advance segment within left right leftInside rightInside owner small)) :
      Subdivision segment within left leftInside owner

namespace Subdivision

def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Endpoint
  | .stop left leftInside _ => ⟨left, leftInside⟩
  | .next _ _ _ _ _ _ remaining => remaining.endpoint

def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Owner (polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter))
  | .stop _ _ owner => owner
  | .next _ _ _ _ _ _ remaining => remaining.terminalOwner

def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Nat
  | .stop _ _ _ => 0
  | .next _ _ _ _ _ _ remaining => remaining.stepCount + 1

/-- Check a proposed finite mesh and recondition after every successful
edge. -/
def trySamples {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (remaining : List Endpoint) →
      Option (Subdivision segment within current.parameter current.inside owner)
  | [] => some (.stop current.parameter current.inside owner)
  | nextPoint :: rest =>
      if small : CCL.Riemann.ClearSheetContinuation.variationBound
          segment current.parameter nextPoint.parameter <
            owner.track.initial.clearance.bound then
        match trySamples segment within nextPoint
            (advance segment within current.parameter nextPoint.parameter
              current.inside nextPoint.inside owner small) rest with
        | none => none
        | some tail => some (.next current.parameter current.inside owner
            nextPoint.parameter nextPoint.inside small tail)
      else none

@[simp] theorem trySamples_nil {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    trySamples segment within current owner [] =
      some (.stop current.parameter current.inside owner) := rfl

theorem trySamples_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (remaining : List Endpoint)
    {subdivision : Subdivision segment within current.parameter
      current.inside owner}
    (success : trySamples segment within current owner remaining =
      some subdivision) :
    subdivision.stepCount = remaining.length := by
  induction remaining generalizing current owner subdivision with
  | nil =>
      simp only [trySamples] at success
      cases success
      rfl
  | cons nextPoint rest inductionHypothesis =>
      simp only [trySamples] at success
      split at success
      next small =>
        split at success
        next recursiveFailure => contradiction
        next tail recursiveSuccess =>
          cases success
          simp only [stepCount, List.length_cons]
          exact congrArg Nat.succ
            (inductionHypothesis nextPoint
              (advance segment within current.parameter nextPoint.parameter
                current.inside nextPoint.inside owner small)
              (subdivision := tail) recursiveSuccess)
      next notSmall => contradiction

/-- Reuse the exact dyadic mesh constructor from the local checker. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) :
    Option (Subdivision segment within left.parameter left.inside owner) :=
  trySamples segment within left owner
    (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets
      depth left right)

theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat)
    {subdivision : Subdivision segment within left.parameter left.inside owner}
    (success : tryDyadic segment within left right owner depth =
      some subdivision) :
    subdivision.stepCount = 2 ^ depth := by
  exact (trySamples_stepCount segment within left owner
    (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets
      depth left right) success).trans
      (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length
        depth left right)

/-- The reconditioned mesh and its geometric path are definitionally aligned. -/
def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      ClearPath polynomial ambient (segment.pointAt left)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop left _ _ => .nil (segment.pointAt left)
  | .next left leftInside _ right rightInside _ remaining =>
      .cons
        (segment.restrict within left right leftInside rightInside)
        remaining.toClearPath

theorem toClearPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.WithinAmbient := by
  induction subdivision with
  | stop => exact .nil _
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact .cons
        (segment.restrict_withinAmbient within left right leftInside rightInside)
        inductionHypothesis

@[simp] theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.segmentCount = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end Subdivision

end CCL.Riemann.ReconditionedClearSheetContinuation
