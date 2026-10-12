module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic

@[expose] public section

/-!
# Reconditioned continuation on a clear segment

The earlier local checker transports an owner by Rouché.  This file adds the
essential endpoint reset: after every accepted edge, the transported owner is
assigned to a fresh independently isolated endpoint owner through an explicit
same-occurrence bridge.  Consequently the next edge uses fresh endpoint
clearance rather than a box nested forever inside the first owner.
-/

namespace Purelib.Riemann.Branches.ReconditionedClearSheetContinuation

open Purelib.Data.Rat in
/-- The exact rational segment-parameter carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A retained segment parameter certified to lie in the unit interval. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Continue the exact original owner between the supplied cleared-segment parameters. -/
def transported {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  ClearSheetContinuation.advance segment within left right
    leftInside rightInside owner small

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
/-- Retain the comparison bridge for the exact owner produced by this continuation step. -/
def stepBridge {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    SquareRootReconditioning.Bridge
      (segment.pointAt_eval_ne_zero right rightInside)
      (transported segment within left right leftInside rightInside owner
        small) :=
  SquareRootReconditioning.bridge
    (segment.pointAt_eval_ne_zero right rightInside)
    (transported segment within left right leftInside rightInside owner small)

/-- Read the fresh isolated owner assigned to the exact transported endpoint owner.

The original segment, source owner and variation witness determine the transported owner; its reconditioning assignment
selects the retained endpoint sheet. -/
def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
    (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : ClearSheetContinuation.variationBound
      segment left right < owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  SquareRootReconditioning.freshOwner
    (segment.pointAt_eval_ne_zero right rightInside)
    (transported segment within left right leftInside rightInside owner small)

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A finite cleared-segment subdivision retaining the exact reconditioned owner after each step.

Each tail starts at the fresh owner assigned by the preceding certified continuation, preserving the dependent endpoint
and original segment. -/
inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Coordinate) →
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1) →
      Owner (polynomial.eval (segment.pointAt left)) → Type
  /-- Stop at the exact current parameter and its retained square-root owner. -/ | stop (left : Coordinate)
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
      (owner : Owner (polynomial.eval (segment.pointAt left))) :
      Subdivision segment within left leftInside owner
  /-- Retain one certified step and the tail indexed by its actual reconditioned endpoint owner. -/ | next (left :
    Coordinate)
      (leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1)
      (owner : Owner (polynomial.eval (segment.pointAt left)))
      (right : Coordinate)
      (rightInside : (0 : Coordinate) ≤ right ∧ right ≤ 1)
      (small : ClearSheetContinuation.variationBound
        segment left right < owner.track.initial.clearance.bound)
      (remaining : Subdivision segment within right rightInside
        (advance segment within left right leftInside rightInside owner small)) :
      Subdivision segment within left leftInside owner

constructive_injectivity Subdivision

namespace Subdivision

section
open Purelib.Polynomial
/-- Read the exact terminal parameter of the retained reconditioned subdivision. -/
def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Endpoint
  | .stop left leftInside _ => ⟨left, leftInside⟩
  | .next _ _ _ _ _ _ remaining => remaining.endpoint

/-- Read the retained final owner indexed by the polynomial value at the exact terminal parameter. -/
def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Owner (polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter))
  | .stop _ _ owner => owner
  | .next _ _ _ _ _ _ remaining => remaining.terminalOwner

/-- Count the retained continuation-and-reconditioning steps. -/
def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Nat
  | .stop _ _ _ => 0
  | .next _ _ _ _ _ _ remaining => remaining.stepCount + 1

open Purelib.Riemann.Branches in
/-- Attempt continuation and reconditioning through the supplied retained parameter list.

Each successful comparison advances the exact current owner before checking the remaining samples. Failure means a
sufficient variation bound did not pass. -/
def trySamples {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (remaining : List Endpoint) →
      Option (Subdivision segment within current.parameter current.inside owner)
  | [] => some (.stop current.parameter current.inside owner)
  | nextPoint :: rest =>
      if small : ClearSheetContinuation.variationBound
          segment current.parameter nextPoint.parameter <
            owner.track.initial.clearance.bound then
        match trySamples segment within nextPoint
            (advance segment within current.parameter nextPoint.parameter
              current.inside nextPoint.inside owner small) rest with
        | none => none
        | some tail => some (.next current.parameter current.inside owner
            nextPoint.parameter nextPoint.inside small tail)
      else none

/-- An empty target list returns the stopped subdivision at the original current owner. -/
@[simp] theorem trySamples_nil {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    trySamples segment within current owner [] =
      some (.stop current.parameter current.inside owner) := rfl

/-- A successful sample-list attempt retains exactly one step per supplied sample. -/
theorem trySamples_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
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

section
open Purelib.Riemann.Branches
/-- Attempt reconditioned continuation along the original exact dyadic target list. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) :
    Option (Subdivision segment within left.parameter left.inside owner) :=
  trySamples segment within left owner
    (ClearSheetContinuation.Subdivision.dyadicTargets
      depth left right)

/-- A successful depth-d dyadic attempt contains exactly two to the power d steps. -/
theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
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
    (ClearSheetContinuation.Subdivision.dyadicTargets
      depth left right) success).trans
      (ClearSheetContinuation.Subdivision.dyadicTargets_length
        depth left right)

end

/-- Read the retained parameter steps as restrictions of the original cleared segment. -/
def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop left _ _ => .nil (segment.pointAt left)
  | .next left leftInside _ right rightInside _ remaining =>
      .cons
        (segment.restrict within left right leftInside rightInside)
        remaining.toClearPath

/-- The geometric path read from the subdivision remains in the original ambient box. -/
theorem toClearPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
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

/-- The geometric path preserves the exact number of retained subdivision steps. -/
@[simp] theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
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

end

end Subdivision

end Purelib.Riemann.Branches.ReconditionedClearSheetContinuation
