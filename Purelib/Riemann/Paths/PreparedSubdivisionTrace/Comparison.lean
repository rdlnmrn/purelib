module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
public import Purelib.Riemann.Integration.PreparedConstantModels.RootPath
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic

/-! # Cached root comparisons through one original retained subdivision

Each accepted original request retains its actual three-link trace view,
one local two-budget RootPath and one shared fixed-box endpoint Owner. The
cache recurses on the identical stored following subdivision and actual
trace suffix. Its comparison fold derives agreement with the original
terminal Owner, including every actual reserve-retention handoff.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (edgeOfStep edgeOfStep_point)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {genus : Nat} (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} (budget : PreparedTraceBudget segment first last) (sheet : Fin 2)
    {source : Canonical} {sourceOwner : Owner source} (second : FixedRootBoxBudget.Budget sourceOwner)
    (movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (source - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement)

include movement in
/-- The original whole-segment movement bound specializes to the exact accepted original request edge. -/
theorem movement_on_edge (current : Endpoint)
    (inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (cached : CachedSource segment current inherited request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound)
    (time : Rational) (inside : Inside time) :
    Norm.Basic.normSq (source - curve.polynomial.eval
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).point
        time)) ≤
      second.movement := by
  rewrite [edgeOfStep_point]
  exact movement (PreparedSheetContinuation.parameterAt current request time)
    (PreparedSheetContinuation.parameterAt_inside current request ordered time inside)

/-- One actual fixed-box endpoint Owner and its entire original factory identity.

The factory occurs only in the correctness field. Cache builders materialize
its Owner once, and later comparisons read that same retained occurrence.
-/
@[expose] def Reference (endpoint : Endpoint) :=
  { owner : Owner (curve.polynomial.eval (segment.pointAt endpoint.parameter)) //
    owner = second.ownerAt
      (segment.pointAt_eval_ne_zero endpoint.parameter endpoint.inside)
      (by
        have bounded := movement endpoint.parameter endpoint.inside
        rewrite [Norm.Basic.normSq_eq_canonical] at bounded
        exact bounded) }

namespace Reference

variable {curve differential budget sheet second movement}

/-- Construct one shared independent reference on the literal original request endpoint. -/
def build (endpoint : Endpoint) : Reference curve second movement endpoint :=
  ⟨second.ownerAt (segment.pointAt_eval_ne_zero endpoint.parameter endpoint.inside)
    (by
      have bounded := movement endpoint.parameter endpoint.inside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded), rfl⟩

/-- The cached endpoint reference retains the same complete original fixed box. -/
theorem refines {endpoint : Endpoint} (reference : Reference curve second movement endpoint) :
    reference.val.track.initial.box.Refines sourceOwner.track.initial.box := by
  rewrite [reference.property, FixedRootBoxBudget.Budget.ownerAt_box]
  exact Geometry.Rational.Box.refines_refl _

/-- The cached fixed-box endpoint reference keeps exactly the original independent budget box. -/
theorem box {endpoint : Endpoint} (reference : Reference curve second movement endpoint) :
    reference.val.track.initial.box = sourceOwner.track.initial.box := by
  rewrite [reference.property]
  exact FixedRootBoxBudget.Budget.ownerAt_box _ _ _

end Reference

/-- The cache spine follows the exact original subdivision and actual materialized trace.

A nonempty entry stores one actual trace view, one original-edge RootPath
and one reference Owner. Its following cache consumes the identical stored
subdivision and literal actual tail. No original source preparation, moving continuation, reserve retention
or mesh factory is replayed by the cache construction.
-/
@[expose] def Cache : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited)
    (fits : budget.RequestsFit current subdivision.requests)
    (_trace : Trace budget subdivision fits), Type
  | _, _, .stop _ _, _, _ => PUnit
  | _, _, .next current inherited request cached ordered small remaining, fits, trace =>
      (view : Trace.View budget current inherited request cached ordered small remaining fits trace) ×
      (_path : Integration.PreparedConstantModels.PreparedEdge.RootPath
        (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
        second (movement_on_edge curve differential sheet second movement
          current inherited request cached ordered small)) ×
      (_next : Reference curve second movement request.endpoint) ×
      Cache remaining fits.2.2 view.tailTrace
termination_by structural _ _ subdivision _ _ => subdivision

namespace Cache

variable {curve differential budget sheet second movement}

/-- Materialize local comparison paths and shared references once on the SAME retained subdivision and trace. -/
def build {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current inherited)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : Trace budget subdivision fits) :
    Cache curve differential budget sheet second movement subdivision fits trace :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      Cache curve differential budget sheet second movement subdivision fits trace)
    subdivision
    (fun _ _ _ _ => PUnit.unit)
    (fun current inherited request cached ordered small remaining fits trace =>
      let view := Trace.View.build trace
      let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
      let path := Integration.PreparedConstantModels.PreparedEdge.RootPath.build edge second
        (movement_on_edge curve differential sheet second movement current inherited request cached ordered small)
      let next : Reference curve second movement request.endpoint := Reference.build request.endpoint
      let tail := build remaining fits.2.2 view.tailTrace
      ⟨view, path, next, tail⟩)
    fits trace
termination_by structural subdivision

/-- Read the final retained independent reference without executing any reference factory. -/
def finishReference : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
    Cache curve differential budget sheet second movement subdivision fits trace →
    Owner (curve.polynomial.eval (segment.pointAt current.parameter)) →
    Owner (curve.polynomial.eval (segment.pointAt subdivision.endpoint.parameter))
  | _, _, .stop _ _, _, _, _, reference => reference
  | _, _, .next _ _ _ _ _ _ _, _, _, retained, _ => retained.2.2.2.finishReference retained.2.2.1.val
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- The final shared reference refines the original independent budget box. -/
theorem finishReference_refines : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter))),
    reference.track.initial.box.Refines sourceOwner.track.initial.box →
    (retained.finishReference reference).track.initial.box.Refines sourceOwner.track.initial.box
  | _, _, .stop _ _, _, _, _, _, refines => refines
  | _, _, .next _ _ _ _ _ _ _, _, _, retained, _, _ =>
      retained.2.2.2.finishReference_refines retained.2.2.1.val retained.2.2.1.refines
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- An exact original-box starting reference leaves that same box at the cached final reference. -/
theorem finishReference_box : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter))),
    reference.track.initial.box = sourceOwner.track.initial.box →
    (retained.finishReference reference).track.initial.box = sourceOwner.track.initial.box
  | _, _, .stop _ _, _, _, _, _, same => same
  | _, _, .next _ _ _ _ _ _ _, _, _, retained, _, _ =>
      retained.2.2.2.finishReference_box retained.2.2.1.val retained.2.2.1.box
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

section RetainedComparisonTypes

/- Keep the original named relation and root-name constructors intact while
   the dependent stop/next equations compare their stored Owner inputs. -/
attribute [local irreducible] NamedEquivalent ownerRootName

/-- Propagate an actual starting comparison to the original stored terminal Owner.

The original moving Owner comes from the stored three-link trace view;
the actual advanced Owner is the SAME following subdivision's sourceOwner.
The existing local RootPath comparison pays every step, including reserve
reconditioning, then consumes the identical cached tail. No finish
agreement is an input and no advancement is rerun.
-/
def equivalent : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (reference : Owner (curve.polynomial.eval (segment.pointAt current.parameter)))
    (_refines : reference.track.initial.box.Refines sourceOwner.track.initial.box),
    NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
      (ownerRootName reference.parameterNonzero reference) →
    NamedEquivalent (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner)
      (ownerRootName (retained.finishReference reference).parameterNonzero (retained.finishReference reference))
  | _, _, .stop _ _, _, _, _, _, _, initial => initial
  | _, _, .next _ _ _ _ _ _ remaining, _, _, retained, reference, refines, initial =>
      let compared := retained.2.1.advanceEquivalent reference refines retained.2.2.1.val retained.2.2.1.refines
        initial retained.1.movingOwner retained.1.movingOwner_eq
        remaining.sourceOwner remaining.sourceOwner_eq
      let tailInitial := Eq.mp (congrArg
        (fun owner => NamedEquivalent (ownerRootName owner.parameterNonzero owner)
          (ownerRootName retained.2.2.1.val.parameterNonzero retained.2.2.1.val))
        remaining.sourceOwner_eq) compared
      retained.2.2.2.equivalent retained.2.2.1.val retained.2.2.1.refines tailInitial
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

end RetainedComparisonTypes

end Cache

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison

end
