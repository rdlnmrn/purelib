module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Owner.Transport

import Purelib.Riemann.Integration.PreparedSubdivisionModels
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Track.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Prepared models for finite clear paths

A clear path may contain several axis segments.  This module carries the
computed terminal square-root owner of each completely prepared segment into
the next one, concatenates the refined geometry, and folds the automatically
aligned uniform integration certificates over the whole finite path.
-/

namespace Purelib.Riemann.Paths.PreparedClearPathModels

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- A dense polynomial over canonical Gaussian rationals. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner at its retained radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A subdivision parameter with its original unit-interval bounds. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- A polynomial cell model with retained endpoints, observations and local allowance. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A coherent wedge-coefficient family certified equivalent to zero at each bounded parameter. -/
abbrev WedgeChart {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.WedgeChart curve leftDifferential
    rightDifferential
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The original dependent subdivision retaining its segment, starting endpoint and owner. -/
abbrev PreparedSubdivision {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  PreparedSheetContinuation.Subdivision segment within left owner

/-- The rational parameter zero with its unit-interval certificate. -/
def zeroEndpoint : Endpoint :=
  { parameter := 0
    inside := by decide }

/-- The rational parameter one with its unit-interval certificate. -/
def oneEndpoint : Endpoint :=
  { parameter := 1
    inside := by decide }

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Transport the original displayed-start owner to the segment's zero-parameter radicand.

The cast uses the exact segment start equation and preserves the original root track and owner data. -/
def ownerAtStart {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :
    Owner (polynomial.eval (segment.pointAt zeroEndpoint.parameter)) := by
  exact SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg polynomial.eval (by
      change start = segment.pointAt 0
      exact segment.pointAt_zero.symm)) owner

section
open Purelib.Polynomial
/-- Transport the zero-parameter owner back to the original displayed start radicand. -/
def ownerAtDisplayedStart {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval (segment.pointAt 0))) :
    Owner (polynomial.eval start) := by
  simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using owner

/-- The displayed-start transport preserves the owner up to heterogeneous equality. -/
theorem ownerAtDisplayedStart_heq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval (segment.pointAt 0))) :
    HEq (ownerAtDisplayedStart segment owner) owner := by
  unfold ownerAtDisplayedStart
  exact cast_heq _ _

end

open Purelib in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Transporting a zero-parameter owner to the displayed start and back returns the exact original owner. -/
theorem ownerAtStart_ownerAtDisplayedStart {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval (segment.pointAt 0))) :
    ownerAtStart segment (ownerAtDisplayedStart segment owner) = owner := by
  apply eq_of_heq
  exact (SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).trans
    (ownerAtDisplayedStart_heq segment owner)

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Refine the original segment to the requested dyadic depth with its displayed endpoints retained.

The construction uses the bounded zero-to-one dyadic path, then transports its endpoint indices through the original
segment equations. -/
def dyadicRefineSegment {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    Polynomial.Geometry.ClearPath polynomial ambient start finish :=
  ((ClearSheetContinuation.Subdivision.dyadicPath segment within
      depth zeroEndpoint oneEndpoint).castStart (by
        exact Geometry.ClearPath.ClearSegment.pointAt_zero _)).castFinish (by
          exact Geometry.ClearPath.ClearSegment.pointAt_one _)

/-- A depth-`depth` segment refinement has exactly `2 ^ depth` segments.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem dyadicRefineSegment_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    (dyadicRefineSegment segment within depth).segmentCount = 2 ^ depth := by
  rewrite [dyadicRefineSegment, Polynomial.Geometry.ClearPath.segmentCount_castFinish,
    Polynomial.Geometry.ClearPath.segmentCount_castStart,
    ClearSheetContinuation.Subdivision.dyadicPath_segmentCount]
  exact Eq.refl _

end

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A prepared subdivision from the original segment start with terminal parameter exactly one.

The initial owner is the original displayed-start owner transported to parameter zero; the final parameter equation
identifies the segment's displayed finish. -/
structure CompleteSegment {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) where
  /-- The actual prepared subdivision starting at parameter zero with the original transported source owner. -/
    subdivision : PreparedSubdivision segment within zeroEndpoint
    (ownerAtStart segment owner)
  /-- The actual terminal subdivision parameter is exactly one. -/ endpoint_eq : subdivision.endpoint.parameter = 1

constructive_injectivity CompleteSegment

namespace CompleteSegment

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Package the actual successful dyadic subdivision as a complete prepared segment.

The success equation supplies its exact terminal parameter, preserving the returned subdivision and the original source
owner. -/
def ofTryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    CompleteSegment segment within owner where
  subdivision := subdivision
  endpoint_eq := by
    have endpointEqual :=
      PreparedSheetContinuation.Subdivision.tryDyadic_endpoint
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive success
    exact congrArg (fun endpoint : Endpoint => endpoint.parameter) endpointEqual

/-- Construct a complete prepared segment from the original dyadic mesh-safety certificate. -/
def ofSafeDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
    (PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive safe)

/-- Construct a complete prepared segment from safety of the actual executed dyadic preparation. -/
def ofExecutedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
    (PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_ofExecutedDyadicMeshSafe
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive safe)

/-- The actual successful complete subdivision has exactly `2 ^ depth` steps. -/
@[simp] theorem ofTryDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.stepCount = 2 ^ depth :=
  PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

/-- The actual successful complete subdivision retains exactly the requested dyadic parameter edges. -/
theorem ofTryDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint :=
  PreparedSheetContinuation.Subdivision.tryDyadic_parameterEdges
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

/-- The actual successful complete subdivision retains exactly the original dyadic endpoint and diameter requests. -/
theorem ofTryDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).subdivision.requests =
        PreparedSheetContinuation.Subdivision.dyadicRequests depth
          zeroEndpoint oneEndpoint rootDiameter rootDiameterPositive :=
  PreparedSheetContinuation.Subdivision.tryDyadic_requests
    segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive success

/-- The mesh-safe complete subdivision has exactly `2 ^ depth` steps. -/
@[simp] theorem ofSafeDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.stepCount = 2 ^ depth :=
  ofTryDyadic_stepCount segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The mesh-safe complete subdivision retains exactly the requested dyadic parameter edges. -/
theorem ofSafeDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint :=
  ofTryDyadic_parameterEdges segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The mesh-safe complete subdivision retains exactly the original dyadic endpoint and diameter requests. -/
theorem ofSafeDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).subdivision.requests =
        PreparedSheetContinuation.Subdivision.dyadicRequests depth
          zeroEndpoint oneEndpoint rootDiameter rootDiameterPositive :=
  ofTryDyadic_requests segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The execution-safe complete subdivision has exactly `2 ^ depth` steps. -/
@[simp] theorem ofExecutedDyadic_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).subdivision.stepCount = 2 ^ depth :=
  ofTryDyadic_stepCount segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The execution-safe complete subdivision retains exactly the requested dyadic parameter edges. -/
theorem ofExecutedDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).subdivision.parameterEdges =
        ClearSheetContinuation.Subdivision.dyadicEdges depth
          zeroEndpoint oneEndpoint :=
  ofTryDyadic_parameterEdges segment within owner depth rootDiameter
    rootDiameterPositive _

/-- Increasing the safe depth by `additional` refines each earlier dyadic parameter edge by that many levels. -/
theorem ofSafeDyadic_parameterEdges_add
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (earlier additional : Nat)
    (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        (earlier + additional) rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner (earlier + additional) rootDiameter
      rootDiameterPositive safe).subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.refineDyadicEdges
        additional
        (ClearSheetContinuation.Subdivision.dyadicEdges earlier
          zeroEndpoint oneEndpoint) := by
  rw [ofSafeDyadic_parameterEdges,
    ClearSheetContinuation.Subdivision.dyadicEdges_add]

end

section
open Purelib.Polynomial
/-- The complete segment's parameter-zero coordinate is its original displayed start.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem start_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (_prepared : CompleteSegment segment within owner) :
    segment.pointAt zeroEndpoint.parameter = start := by
  exact Geometry.ClearPath.ClearSegment.pointAt_zero _

/-- The complete subdivision's actual terminal coordinate is the original displayed finish. -/
theorem finish_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    segment.pointAt prepared.subdivision.endpoint.parameter = finish := by
  rw [prepared.endpoint_eq, Geometry.ClearPath.ClearSegment.pointAt_one]

end

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Transport the actual terminal subdivision owner to the segment's displayed finish radicand. -/
def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Owner (polynomial.eval finish) := by
  exact SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg polynomial.eval prepared.finish_eq) prepared.subdivision.terminalOwner

open Purelib.Polynomial in
/-- The exact terminal owner at the segment's displayed finish. -/
def finishOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Owner (polynomial.eval finish) :=
  prepared.terminalOwner

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The displayed finish owner preserves the original subdivision terminal owner up to heterogeneous equality. -/
theorem finishOwner_heq_terminalOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    HEq prepared.finishOwner prepared.subdivision.terminalOwner := by
  unfold finishOwner terminalOwner
  exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The retained terminal and finish-owner names are operationally equivalent. -/
def terminalRootEquivalentFinishOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        prepared.terminalOwner.parameterNonzero prepared.terminalOwner)
      (SquareRootTrackEquivalence.ownerRootName
        prepared.terminalOwner.parameterNonzero prepared.finishOwner) := by
  exact Equivalence.NamedEquivalent.refl _

open Purelib.Polynomial in
/-- Read the original prepared subdivision as a clear path with its displayed endpoint indices. -/
def clearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    Polynomial.Geometry.ClearPath polynomial ambient start finish :=
  (prepared.subdivision.toClearPath.castStart prepared.start_eq).castFinish
    prepared.finish_eq

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Read the original subdivision's edges with their exact canonical center states. -/
def centeredEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    List
      (PreparedSubdivisionModelCore.CenteredEdge curve differential) :=
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet prepared.subdivision
  PreparedSubdivisionModelCore.centeredEdges curve differential sheet
    prepared.subdivision centers

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- The sum of retained geometric lower estimates for the integral sample's real coordinate. -/
def integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    Fraction.Rational :=
  PreparedSubdivisionModelCore.preparedSubdivisionIntegralRealLower
    curve differential sheet prepared.subdivision

/-- The sum of retained geometric lower estimates for the integral sample's negated real coordinate. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    Fraction.Rational :=
  PreparedSubdivisionModelCore.preparedSubdivisionNegatedIntegralRealLower
    curve differential sheet prepared.subdivision

/-- The sum of retained geometric lower estimates for the integral sample's scalar projection onto the supplied Gaussian
direction. -/
def directionalIntegralLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (direction : Gaussian)
    (prepared : CompleteSegment segment within owner) :
    Fraction.Rational :=
  PreparedSubdivisionModelCore.preparedSubdivisionDirectionalIntegralLower
    curve differential sheet direction prepared.subdivision

end

open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- The canonical centered edge list has the original subdivision's step count. -/
@[simp] theorem centeredEdges_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).length =
      prepared.subdivision.stepCount := by
  unfold centeredEdges
  exact PreparedSubdivisionModelCore.centeredEdges_length
    curve differential sheet prepared.subdivision _

/-- The centered edges retain the exact original subdivision parameter-edge list. -/
theorem centeredEdges_parameterEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.parameterEdge =
      prepared.subdivision.parameterEdges := by
  unfold centeredEdges
  exact PreparedSubdivisionModelCore.centeredEdges_parameterEdges
    curve differential sheet prepared.subdivision _

/-- The centered edges retain the exact original cached prepared-box list. -/
theorem centeredEdges_preparedBoxes {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        (fun centered =>
          centered.edge.cached.preparedOwner.track.initial.box) =
      prepared.subdivision.preparedBoxes := by
  unfold centeredEdges
  exact PreparedSubdivisionModelCore.centeredEdges_preparedBoxes
    curve differential sheet prepared.subdivision _

/-- The canonical centered edge models are exactly the canonical centered subdivision's certified cells. -/
theorem centeredEdges_models {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model =
      (PreparedSubdivisionAutomaticModels.certifyCenteredSubdivision curve
        differential sheet prepared.subdivision
          (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
            differential sheet prepared.subdivision)).cells := by
  unfold centeredEdges
  exact PreparedSubdivisionAutomaticModels.centeredEdges_models curve
    differential sheet prepared.subdivision _

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Exact dyadic parameter edges identify the complete segment's clear path with its geometric dyadic refinement.

The proof transports the original target list and endpoint equations, preserving the actual segment restrictions and
their ordered concatenation. -/
theorem clearPath_eq_dyadicRefineSegment_of_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (prepared : CompleteSegment segment within owner)
    (depth : Nat)
    (edges : prepared.subdivision.parameterEdges =
      ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint) :
    prepared.clearPath = dyadicRefineSegment segment within depth := by
  let startEqual : segment.pointAt zeroEndpoint.parameter = start := by
    exact Geometry.ClearPath.ClearSegment.pointAt_zero _
  let finishEqual : segment.pointAt oneEndpoint.parameter = finish := by
    exact Geometry.ClearPath.ClearSegment.pointAt_one _
  have mesh :=
    PreparedSheetContinuation.Subdivision.toClearPath_eq_geometricPath_parameterEdges
      prepared.subdivision
  let actualTargets :=
    prepared.subdivision.parameterEdges.map (fun edge => edge.right)
  let targetsEqual : actualTargets =
      ClearSheetContinuation.Subdivision.dyadicTargets depth
        zeroEndpoint oneEndpoint := by
    calc
      actualTargets =
          (ClearSheetContinuation.Subdivision.dyadicEdges depth
            zeroEndpoint oneEndpoint).map (fun edge => edge.right) :=
        congrArg (List.map fun edge => edge.right) edges
      _ = ClearSheetContinuation.Subdivision.dyadicTargets depth
          zeroEndpoint oneEndpoint :=
        ClearSheetContinuation.Subdivision.dyadicEdges_rights
          depth zeroEndpoint oneEndpoint
  let actualFinishEqual := congrArg
    (fun targets : List Endpoint =>
      segment.pointAt
        ((ClearSheetContinuation.Subdivision.finalTarget
          zeroEndpoint targets).parameter)) targetsEqual
  let dyadicFinishEqual := congrArg
    (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
        depth zeroEndpoint oneEndpoint)
  have transportGeometry : forall (first second : List Endpoint)
      (equal : first = second),
      (ClearSheetContinuation.Subdivision.geometricPath segment
        within zeroEndpoint first).castFinish
          (congrArg
            (fun targets : List Endpoint =>
              segment.pointAt
                ((ClearSheetContinuation.Subdivision.finalTarget
                  zeroEndpoint targets).parameter)) equal) =
        ClearSheetContinuation.Subdivision.geometricPath segment
          within zeroEndpoint second := by
    intro first second equal
    subst second
    rfl
  have geometricEqual :
      (ClearSheetContinuation.Subdivision.geometricPath segment
        within zeroEndpoint actualTargets).castFinish actualFinishEqual =
        ClearSheetContinuation.Subdivision.geometricPath segment
          within zeroEndpoint
            (ClearSheetContinuation.Subdivision.dyadicTargets depth
              zeroEndpoint oneEndpoint) :=
    transportGeometry _ _ targetsEqual
  have endpointEqual : prepared.subdivision.endpoint = oneEndpoint :=
    (PreparedSheetContinuation.Subdivision.endpoint_eq_finalTarget_parameterEdges
      prepared.subdivision).trans
        ((congrArg
          (ClearSheetContinuation.Subdivision.finalTarget
            zeroEndpoint) targetsEqual).trans
          (ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
            depth zeroEndpoint oneEndpoint))
  have meshAtEndpoint :
      prepared.subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter) endpointEqual) =
        ClearSheetContinuation.Subdivision.dyadicPath segment within
          depth zeroEndpoint oneEndpoint := by
    calc
      prepared.subdivision.toClearPath.castFinish
            (congrArg (fun endpoint : Endpoint =>
              segment.pointAt endpoint.parameter) endpointEqual) =
          ((prepared.subdivision.toClearPath.castFinish
            (congrArg (fun endpoint : Endpoint =>
              segment.pointAt endpoint.parameter)
                (PreparedSheetContinuation.Subdivision.endpoint_eq_finalTarget_parameterEdges
                    prepared.subdivision))).castFinish
              actualFinishEqual).castFinish dyadicFinishEqual := by
        rewrite [Polynomial.Geometry.ClearPath.castFinish_castFinish,
          Polynomial.Geometry.ClearPath.castFinish_castFinish]
        exact Eq.refl _
      _ = ((ClearSheetContinuation.Subdivision.geometricPath
            segment within zeroEndpoint actualTargets).castFinish
              actualFinishEqual).castFinish dyadicFinishEqual := by
        rw [mesh]
      _ = (ClearSheetContinuation.Subdivision.geometricPath
            segment within zeroEndpoint
              (ClearSheetContinuation.Subdivision.dyadicTargets
                depth zeroEndpoint oneEndpoint)).castFinish
                  dyadicFinishEqual := by
        rw [geometricEqual]
      _ = ClearSheetContinuation.Subdivision.dyadicPath segment
          within depth zeroEndpoint oneEndpoint := rfl
  have transported := congrArg
    (fun refined : Polynomial.Geometry.ClearPath polynomial ambient
        (segment.pointAt zeroEndpoint.parameter)
        (segment.pointAt oneEndpoint.parameter) =>
      (refined.castStart startEqual).castFinish finishEqual) meshAtEndpoint
  dsimp only [clearPath, dyadicRefineSegment]
  rewrite [Polynomial.Geometry.ClearPath.castStart_castFinish,
    Polynomial.Geometry.ClearPath.castFinish_castFinish] at transported
  rewrite [Polynomial.Geometry.ClearPath.castStart_castFinish]
  exact transported

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- The actual successful complete subdivision has exactly the geometric dyadic refinement as its clear path.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem ofTryDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    (ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).clearPath = dyadicRefineSegment segment within depth := by
  let startEqual : segment.pointAt zeroEndpoint.parameter = start := by
    exact Geometry.ClearPath.ClearSegment.pointAt_zero _
  let finishEqual : segment.pointAt oneEndpoint.parameter = finish := by
    exact Geometry.ClearPath.ClearSegment.pointAt_one _
  have mesh :=
    PreparedSheetContinuation.Subdivision.tryDyadic_toClearPath_eq_dyadicPath
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive success
  have transported := congrArg
    (fun refined : Polynomial.Geometry.ClearPath polynomial ambient
        (segment.pointAt zeroEndpoint.parameter)
        (segment.pointAt oneEndpoint.parameter) =>
      (refined.castStart startEqual).castFinish finishEqual) mesh
  dsimp only [clearPath, ofTryDyadic, dyadicRefineSegment]
  rewrite [Polynomial.Geometry.ClearPath.castStart_castFinish,
    Polynomial.Geometry.ClearPath.castFinish_castFinish] at transported
  rewrite [Polynomial.Geometry.ClearPath.castStart_castFinish]
  exact transported

/-- The mesh-safe complete subdivision has exactly the geometric dyadic refinement as its clear path. -/
theorem ofSafeDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    (ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).clearPath = dyadicRefineSegment segment within depth :=
  ofTryDyadic_clearPath segment within owner depth rootDiameter
    rootDiameterPositive _

/-- The execution-safe complete subdivision has exactly the geometric dyadic refinement as its clear path. -/
theorem ofExecutedDyadic_clearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
          depth rootDiameter rootDiameterPositive) :
    (ofExecutedDyadic segment within owner depth rootDiameter
      rootDiameterPositive safe).clearPath =
        dyadicRefineSegment segment within depth :=
  ofTryDyadic_clearPath segment within owner depth rootDiameter
    rootDiameterPositive _

end

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- The mesh-safe complete subdivision has canonical centered edges with exactly the requested dyadic parameter edges.
-/
theorem ofSafeDyadic_centeredEdges_parameterEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat)
    (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    ((ofSafeDyadic segment within owner depth rootDiameter rootDiameterPositive
      safe).centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.parameterEdge =
      ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint := by
  rw [centeredEdges_parameterEdges, ofSafeDyadic_parameterEdges]

/-- The actual successful complete subdivision has canonical centered edges with exactly the requested dyadic parameter
edges. -/
theorem ofTryDyadic_centeredEdges_parameterEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat)
    (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision segment within zeroEndpoint
      (ownerAtStart segment owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic
      segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
        depth rootDiameter rootDiameterPositive = some subdivision) :
    ((ofTryDyadic segment within owner depth rootDiameter rootDiameterPositive
      success).centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.parameterEdge =
      ClearSheetContinuation.Subdivision.dyadicEdges depth
        zeroEndpoint oneEndpoint := by
  rw [centeredEdges_parameterEdges,
    ofTryDyadic_parameterEdges segment within owner depth rootDiameter
      rootDiameterPositive success]

end CompleteSegment

section
open Purelib.Polynomial
/-- Refine every original clear-path segment at the same dyadic depth and concatenate in order. -/
def dyadicRefinePath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient -> Nat -> Polynomial.Geometry.ClearPath polynomial ambient start finish
  | _, _, .nil point, _within, _depth => .nil point
  | _, _, .cons head tail, within, depth =>
      (dyadicRefineSegment head within.head depth).append
        (dyadicRefinePath tail within.tail depth)

/-- Refine successive original path segments using the corresponding scheduled depths.

When the depth list ends, the unchanged original path tail is retained; extra depths after the path ends contribute
nothing. -/
def dyadicRefinePathScheduled {polynomial : GaussianPolynomial}
    {ambient : Box} : {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient -> List Nat ->
          Polynomial.Geometry.ClearPath polynomial ambient start finish
  | _, _, .nil point, _within, _depths => .nil point
  | _, _, .cons head tail, _within, [] => .cons head tail
  | _, _, .cons head tail, within, depth :: depths =>
      (dyadicRefineSegment head within.head depth).append
        (dyadicRefinePathScheduled tail within.tail depths)

open Purelib.Riemann.Branches in
/-- The geometric path through the retained bounded parameters remains inside the original ambient box. -/
private theorem geometricPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : ClearSheetContinuation.Subdivision.Endpoint) :
    forall remaining :
      List ClearSheetContinuation.Subdivision.Endpoint,
      (ClearSheetContinuation.Subdivision.geometricPath segment
        within current remaining).WithinAmbient
  | [] => .nil _
  | endpoint :: remaining =>
      .cons
        (segment.restrict_withinAmbient within current.parameter
          endpoint.parameter current.inside endpoint.inside)
        (geometricPath_withinAmbient segment within endpoint remaining)

/-- Transporting the start endpoint along equality preserves the original ambient-containment certificate. -/
private theorem castStart_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient left finish)
    (within : path.WithinAmbient) (equal : left = right) :
    (path.castStart equal).WithinAmbient := by
  subst right
  exact within

/-- Transporting the finish endpoint along equality preserves the original ambient-containment certificate. -/
private theorem castFinish_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start left)
    (within : path.WithinAmbient) (equal : left = right) :
    (path.castFinish equal).WithinAmbient := by
  subst right
  exact within

open Purelib.Riemann.Branches in
/-- Dyadic refinement of an ambient-contained segment remains in that same ambient box. -/
theorem dyadicRefineSegment_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat) :
    (dyadicRefineSegment segment within depth).WithinAmbient := by
  unfold dyadicRefineSegment
  apply castFinish_withinAmbient
  apply castStart_withinAmbient
  unfold ClearSheetContinuation.Subdivision.dyadicPath
  apply castFinish_withinAmbient
  exact geometricPath_withinAmbient segment within zeroEndpoint _

/-- Uniform dyadic refinement preserves containment of the whole original path in its ambient box. -/
theorem dyadicRefinePath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box} :
    forall {start finish : Gaussian}
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
      (within : path.WithinAmbient) (depth : Nat),
      (dyadicRefinePath path within depth).WithinAmbient
  | _, _, .nil point, _within, _depth => .nil point
  | _, _, .cons head tail, within, depth =>
      (dyadicRefineSegment_withinAmbient head within.head depth).append
        (dyadicRefinePath_withinAmbient tail within.tail depth)

/-- Scheduled dyadic refinement preserves the original path's ambient containment. -/
theorem dyadicRefinePathScheduled_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box} :
    forall {start finish : Gaussian}
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
      (within : path.WithinAmbient) (depths : List Nat),
      (dyadicRefinePathScheduled path within depths).WithinAmbient
  | _, _, .nil point, _within, _depths => by
      simp only [dyadicRefinePathScheduled]
      exact .nil point
  | _, _, .cons _head _tail, within, [] => within
  | _, _, .cons head tail, within, _depth :: depths =>
      (dyadicRefineSegment_withinAmbient head within.head _).append
        (dyadicRefinePathScheduled_withinAmbient tail within.tail depths)

/-- Uniform depth-`depth` refinement multiplies the original segment count by `2 ^ depth`.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem dyadicRefinePath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (depth : Nat) :
    (dyadicRefinePath path within depth).segmentCount =
      2 ^ depth * path.segmentCount := by
  induction path with
  | nil point => rfl
  | cons head tail inductionHypothesis =>
      change ((dyadicRefineSegment head within.head depth).append
        (dyadicRefinePath tail within.tail depth)).segmentCount = _
      rewrite [Polynomial.Geometry.ClearPath.segmentCount_append,
        dyadicRefineSegment_segmentCount, inductionHypothesis within.tail]
      change 2 ^ depth + 2 ^ depth * tail.segmentCount = 2 ^ depth * (tail.segmentCount + 1)
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The maximum sufficient dyadic depth of the original path's segments for the given diameter target.

The finite recursion retains the original segment geometry; the empty path contributes depth zero. -/
def sufficientDepth {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      Polynomial.Geometry.ClearPath polynomial ambient start finish ->
        Fraction.Rational -> Nat
  | _, _, .nil _point, _rootDiameter => 0
  | _, _, .cons head tail, rootDiameter =>
      max
        (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
          head zeroEndpoint oneEndpoint rootDiameter)
        (sufficientDepth tail rootDiameter)

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Data in
/-- The head segment's sufficient depth is at most the entire path's sufficient depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem headSufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
    (rootDiameter : Fraction.Rational) :
    PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        head zeroEndpoint oneEndpoint rootDiameter <=
      sufficientDepth (.cons head tail) rootDiameter :=
  by
    change _ ≤ max _ _
    rw [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_left _ _

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Data in
/-- The original tail's sufficient depth is at most the entire path's sufficient depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem tailSufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
    (rootDiameter : Fraction.Rational) :
    sufficientDepth tail rootDiameter <=
      sufficientDepth (.cons head tail) rootDiameter :=
  by
    change _ ≤ max _ _
    rw [Nat.Order.max_eq_natMax]
    exact Nat.Order.le_max_right _ _

open Purelib.Polynomial in
set_option genInjectivity false in
/-- Complete prepared segments linked through their actual terminal root owners.

Each tail begins with the preceding complete segment's exact finish owner, retaining the original clear-path geometry
and source owner. -/
inductive PreparedPath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  /-- Retain the empty prepared path at the original point and root owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) :
      PreparedPath (.nil point) owner
  /-- Retain the original head segment and its certificate, with the tail starting at the head's exact finish owner. -/
    | cons {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (preparedHead : CompleteSegment head headWithin owner)
      (preparedTail : PreparedPath tail preparedHead.finishOwner) :
      PreparedPath (.cons head tail) owner

constructive_injectivity PreparedPath

namespace PreparedPath

section
open Purelib.Data.Rat
open Purelib.Polynomial
section
open Purelib.Riemann.Branches
/-- Attempt dyadic preparation of each original path segment at the same requested depth and positive diameter.

Successful segments pass their actual finish owner to the next segment. Success retains the complete prepared path;
`none` is the unsuccessful outcome of this finite attempt. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            (depth : Nat) ->
              (rootDiameter : Fraction.Rational) ->
                0 < rootDiameter -> Option (PreparedPath path owner)
  | _, _, .nil point, _within, owner, _depth, _rootDiameter,
      _rootDiameterPositive => some (.nil point owner)
  | _, _, .cons head tail, within, owner, depth, rootDiameter,
      rootDiameterPositive =>
      let headWithin := within.head
      match success :
          PreparedSheetContinuation.Subdivision.tryDyadic head
            headWithin zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive with
      | none => none
      | some subdivision =>
          let preparedHead := CompleteSegment.ofTryDyadic head headWithin owner
            depth rootDiameter rootDiameterPositive (subdivision := subdivision)
              success
          match tryDyadic tail within.tail preparedHead.finishOwner depth
              rootDiameter rootDiameterPositive with
          | none => none
          | some preparedTail =>
              some (.cons head tail owner headWithin preparedHead preparedTail)

/-- Safety of the actual successive dyadic preparations along the original path.

Each segment's execution certificate determines the precise finish owner used in the remaining safety predicate. -/
def ExecutedDyadicPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) -> Prop
  | _, _, .nil _point, _within, _owner => True
  | _, _, .cons head tail, within, owner =>
      if safe :
          PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
          within.tail
            (CompleteSegment.ofExecutedDyadic head within.head owner depth
              rootDiameter rootDiameterPositive safe).finishOwner
      else False

/-- Decide executed path safety by testing each original segment and its actual successor owner. -/
def executedDyadicPathSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            Decidable (ExecutedDyadicPathSafe depth rootDiameter
              rootDiameterPositive path within owner)
  | _, _, .nil _point, _within, _owner => isTrue trivial
  | _, _, .cons head tail, within, owner => by
      if safe :
          PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        let tailDecision := executedDyadicPathSafeDecidable depth rootDiameter
          rootDiameterPositive tail within.tail preparedHead.finishOwner
        match tailDecision with
        | isTrue tailSafe =>
            exact isTrue (by
              change (if witness :
                  PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                    head within.head zeroEndpoint oneEndpoint
                      (ownerAtStart head owner) depth rootDiameter
                        rootDiameterPositive then
                ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
                  tail within.tail
                    (CompleteSegment.ofExecutedDyadic head within.head owner
                      depth rootDiameter rootDiameterPositive witness).finishOwner
              else False)
              simpa only [dif_pos safe] using tailSafe)
        | isFalse tailNotSafe =>
            exact isFalse (fun pathSafe => by
              change (if witness :
                  PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                    head within.head zeroEndpoint oneEndpoint
                      (ownerAtStart head owner) depth rootDiameter
                        rootDiameterPositive then
                ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
                  tail within.tail
                    (CompleteSegment.ofExecutedDyadic head within.head owner
                      depth rootDiameter rootDiameterPositive witness).finishOwner
              else False) at pathSafe
              have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
                  rootDiameterPositive tail within.tail
                    preparedHead.finishOwner := by
                simpa only [dif_pos safe] using pathSafe
              exact tailNotSafe tailSafe)
      else
        exact isFalse (fun pathSafe => by
          change (if witness :
              PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe)

end

/-- The executable decision procedure for safety of the retained dyadic path preparation. -/
instance executedDyadicPathSafeInstance
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) :
    Decidable (ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
      path within owner) :=
  executedDyadicPathSafeDecidable depth rootDiameter rootDiameterPositive path
    within owner

open Purelib.Riemann.Branches in
/-- Construct a prepared path from safety of its actual successive dyadic preparations.

The recursion retains every certified head subdivision and starts the tail with that head's exact finish owner. -/
def ofExecutedDyadicPathSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive path
              within owner -> PreparedPath path owner
  | _, _, .nil point, _within, owner, _safe => .nil point owner
  | _, _, .cons head tail, within, owner, pathSafe => by
      if safe :
          PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
            rootDiameterPositive tail within.tail preparedHead.finishOwner := by
          change (if witness :
              PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simpa only [dif_pos safe] using pathSafe
        exact .cons head tail owner within.head preparedHead
          (ofExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner tailSafe)
      else
        have impossible : False := by
          change (if witness :
              PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe
        exact impossible.elim

end

open Purelib.Polynomial in
/-- Concatenate the actual complete prepared segment paths in original order. -/
def toClearPath {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> Polynomial.Geometry.ClearPath polynomial ambient start finish
  | _, _, _, _, .nil point _owner => .nil point
  | _, _, _, _, .cons head tail owner _headWithin preparedHead preparedTail =>
      preparedHead.clearPath.append preparedTail.toClearPath

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Rat
open Purelib.Polynomial
/-- The sum of retained geometric lower estimates for the integral sample's real coordinate. -/
def integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> Fraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.integralRealLower curve differential sheet +
        integralRealLower curve differential sheet preparedTail

/-- The sum of retained geometric lower estimates for the integral sample's negated real coordinate. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> Fraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.negatedIntegralRealLower curve differential sheet +
        negatedIntegralRealLower curve differential sheet preparedTail

/-- The sum of retained geometric lower estimates for the integral sample's scalar projection onto the supplied Gaussian
direction. -/
def directionalIntegralLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    (direction : Gaussian)
    {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} ->
      {owner : Owner (curve.polynomial.eval start)} ->
        PreparedPath path owner -> Fraction.Rational
  | _, _, _, _, .nil _point _owner => 0
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.directionalIntegralLower curve differential sheet direction +
        directionalIntegralLower curve differential sheet direction preparedTail

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- Dyadic mesh-safety certificates for all original path segments at a common depth and diameter.

Each tail is indexed by the exact finish owner produced from the preceding segment's retained safety certificate. -/
inductive CheckedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  /-- The empty certified path at the original point and source owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) :
      CheckedDyadic depth rootDiameter rootDiameterPositive (.nil point) owner
  /-- Retain the original head segment with its mesh-safety certificate, and the certified tail at the head's exact
    finish owner. -/ | cons {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (headSafe :
        PreparedSheetContinuation.Subdivision.DyadicMeshSafe
          head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
            rootDiameter rootDiameterPositive)
      (remaining : CheckedDyadic depth rootDiameter rootDiameterPositive tail
        (CompleteSegment.ofSafeDyadic head headWithin owner depth rootDiameter
          rootDiameterPositive headSafe).finishOwner) :
      CheckedDyadic depth rootDiameter rootDiameterPositive (.cons head tail)
        owner

constructive_injectivity CheckedDyadic

namespace CheckedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Construct checked dyadic safety when the requested depth meets the path's finite sufficient-depth bound.

The bound is specialized to each original segment; every successor owner is the actual finish owner of its certified
predecessor. -/
def totalAt {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            (depth : Nat) ->
              (rootDiameter : Fraction.Rational) ->
                (rootDiameterPositive : 0 < rootDiameter) ->
                  sufficientDepth path rootDiameter <= depth ->
                    CheckedDyadic depth rootDiameter rootDiameterPositive path
                      owner
  | _, _, .nil point, _within, owner, depth, rootDiameter,
      rootDiameterPositive, _enough => .nil point owner
  | _, _, .cons head tail, within, owner, depth, rootDiameter,
      rootDiameterPositive, enough => by
      have headEnough :
          PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
              head zeroEndpoint oneEndpoint rootDiameter <= depth :=
        (headSufficientDepth_le head tail rootDiameter).trans enough
      let headSafe :=
        PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
          head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
            rootDiameter rootDiameterPositive (by decide) headEnough
      let preparedHead := CompleteSegment.ofSafeDyadic head within.head owner
        depth rootDiameter rootDiameterPositive headSafe
      have tailEnough : sufficientDepth tail rootDiameter <= depth :=
        (tailSufficientDepth_le head tail rootDiameter).trans enough
      exact .cons head tail owner within.head headSafe
        (totalAt tail within.tail preparedHead.finishOwner depth rootDiameter
          rootDiameterPositive tailEnough)

set_option linter.defProp false in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the original path's retained ambient-containment certificate. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          CheckedDyadic depth rootDiameter rootDiameterPositive path owner ->
            path.WithinAmbient
  | _, _, _, _, .nil point owner => .nil point
  | _, _, _, _, .cons head tail owner headWithin _headSafe remaining =>
      .cons headWithin remaining.within

open Purelib.Data.Rat
open Purelib.Polynomial
/-- Read the exact prepared path supplied by the retained dyadic certificates or execution result. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          CheckedDyadic depth rootDiameter rootDiameterPositive path owner ->
            PreparedPath path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin headSafe remaining =>
      .cons head tail owner headWithin
        (CompleteSegment.ofSafeDyadic head headWithin owner depth rootDiameter
          rootDiameterPositive headSafe) remaining.prepared

/-- The retained prepared geometry is exactly the original path's dyadic refinement at the certified depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
      owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      dsimp only [prepared, toClearPath, dyadicRefinePath]
      rewrite [CompleteSegment.ofSafeDyadic_clearPath, inductionHypothesis]
      exact Eq.refl _

end CheckedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A path of certificates for the actual executed dyadic preparations and their exact successor owners.

The depth and positive diameter target remain common indices, while each original segment retains its own
execution-safety evidence. -/
inductive ExecutedCheckedDyadic {polynomial : GaussianPolynomial}
    {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  /-- The empty certified path at the original point and source owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) :
      ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
        (.nil point) owner
  /-- Retain the original head segment with its executed mesh-safety certificate, and the certified tail at the head's
    exact finish owner. -/ | cons {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (headSafe :
        PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
          head headWithin zeroEndpoint oneEndpoint (ownerAtStart head owner)
            depth rootDiameter rootDiameterPositive)
      (remaining : ExecutedCheckedDyadic depth rootDiameter
        rootDiameterPositive tail
          (CompleteSegment.ofExecutedDyadic head headWithin owner depth
            rootDiameter rootDiameterPositive headSafe).finishOwner) :
      ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
        (.cons head tail) owner

constructive_injectivity ExecutedCheckedDyadic

namespace ExecutedCheckedDyadic

set_option linter.defProp false in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the original path's retained ambient-containment certificate. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive path
            owner -> path.WithinAmbient
  | _, _, _, _, .nil point owner => .nil point
  | _, _, _, _, .cons head tail owner headWithin _headSafe remaining =>
      .cons headWithin remaining.within

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the exact prepared path supplied by the retained dyadic certificates or execution result. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive path
            owner -> PreparedPath path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin headSafe remaining =>
      .cons head tail owner headWithin
        (CompleteSegment.ofExecutedDyadic head headWithin owner depth
          rootDiameter rootDiameterPositive headSafe) remaining.prepared

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Convert executed path safety into the dependent list of exact segment execution certificates. -/
def ofPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        (within : path.WithinAmbient) ->
          (owner : Owner (polynomial.eval start)) ->
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive path
              within owner ->
                ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
                  path owner
  | _, _, .nil point, _within, owner, _safe => .nil point owner
  | _, _, .cons head tail, within, owner, pathSafe => by
      if safe :
          PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
            head within.head zeroEndpoint oneEndpoint
              (ownerAtStart head owner) depth rootDiameter
                rootDiameterPositive then
        let preparedHead := CompleteSegment.ofExecutedDyadic head within.head
          owner depth rootDiameter rootDiameterPositive safe
        have tailSafe : ExecutedDyadicPathSafe depth rootDiameter
            rootDiameterPositive tail within.tail preparedHead.finishOwner := by
          change (if witness :
              PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simpa only [dif_pos safe] using pathSafe
        exact .cons head tail owner within.head safe
          (ofPathSafe depth rootDiameter rootDiameterPositive tail within.tail
            preparedHead.finishOwner tailSafe)
      else
        have impossible : False := by
          change (if witness :
              PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
                head within.head zeroEndpoint oneEndpoint
                  (ownerAtStart head owner) depth rootDiameter
                    rootDiameterPositive then
            ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive tail
              within.tail
                (CompleteSegment.ofExecutedDyadic head within.head owner depth
                  rootDiameter rootDiameterPositive witness).finishOwner
          else False) at pathSafe
          simp only [dif_neg safe] at pathSafe
        exact impossible.elim

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained prepared geometry is exactly the original path's dyadic refinement at the certified depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      dsimp only [prepared, toClearPath, dyadicRefinePath]
      rewrite [CompleteSegment.ofExecutedDyadic_clearPath, inductionHypothesis]
      exact Eq.refl _

end ExecutedCheckedDyadic

open Purelib.Polynomial in
/-- Sum the actual subdivision step counts of the complete prepared segments in order. -/
def stepCount {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} -> PreparedPath path owner -> Nat
  | _, _, _, _, .nil _ _ => 0
  | _, _, _, _, .cons _ _ _ _ preparedHead preparedTail =>
      preparedHead.subdivision.stepCount + preparedTail.stepCount

namespace ExecutedCheckedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained prepared path has `2 ^ depth` steps per original clear-path segment.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ExecutedCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      dsimp only [prepared, stepCount]
      rewrite [CompleteSegment.ofExecutedDyadic_stepCount, inductionHypothesis]
      change 2 ^ depth + 2 ^ depth * tail.segmentCount = 2 ^ depth * (tail.segmentCount + 1)
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

end ExecutedCheckedDyadic

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- Read all original prepared differential edges in path and subdivision order. -/
def preparedEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    PreparedPath path owner ->
      List (PreparedSubdivisionModelCore.PreparedEdge curve
        differential)
  | .nil _ _ => []
  | .cons _ _ _ _ preparedHead preparedTail =>
      PreparedSubdivisionModelCore.preparedEdges curve differential
          sheet preparedHead.subdivision ++
        preparedEdges curve differential sheet preparedTail

/-- Read the zero wedge-coefficient charts of the original prepared segments in order. -/
def wedgeCharts {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .nil _ _ => []
  | .cons _ _ _ _ preparedHead preparedTail =>
      PreparedSubdivisionModelCore.wedgeCharts curve
          leftDifferential rightDifferential sheet preparedHead.subdivision ++
        wedgeCharts curve leftDifferential rightDifferential sheet preparedTail

open Purelib.Data in
/-- The wedge-chart list has exactly the total prepared subdivision step count.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    (wedgeCharts curve leftDifferential rightDifferential sheet
      prepared).length = prepared.stepCount := by
  induction prepared with
  | nil => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      dsimp only [wedgeCharts, stepCount]
      rewrite [List.Append.length_append,
        PreparedSubdivisionModelCore.wedgeCharts_length, inductionHypothesis]
      exact Eq.refl _

end

namespace CheckedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained prepared path has `2 ^ depth` steps per original clear-path segment.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
      owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction checked with
  | nil => rfl
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      dsimp only [prepared, stepCount]
      rewrite [CompleteSegment.ofSafeDyadic_stepCount, inductionHypothesis]
      change 2 ^ depth + 2 ^ depth * tail.segmentCount = 2 ^ depth * (tail.segmentCount + 1)
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

end CheckedDyadic

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Variation below the retained predicted clearance floor certifies the original segment's dyadic mesh safety. -/
theorem dyadicSafeOfVariation {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (below :
      Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound segment
            zeroEndpoint.parameter oneEndpoint.parameter) depth <
        PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
          segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
            rootDiameter rootDiameterPositive) :
    PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive :=
  PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_variation_lt_predictedClearanceFloor
    segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
      rootDiameter rootDiameterPositive (by decide) below

/-- Construct a complete segment from the retained variation-versus-predicted-clearance inequality. -/
def completeSegmentOfVariation {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (below :
      Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound segment
            zeroEndpoint.parameter oneEndpoint.parameter) depth <
        PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
          segment zeroEndpoint oneEndpoint (ownerAtStart segment owner) depth
            rootDiameter rootDiameterPositive) :
    CompleteSegment segment within owner :=
  CompleteSegment.ofSafeDyadic segment within owner depth rootDiameter
    rootDiameterPositive
      (dyadicSafeOfVariation segment owner depth rootDiameter
        rootDiameterPositive below)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- Per-segment variation bounds below the actual predicted dyadic clearance floors.

The dependent path retains each original segment and the finish owner produced by its certified preparation. -/
inductive ClearanceCheckedDyadic {polynomial : GaussianPolynomial}
    {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        Owner (polynomial.eval start) -> Type
  /-- The empty certified path at the original point and source owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) :
      ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
        (.nil point) owner
  /-- Retain the original head segment with its variation-versus-predicted-clearance inequality, and the certified tail
    at the head's exact finish owner. -/ | cons {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish)
      (owner : Owner (polynomial.eval start))
      (headWithin : head.WithinAmbient)
      (below :
        Geometric.Basic.quarterRadius
            (ClearSheetContinuation.variationBound head
              zeroEndpoint.parameter oneEndpoint.parameter) depth <
          PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
            head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive)
      (remaining : ClearanceCheckedDyadic depth rootDiameter
        rootDiameterPositive tail
          (completeSegmentOfVariation head headWithin owner depth rootDiameter
            rootDiameterPositive below).finishOwner) :
      ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
        (.cons head tail) owner

constructive_injectivity ClearanceCheckedDyadic

namespace ClearanceCheckedDyadic

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Test predicted dyadic clearance along the actual successive owner chain and retain the successful certificates.

Each original segment is tested at the fixed depth and diameter. An unsuccessful finite check returns `none`. -/
def execute? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (ClearanceCheckedDyadic depth rootDiameter
              rootDiameterPositive path owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if below :
          Geometric.Basic.quarterRadius
              (ClearSheetContinuation.variationBound head
                zeroEndpoint.parameter oneEndpoint.parameter) depth <
            PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
              head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                rootDiameter rootDiameterPositive then
        let preparedHead := completeSegmentOfVariation head within.head owner
          depth rootDiameter rootDiameterPositive below
        match execute? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head below remaining)
      else none

/-- Test each original segment against its uniform prepared-clearance floor along the actual owner chain.

Successful inequalities are transported to the predicted dyadic floors, retaining the corresponding original prepared
successor owners. -/
def executeUniform? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (ClearanceCheckedDyadic depth rootDiameter
              rootDiameterPositive path owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if below :
          Geometric.Basic.quarterRadius
              (ClearSheetContinuation.variationBound head
                zeroEndpoint.parameter oneEndpoint.parameter) depth <
            PreparedSheetContinuation.uniformPreparedClearanceFloor
              head rootDiameter then
        have predictedBelow :
            Geometric.Basic.quarterRadius
                (ClearSheetContinuation.variationBound head
                  zeroEndpoint.parameter oneEndpoint.parameter) depth <
              PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor
                head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                  rootDiameter rootDiameterPositive :=
          lt_of_lt_of_le below
            (PreparedSheetContinuation.Subdivision.uniformPreparedClearanceFloor_le_dyadicPredicted
              head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
                rootDiameter rootDiameterPositive)
        let preparedHead := completeSegmentOfVariation head within.head owner
          depth rootDiameter rootDiameterPositive predictedBelow
        match executeUniform? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head predictedBelow remaining)
      else none

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Decide the full dyadic mesh-safety predicate along the original path's actual successor-owner chain. -/
def executeMeshSafe? {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) ->
        path.WithinAmbient ->
          (owner : Owner (polynomial.eval start)) ->
            Option (CheckedDyadic depth rootDiameter rootDiameterPositive path
              owner)
  | _, _, .nil point, _within, owner => some (.nil point owner)
  | _, _, .cons head tail, within, owner =>
      if safe :
          PreparedSheetContinuation.Subdivision.DyadicMeshSafe
            head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth
              rootDiameter rootDiameterPositive then
        let preparedHead := CompleteSegment.ofSafeDyadic head within.head owner
          depth rootDiameter rootDiameterPositive safe
        match executeMeshSafe? depth rootDiameter rootDiameterPositive tail
            within.tail preparedHead.finishOwner with
        | none => none
        | some remaining =>
            some (.cons head tail owner within.head safe remaining)
      else none

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Convert retained predicted-clearance bounds to the exact dependent dyadic mesh-safety certificates. -/
def checked {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive path
              owner ->
            CheckedDyadic depth rootDiameter rootDiameterPositive path owner
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons head tail owner headWithin below remaining =>
      .cons head tail owner headWithin
        (dyadicSafeOfVariation head owner depth rootDiameter
          rootDiameterPositive below)
        remaining.checked

set_option linter.defProp false in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the original path's retained ambient-containment certificate. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) : path.WithinAmbient :=
  checked.checked.within

open Purelib.Data.Rat
open Purelib.Polynomial
/-- Read the exact prepared path supplied by the retained dyadic certificates or execution result. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) : PreparedPath path owner :=
  checked.checked.prepared

/-- The retained prepared geometry is exactly the original path's dyadic refinement at the certified depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.toClearPath =
      dyadicRefinePath path checked.within depth :=
  checked.checked.prepared_toClearPath_eq_dyadicRefinePath

/-- The retained prepared path has `2 ^ depth` steps per original clear-path segment.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ClearanceCheckedDyadic depth rootDiameter rootDiameterPositive
      path owner) :
    checked.prepared.stepCount = 2 ^ depth * path.segmentCount :=
  checked.checked.prepared_stepCount

end ClearanceCheckedDyadic

section
open Purelib.Data.Rat
open Purelib.Polynomial
/-- A successful finite dyadic preparation has `2 ^ depth` steps per original segment.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem tryDyadic_stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {prepared : PreparedPath path owner}
    (success : tryDyadic path within owner depth rootDiameter
      rootDiameterPositive = some prepared) :
    prepared.stepCount = 2 ^ depth * path.segmentCount := by
  induction path with
  | nil point =>
      simp only [tryDyadic] at success
      cases success
      rfl
  | cons head tail inductionHypothesis =>
      rw [tryDyadic] at success
      split at success
      · contradiction
      · rename_i subdivision headSuccess
        simp only at success
        split at success
        · contradiction
        · rename_i preparedTail tailSuccess
          cases success
          dsimp only [stepCount]
          rewrite [CompleteSegment.ofTryDyadic_stepCount,
            inductionHypothesis within.tail _ tailSuccess]
          change 2 ^ depth + 2 ^ depth * tail.segmentCount = 2 ^ depth * (tail.segmentCount + 1)
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- The actual successful dyadic preparation retains exactly the original path's geometric refinement. -/
theorem tryDyadic_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {prepared : PreparedPath path owner}
    (success : tryDyadic path within owner depth rootDiameter
      rootDiameterPositive = some prepared) :
    prepared.toClearPath = dyadicRefinePath path within depth := by
  induction path with
  | nil point =>
      simp only [tryDyadic] at success
      cases success
      rfl
  | cons head tail inductionHypothesis =>
      rw [tryDyadic] at success
      split at success
      · contradiction
      · rename_i subdivision headSuccess
        simp only at success
        split at success
        · contradiction
        · rename_i preparedTail tailSuccess
          cases success
          dsimp only [toClearPath, dyadicRefinePath]
          rewrite [CompleteSegment.ofTryDyadic_clearPath,
            inductionHypothesis within.tail _ tailSuccess]
          exact Eq.refl _

end

open Purelib.Riemann.Branches in
/-- Every retained parameter edge has strictly ordered endpoints. -/
def StrictParameterEdges :
    List ClearSheetContinuation.Subdivision.ParameterEdge -> Prop
  | [] => True
  | edge :: remaining =>
      edge.left.parameter < edge.right.parameter ∧
        StrictParameterEdges remaining

section
open Purelib.Data.Rat
open Purelib.Riemann.Branches
/-- A strictly ordered rational interval's midpoint is strictly above its left endpoint. -/
private theorem left_lt_midpoint {left right :
    Fraction.Rational} (proper : left < right) :
    left < ClearSheetContinuation.midpoint left right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (2 : Fraction.Rational))
  · calc
      left * 2 = left + left := by ring1
      _ < left + right :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct proper left
      _ = ClearSheetContinuation.midpoint left right * 2 := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
  · decide

/-- A strictly ordered rational interval's midpoint is strictly below its right endpoint. -/
private theorem midpoint_lt_right {left right :
    Fraction.Rational} (proper : left < right) :
    ClearSheetContinuation.midpoint left right < right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (2 : Fraction.Rational))
  · calc
      ClearSheetContinuation.midpoint left right * 2 =
          left + right := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
      _ < right + right :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct proper right
      _ = right * 2 := by ring1
  · decide

end

section
open Purelib.Riemann.Branches
/-- Concatenating two strictly ordered parameter-edge lists preserves strictness of every edge. -/
private theorem strictParameterEdges_append : forall
    (first second :
      List ClearSheetContinuation.Subdivision.ParameterEdge),
    StrictParameterEdges first -> StrictParameterEdges second ->
      StrictParameterEdges (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _edge :: remaining, second, firstProper, secondProper =>
      ⟨firstProper.1,
        strictParameterEdges_append remaining second firstProper.2 secondProper⟩

/-- Dyadic subdivision of a strictly ordered parameter interval produces strictly ordered edges. -/
theorem dyadicEdges_strictParameterEdges : forall
    (depth : Nat) (left right : Endpoint),
    left.parameter < right.parameter ->
      StrictParameterEdges
        (ClearSheetContinuation.Subdivision.dyadicEdges depth
          left right)
  | 0, _left, _right, proper => ⟨proper, trivial⟩
  | depth + 1, left, right, proper => by
      let middle : Endpoint :=
        ⟨ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      apply strictParameterEdges_append
      · exact dyadicEdges_strictParameterEdges depth left middle
          (left_lt_midpoint proper)
      · exact dyadicEdges_strictParameterEdges depth middle right
          (midpoint_lt_right proper)

end

open Purelib.Polynomial in
/-- Every actual subdivision edge of the prepared path has strictly ordered parameters. -/
def AllEdgesProper {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> Prop
  | _, _, _, _, .nil _point _owner => True
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      StrictParameterEdges preparedHead.subdivision.parameterEdges ∧
        AllEdgesProper preparedTail

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Every complete prepared segment retains exactly the dyadic requests for the given depth and diameter. -/
def AllRequestsDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    {start finish : Gaussian} ->
      {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} ->
        {owner : Owner (polynomial.eval start)} ->
          PreparedPath path owner -> Prop
  | _, _, _, _, .nil _point _owner => True
  | _, _, _, _, .cons _head _tail _owner _headWithin preparedHead
      preparedTail =>
      preparedHead.subdivision.requests =
          PreparedSheetContinuation.Subdivision.dyadicRequests
            depth zeroEndpoint oneEndpoint rootDiameter
              rootDiameterPositive ∧
        AllRequestsDyadic depth rootDiameter rootDiameterPositive preparedTail

open Purelib.Data.Rat in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A prepared path with exact dyadic requests, strict edges, step count and geometric readback.

The certificate retains the original path, starting owner and ambient containment, and states the exact equations tying
its prepared data to the requested refinement. -/
structure CertifiedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) where
  /-- The original clear path is contained in its retained ambient box. -/ within : path.WithinAmbient
  /-- The actual prepared path at the original source owner. -/ prepared : PreparedPath path owner
  /-- Each original segment retains the exact requested dyadic endpoint and diameter list. -/ generated :
    AllRequestsDyadic depth rootDiameter rootDiameterPositive prepared
  /-- Every actual prepared parameter edge has strictly ordered endpoints. -/ prepared_allEdgesProper : AllEdgesProper
    prepared
  /-- The actual prepared step count is `2 ^ depth` times the original segment count. -/ prepared_stepCount :
    prepared.stepCount = 2 ^ depth * path.segmentCount
  /-- The actual prepared clear path is exactly the requested geometric dyadic refinement. -/ prepared_toClearPath :
    prepared.toClearPath = dyadicRefinePath path within depth

constructive_injectivity CertifiedDyadic

open Purelib.Data.Rat in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained dyadic preparation supplied by mesh safety, actual execution or an explicit exact certificate.

Each alternative preserves the original path and source owner, common depth and positive diameter target, together with
its distinct evidence route. -/
inductive DyadicBank {polynomial : GaussianPolynomial} {ambient : Box}
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) : Type
  /-- Retain the exact dyadic mesh-safety certificates and their dependent successor owners. -/ | safe
      (checked : CheckedDyadic depth rootDiameter rootDiameterPositive path
        owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  /-- Retain the actual successful prepared path and its original execution equation. -/ | executed
      (within : path.WithinAmbient)
      (prepared : PreparedPath path owner)
      (success : tryDyadic path within owner depth rootDiameter
        rootDiameterPositive = some prepared) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  /-- Retain the exact per-segment certificates for the executed dyadic preparation. -/ | executedCertified
      (checked : ExecutedCheckedDyadic depth rootDiameter
        rootDiameterPositive path owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner
  /-- Retain the explicit prepared path and its exact request, order, count and geometry equations. -/ | certified
      (certificate : CertifiedDyadic depth rootDiameter rootDiameterPositive
        path owner) :
      DyadicBank depth rootDiameter rootDiameterPositive path owner

constructive_injectivity DyadicBank

namespace DyadicBank

section
open Purelib.Data.Rat
open Purelib.Polynomial
/-- Retain the actual segment execution certificates derived from the original path-safety witness. -/
def ofExecutedPathSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicPathSafe depth rootDiameter rootDiameterPositive
      path within owner) :
    DyadicBank depth rootDiameter rootDiameterPositive path owner :=
  .executedCertified (ExecutedCheckedDyadic.ofPathSafe depth rootDiameter
    rootDiameterPositive path within owner safe)

end

set_option linter.defProp false in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the original path's retained ambient-containment certificate. -/
def within {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} :
    DyadicBank depth rootDiameter rootDiameterPositive path owner ->
      path.WithinAmbient
  | .safe checked => checked.within
  | .executed within _prepared _success => within
  | .executedCertified checked => checked.within
  | .certified certificate => certificate.within

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Read the exact prepared path supplied by the retained dyadic certificates or execution result. -/
def prepared {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} :
    DyadicBank depth rootDiameter rootDiameterPositive path owner ->
      PreparedPath path owner
  | .safe checked => checked.prepared
  | .executed _within prepared _success => prepared
  | .executedCertified checked => checked.prepared
  | .certified certificate => certificate.prepared

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Rat
open Purelib.Polynomial
/-- The sum of retained geometric lower estimates for the integral sample's real coordinate. -/
def integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2)
    {ambient : Box} {start finish : Gaussian}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    Fraction.Rational :=
  bank.prepared.integralRealLower curve differential sheet

/-- The sum of retained geometric lower estimates for the integral sample's negated real coordinate. -/
def negatedIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2)
    {ambient : Box} {start finish : Gaussian}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    Fraction.Rational :=
  bank.prepared.negatedIntegralRealLower curve differential sheet

end

open Purelib.Data.Rat
open Purelib.Polynomial
/-- The retained prepared path has `2 ^ depth` steps per original clear-path segment.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    bank.prepared.stepCount = 2 ^ depth * path.segmentCount := by
  cases bank with
  | safe checked => exact checked.prepared_stepCount
  | executed within prepared success =>
      exact tryDyadic_stepCount path within owner depth rootDiameter
        rootDiameterPositive success
  | executedCertified checked => exact checked.prepared_stepCount
  | certified certificate => exact certificate.prepared_stepCount

/-- The retained prepared geometry is exactly the original path's dyadic refinement at the certified depth.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
theorem prepared_toClearPath_eq_dyadicRefinePath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (bank : DyadicBank depth rootDiameter rootDiameterPositive path owner) :
    bank.prepared.toClearPath = dyadicRefinePath path bank.within depth := by
  cases bank with
  | safe checked => exact checked.prepared_toClearPath_eq_dyadicRefinePath
  | executed within prepared success =>
      exact tryDyadic_toClearPath_eq_dyadicRefinePath path within owner depth
        rootDiameter rootDiameterPositive success
  | executedCertified checked =>
      exact checked.prepared_toClearPath_eq_dyadicRefinePath
  | certified certificate => exact certificate.prepared_toClearPath

end DyadicBank

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Ordered cell models uniformly certified along the original prepared path's selected sheet lift.

The certificate keeps the exact prepared clear path and the supplied differential as indices of every cell's algebraic
certificate. -/
structure Certified {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) where
  /-- The original ordered model cells along the selected prepared-path sheet lift. -/ cells : List CellModel
  /-- Uniform algebraic certificates for these exact cells on the original lifted prepared path. -/ certificates :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells
    (ClearPath.liftOnSheet sheet prepared.toClearPath)

constructive_injectivity Certified

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Two uniformly certified differential models with their retained zero wedge charts and matching cell counts.

Both models use the same original prepared path and sheet; the chart list carries a zero coefficient certificate at
every query. -/
structure HolomorphicCertificate {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) where
  /-- The uniformly certified model for the first differential on the original path and sheet. -/ leftModel : Certified
    curve leftDifferential sheet prepared
  /-- The uniformly certified model for the second differential on the same original path and sheet. -/ rightModel :
    Certified curve rightDifferential sheet prepared
  /-- The retained zero wedge-coefficient charts for the two differentials. -/ charts : List (WedgeChart curve
    leftDifferential rightDifferential)
  /-- There is exactly one retained wedge chart per cell of the first differential model. -/ charts_match_left :
    charts.length = leftModel.cells.length
  /-- There is exactly one retained wedge chart per cell of the second differential model. -/ charts_match_right :
    charts.length = rightModel.cells.length

constructive_injectivity HolomorphicCertificate

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Geometry.Path.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Build uniformly certified constant cells along the exact prepared path and selected sheet.

Each complete segment uses its automatically aligned centers. Endpoint transports and ordered concatenation preserve the
original lifted geometry and link the actual cell certificates. -/
def certify {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      Certified curve differential sheet prepared
  | .nil point owner =>
      { cells := []
        certificates := .nil _ }
  | .cons head tail owner headWithin preparedHead preparedTail => by
      let headCertified :=
        PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      let headCertificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve
        differential
          headCertified.cells
          (ClearPath.liftOnSheet sheet preparedHead.clearPath) := by
        let startEqual := congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
            preparedHead.start_eq
        let finishEqual := congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
            preparedHead.finish_eq
        let castStart := Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.castStart
          startEqual
          headCertified.certificates
        let castFinish := Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.castFinish
          finishEqual
          castStart
        simpa only [CompleteSegment.clearPath,
          ClearPath.liftOnSheet_castStart,
          ClearPath.liftOnSheet_castFinish] using castFinish
      exact
        { cells := headCertified.cells ++ tailCertified.cells
          certificates := by
            rw [toClearPath, ClearPath.liftOnSheet_append]
            exact Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.append _
              headCertificates
              tailCertified.certificates }

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- For exponent zero, the retained geometric estimate is below the certified integral sample's real coordinate.

The estimate follows the original ordered segments and the exact automatically aligned cell models used by
certification. -/
theorem integralRealLower_le_certify {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.integralRealLower curve differential sheet <=
        (Basic.PathModel.mk
          (certify curve differential sheet prepared).cells).integralSample.re
  | .nil _point _owner => by
      rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        PreparedSubdivisionAutomaticModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.integralRealLower curve differential sheet <=
            (Basic.PathModel.mk
              headCertified.cells).integralSample.re := by
        change
          PreparedSubdivisionModelCore.preparedSubdivisionIntegralRealLower
              curve differential sheet preparedHead.subdivision <= _
        have lower :=
          PreparedSubdivisionModelCore.preparedSubdivisionIntegralRealLower_le
            curve differential sheet preparedHead.subdivision centers
              exponentZero
        rw [PreparedSubdivisionAutomaticModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.integralRealLower curve differential sheet <=
            (Basic.PathModel.mk
              tailCertified.cells).integralSample.re :=
        integralRealLower_le_certify curve differential sheet exponentZero
          preparedTail
      change
        preparedHead.integralRealLower curve differential sheet +
            preparedTail.integralRealLower curve differential sheet <=
          (Basic.PathModel.mk
            (headCertified.cells ++ tailCertified.cells)).integralSample.re
      rw [show Basic.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (Basic.PathModel.mk
              headCertified.cells).concat
                (Basic.PathModel.mk
                  tailCertified.cells) from rfl,
        Basic.PathModel.integralSample_concat,
        Basic.add_re]
      exact add_le_add headLower tailLower

/-- For exponent zero, the retained geometric estimate is below the certified integral sample's negated real coordinate.

The estimate follows the original ordered segments and the exact automatically aligned cell models used by
certification. -/
theorem negatedIntegralRealLower_le_certify {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.negatedIntegralRealLower curve differential sheet <=
        -(Basic.PathModel.mk
          (certify curve differential sheet prepared).cells).integralSample.re
  | .nil _point _owner => by
      rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        PreparedSubdivisionAutomaticModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.negatedIntegralRealLower curve differential sheet <=
            -(Basic.PathModel.mk
              headCertified.cells).integralSample.re := by
        change
          PreparedSubdivisionModelCore.preparedSubdivisionNegatedIntegralRealLower
              curve differential sheet preparedHead.subdivision <= _
        have lower :=
          PreparedSubdivisionModelCore.preparedSubdivisionNegatedIntegralRealLower_le
            curve differential sheet preparedHead.subdivision centers
              exponentZero
        rw [PreparedSubdivisionAutomaticModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.negatedIntegralRealLower curve differential sheet <=
            -(Basic.PathModel.mk
              tailCertified.cells).integralSample.re :=
        negatedIntegralRealLower_le_certify curve differential sheet
          exponentZero preparedTail
      change
        preparedHead.negatedIntegralRealLower curve differential sheet +
            preparedTail.negatedIntegralRealLower curve differential sheet <=
          -(Basic.PathModel.mk
            (headCertified.cells ++ tailCertified.cells)).integralSample.re
      rw [show Basic.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (Basic.PathModel.mk
              headCertified.cells).concat
                (Basic.PathModel.mk
                  tailCertified.cells) from rfl,
        Basic.PathModel.integralSample_concat,
        Basic.add_re]
      exact (add_le_add headLower tailLower).trans_eq (by ring1)

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- For exponent zero, the retained geometric estimate is below the certified integral sample's scalar projection onto
the supplied Gaussian direction.

The estimate follows the original ordered segments and the exact automatically aligned cell models used by
certification. -/
theorem directionalIntegralLower_le_certify {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall prepared : PreparedPath path owner,
      prepared.directionalIntegralLower curve differential sheet direction <=
        direction.re *
            (Basic.PathModel.mk
              (certify curve differential sheet prepared).cells).integralSample.re +
          direction.im *
            (Basic.PathModel.mk
              (certify curve differential sheet prepared).cells).integralSample.im
  | .nil _point _owner => by
      unfold directionalIntegralLower certify
        Basic.PathModel.integralSample
      simp only [List.foldr_nil,
        Basic.zero_re,
        Basic.zero_im,
        Fraction.Field.mul_zero_direct, zero_add]
      exact le_rfl
  | .cons _head _tail _owner _headWithin preparedHead preparedTail => by
      let centers :=
        PreparedSubdivisionAutomaticModels.automaticAlignedCenterStates
          curve differential sheet preparedHead.subdivision
      let headCertified :=
        PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision
          curve differential sheet preparedHead.subdivision
      let tailCertified := certify curve differential sheet preparedTail
      have headLower :
          preparedHead.directionalIntegralLower curve differential sheet
              direction <=
            direction.re *
                (Basic.PathModel.mk
                  headCertified.cells).integralSample.re +
              direction.im *
                (Basic.PathModel.mk
                  headCertified.cells).integralSample.im := by
        change
          PreparedSubdivisionModelCore.preparedSubdivisionDirectionalIntegralLower
              curve differential sheet direction preparedHead.subdivision <= _
        have lower :=
          PreparedSubdivisionModelCore.preparedSubdivisionDirectionalIntegralLower_le
            curve differential sheet direction preparedHead.subdivision centers
              exponentZero
        rw [PreparedSubdivisionAutomaticModels.centeredEdges_models
          curve differential sheet preparedHead.subdivision centers] at lower
        exact lower
      have tailLower :
          preparedTail.directionalIntegralLower curve differential sheet
              direction <=
            direction.re *
                (Basic.PathModel.mk
                  tailCertified.cells).integralSample.re +
              direction.im *
                (Basic.PathModel.mk
                  tailCertified.cells).integralSample.im :=
        directionalIntegralLower_le_certify curve differential sheet direction
          exponentZero preparedTail
      change
        preparedHead.directionalIntegralLower curve differential sheet direction +
            preparedTail.directionalIntegralLower curve differential sheet direction <=
          direction.re *
              (Basic.PathModel.mk
                (headCertified.cells ++ tailCertified.cells)).integralSample.re +
            direction.im *
              (Basic.PathModel.mk
                (headCertified.cells ++ tailCertified.cells)).integralSample.im
      rw [show Basic.PathModel.mk
          (headCertified.cells ++ tailCertified.cells) =
            (Basic.PathModel.mk
              headCertified.cells).concat
                (Basic.PathModel.mk
                  tailCertified.cells) from rfl,
        Basic.PathModel.integralSample_concat,
        Basic.add_re,
        Basic.add_im]
      exact (add_le_add headLower tailLower).trans_eq (by ring1)

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Retain the exact constant coefficient certificate of every automatically aligned model cell. -/
def certify_constantCells {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) :
    (prepared : PreparedPath path owner) ->
      Basic.PathModel.ConstantCells
        (certify curve differential sheet prepared).cells
  | .nil _ _ => .nil
  | .cons _head _tail _owner _headWithin preparedHead preparedTail =>
      Constant.PathModel.ConstantCells.append
        (PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision_constantCells
          curve differential sheet preparedHead.subdivision)
          (certify_constantCells curve differential sheet preparedTail)

open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Data in
/-- Uniform model certification preserves the actual prepared path's total step count.

The original retained segment and tail certificates supply the displayed finite geometry. Their exact endpoints, dyadic
depth and source owners are preserved in this scalar readback. -/
@[simp] theorem certify_cellCount {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    (certify curve differential sheet prepared).cells.length =
      prepared.stepCount := by
  induction prepared with
  | nil => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      dsimp only [certify, stepCount]
      rewrite [List.Append.length_append,
        PreparedSubdivisionAutomaticModels.certifyAutomaticallyAlignedSubdivision_cellCount,
        inductionHypothesis]
      exact Eq.refl _

open Purelib.Polynomial in
/-- Certify both differentials and retain the zero wedge charts on the same original prepared path.

The two cell lists and chart list have the same original step count, and each model retains its own differential and
uniform certificates. -/
def certifyHolomorphic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    HolomorphicCertificate curve leftDifferential rightDifferential sheet
      prepared where
  leftModel := certify curve leftDifferential sheet prepared
  rightModel := certify curve rightDifferential sheet prepared
  charts := wedgeCharts curve leftDifferential rightDifferential sheet prepared
  charts_match_left := by
    rw [wedgeCharts_length, certify_cellCount]
  charts_match_right := by
    rw [wedgeCharts_length, certify_cellCount]

end

end PreparedPath

end Purelib.Riemann.Paths.PreparedClearPathModels
