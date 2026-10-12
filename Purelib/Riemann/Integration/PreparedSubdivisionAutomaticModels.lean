module
import Purelib.Data.List.Membership
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Readings.PreparedBoundaryEquivalence

public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Automatic models for prepared subdivisions

Executable canonical centres, boundary witnesses, and certification wrappers
for a complete prepared subdivision.  This layer depends only on the shared
model core, not on the separate parent-refinement proof layer.
-/

namespace Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-- The original rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational

/-- An ordered finite list of polynomial cell models. -/
abbrev PathModel := Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Retain each prepared subdivision step's canonical center state in a dependent family.

The recursion follows the original requests and cached source owners, keeping the exact center state of each original
edge. -/
def canonicalCenterStates {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision
  | .stop _ _ => ()
  | .next left owner request cached ordered small remaining =>
      let head := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      (PreparedConstantModels.PreparedEdge.CenterState.canonical
          head,
        canonicalCenterStates curve differential sheet remaining)

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- Sum the denominator projection-box real lower estimates at the canonical centers.

The sum follows the original prepared subdivision and uses each edge's exact canonical center and retained denominator
projection box. -/
def canonicalBallIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      let center :=
        PreparedConstantModels.PreparedEdge.CenterState.canonical
          edge
      edge.centeredBallIntegralRealDyadicLower center +
        canonicalBallIntegralRealLower curve differential sheet remaining

/-- Sum the denominator projection-box lower estimates for the negated real integral at the canonical centers.

Every summand uses the original step and its exact canonical center; the terminal subdivision contributes zero. -/
def canonicalBallNegatedIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      let center :=
        PreparedConstantModels.PreparedEdge.CenterState.canonical
          edge
      edge.centeredBallNegatedIntegralRealDyadicLower center +
        canonicalBallNegatedIntegralRealLower curve differential sheet remaining

end

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Polynomial
/-- The canonical subdivision real estimate equals the corresponding sum over its canonical centered edges. -/
theorem canonicalBallIntegralRealLower_eq_centeredEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall subdivision : PreparedSubdivision segment within left owner,
      canonicalBallIntegralRealLower curve differential sheet subdivision =
        centeredEdgesBallIntegralRealLower
          (centeredEdges curve differential sheet subdivision
            (canonicalCenterStates curve differential sheet subdivision))
  | .stop _ _ => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [canonicalBallIntegralRealLower, centeredEdges,
        canonicalCenterStates, centeredEdgesBallIntegralRealLower,
        List.foldr_cons, CenteredEdge.ballIntegralRealLower]
      rw [canonicalBallIntegralRealLower_eq_centeredEdges curve differential
        sheet remaining]
      rfl

/-- The canonical subdivision negated-real estimate equals the corresponding sum over its canonical centered edges. -/
theorem canonicalBallNegatedIntegralRealLower_eq_centeredEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall subdivision : PreparedSubdivision segment within left owner,
      canonicalBallNegatedIntegralRealLower curve differential sheet subdivision =
        centeredEdgesBallNegatedIntegralRealLower
          (centeredEdges curve differential sheet subdivision
            (canonicalCenterStates curve differential sheet subdivision))
  | .stop _ _ => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [canonicalBallNegatedIntegralRealLower, centeredEdges,
        canonicalCenterStates, centeredEdgesBallNegatedIntegralRealLower,
        List.foldr_cons, CenteredEdge.ballNegatedIntegralRealLower]
      rw [canonicalBallNegatedIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining]
      rfl

end

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
/-- For exponent zero, the canonical ball estimate is below the actual centered path integral's real coordinate. -/
theorem canonicalBallIntegralRealLower_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (exponentZero : differential.exponent = 0) :
    canonicalBallIntegralRealLower curve differential sheet subdivision <=
      (Basic.PathModel.mk
        ((centeredEdges curve differential sheet subdivision
          (canonicalCenterStates curve differential sheet subdivision)).map
            CenteredEdge.model)).integralSample.re := by
  rw [canonicalBallIntegralRealLower_eq_centeredEdges curve differential sheet
    subdivision]
  exact centeredEdgesBallIntegralRealLower_le exponentZero _

/-- For exponent zero, the canonical ball estimate is below the negated real coordinate of the actual centered path
integral. -/
theorem canonicalBallNegatedIntegralRealLower_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (exponentZero : differential.exponent = 0) :
    canonicalBallNegatedIntegralRealLower curve differential sheet subdivision <=
      -(Basic.PathModel.mk
        ((centeredEdges curve differential sheet subdivision
          (canonicalCenterStates curve differential sheet subdivision)).map
            CenteredEdge.model)).integralSample.re := by
  rw [canonicalBallNegatedIntegralRealLower_eq_centeredEdges curve differential
    sheet subdivision]
  exact centeredEdgesBallNegatedIntegralRealLower_le exponentZero _

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Every edge built from the canonical center family retains its exact canonical center state.

Each actual list occurrence is either the displayed head or an occurrence in the retained tail. The canonical dependent
center family supplies the head identity and the recursive tail certificate without changing edge owners or caches. -/
theorem centeredEdges_canonical_center {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : PreparedSubdivision segment within left owner) :
    ∀ centered ∈ centeredEdges curve differential sheet subdivision
        (canonicalCenterStates curve differential sheet subdivision),
      centered.center =
        PreparedConstantModels.PreparedEdge.CenterState.canonical
          centered.edge := by
  induction subdivision with
  | stop endpoint owner =>
      intro centered membership
      nomatch membership
  | @next left owner request cached ordered small remaining induction =>
      intro centered membership
      rcases Purelib.Data.List.Membership.mem_cons.mp membership with equal | membership
      · subst centered
        rfl
      · exact induction centered membership

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Readings in
/-- Retain the adjacent steps' actual endpoint coefficient names and their operational equivalence.

The next step uses the first step's advanced owner; both caches and the common sheet are preserved in the boundary
comparison. -/
def boundaryWitness {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (nextRequest : StepRequest)
    (nextCached : PreparedSheetContinuation.CachedSource segment
      request.endpoint
        (PreparedSheetContinuation.advance segment within left
          owner request small) nextRequest)
    (nextOrdered : request.endpoint.parameter <=
      nextRequest.endpoint.parameter)
    (nextSmall : ClearSheetContinuation.variationBound segment
      request.endpoint.parameter nextRequest.endpoint.parameter <
        (PreparedSheetContinuation.prepared
          segment request.endpoint
          (PreparedSheetContinuation.advance segment within left
            owner request small) nextRequest).track.initial.clearance.bound)
    (sheet : Fin 2) : BoundaryWitness :=
  let parent := edgeOfStep curve differential segment within left owner request
    cached ordered small sheet
  let child := edgeOfStep curve differential segment within request.endpoint
    (PreparedSheetContinuation.advance segment within left owner
      request small) nextRequest nextCached nextOrdered nextSmall sheet
  { parentName := (parent.coefficient 1 endpointInside).name
    childName := (child.coefficient 0 child.baseInside).name
    equivalent :=
      PreparedBoundaryEquivalence.adjacentCoefficientEquivalent
        curve differential segment within left owner request cached ordered small
          nextRequest nextCached nextOrdered nextSmall sheet }

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- A boundary-witness constructor for a step at the retained source owner.

The constructor consumes the actual next request, cache, ordering and clearance proof, so its witness stays tied to
those exact step inputs. -/
abbrev BoundaryBuilder {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    {ambient : Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))) :=
  (request : StepRequest) ->
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request) ->
      (ordered : left.parameter <= request.endpoint.parameter) ->
      (small : ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (PreparedSheetContinuation.prepared segment left owner
            request).track.initial.clearance.bound) -> BoundaryWitness

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Construct boundary witnesses along a subdivision, retaining an optional witness builder from its predecessor.

Each step forms the builder for the following original owner. A witness is emitted only when a predecessor builder is
present. -/
def automaticBoundaryWitnessesFrom {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (previous : Option
      (BoundaryBuilder curve segment left owner)) :
    PreparedSubdivision segment within left owner -> List BoundaryWitness
  | .stop _ _ => []
  | .next left owner request cached ordered small remaining =>
      let current : BoundaryBuilder curve segment request.endpoint
          (PreparedSheetContinuation.advance segment within left
            owner request small) :=
        fun nextRequest nextCached nextOrdered nextSmall =>
          boundaryWitness curve differential left owner request cached ordered
            small nextRequest nextCached nextOrdered nextSmall sheet
      let tail := automaticBoundaryWitnessesFrom curve differential sheet
        (some current) remaining
      match previous with
      | none => tail
      | some build => build request cached ordered small :: tail

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Construct the ordered coefficient-name comparisons at every adjacent subdivision boundary.

The first step has no predecessor witness; subsequent comparisons retain both actual caches and the advanced root
owners. -/
def automaticBoundaryWitnesses {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    List BoundaryWitness :=
  automaticBoundaryWitnessesFrom curve differential sheet
    none subdivision

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- With a retained predecessor builder, there is one boundary witness per subdivision step. -/
private theorem automaticBoundaryWitnessesFrom_some_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (builder : BoundaryBuilder curve segment left owner) :
    (automaticBoundaryWitnessesFrom curve differential sheet (some builder)
      subdivision).length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      simp only [automaticBoundaryWitnessesFrom,
        PreparedSheetContinuation.Subdivision.stepCount_next,
        List.length_cons]
      exact congrArg Nat.succ (inductionHypothesis _)

/-- The number of adjacent boundary witnesses is the predecessor of the subdivision step count. -/
@[simp] theorem automaticBoundaryWitnesses_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (automaticBoundaryWitnesses curve differential sheet subdivision).length =
      subdivision.stepCount.pred := by
  cases subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining =>
      simp only [automaticBoundaryWitnesses,
        automaticBoundaryWitnessesFrom,
        PreparedSheetContinuation.Subdivision.stepCount_next]
      exact automaticBoundaryWitnessesFrom_some_length curve differential sheet
        remaining _

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- A center-state constructor for the next request at the retained source owner and sheet.

The result is indexed by the exact edge assembled from the supplied cache, ordering and clearance evidence. -/
abbrev CenterBuilder {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (sheet : Fin 2) :=
  (request : StepRequest) ->
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request) ->
      (ordered : left.parameter <= request.endpoint.parameter) ->
      (small : ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (PreparedSheetContinuation.prepared segment left owner
            request).track.initial.clearance.bound) ->
        PreparedConstantModels.PreparedEdge.CenterState
          (edgeOfStep curve differential segment within left owner request
            cached ordered small sheet)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Construct center states from an optional predecessor builder and successive endpoint comparisons.

Without a predecessor the first center is canonical. Each following center is aligned to the original previous edge's
canonical endpoint query using the actual boundary equivalence. -/
def automaticAlignedCenterStatesFrom {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (previous : Option
      (CenterBuilder curve differential segment within left owner sheet)) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision
  | .stop _ _ => ()
  | .next left owner request cached ordered small remaining =>
      let parent := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      let center :
          PreparedConstantModels.PreparedEdge.CenterState parent :=
        match previous with
        | none =>
            PreparedConstantModels.PreparedEdge.CenterState.canonical
              parent
        | some build => build request cached ordered small
      let current : CenterBuilder curve differential segment within
          request.endpoint
          (PreparedSheetContinuation.advance segment within left
            owner request small) sheet :=
        fun nextRequest nextCached nextOrdered nextSmall =>
          let child := edgeOfStep curve differential segment within
            request.endpoint
            (PreparedSheetContinuation.advance segment within left
              owner request small) nextRequest nextCached nextOrdered nextSmall
                sheet
          let query :=
            PreparedConstantModels.PreparedEdge.QueryState.canonical
              parent 1 endpointInside
          PreparedConstantModels.PreparedEdge.alignedChildAt parent
            child query
              (PreparedBoundaryEquivalence.adjacentCoefficientEquivalent
                curve differential segment within left owner request cached
                  ordered small nextRequest nextCached nextOrdered nextSmall sheet)
      (center, automaticAlignedCenterStatesFrom curve differential sheet
        (some current) remaining)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Construct the canonical first center and the successively endpoint-aligned centers of the original subdivision.

Each later state is selected from the exact adjacent coefficient equivalence, retaining the original step owners and
caches. -/
def automaticAlignedCenterStates {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    CenterStates curve differential sheet subdivision :=
  automaticAlignedCenterStatesFrom curve differential sheet none subdivision

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- Build constant cell models and uniform algebraic certificates along the original lifted subdivision.

Each cell uses its edge's base-reading model; endpoint equalities and the original edge certificate connect the ordered
cells to the retained clear path. -/
def certifySubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CertifiedSubdivision curve differential sheet subdivision
  | .stop endpoint owner =>
      { cells := []
        certificates := .nil _ }
  | .next left owner request cached ordered small remaining => by
      let head : PreparedConstantModels.PreparedEdge curve
          differential :=
        { ambient := ambient
          start := start
          finish := finish
          segment := segment
          within := within
          left := left
          owner := owner
          request := request
          cached := cached
          ordered := ordered
          small := small
          sheet := sheet }
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons
            (by
              change head.model.start = segment.pointAt left.parameter
              change head.localSegment.pointAt 0 = segment.pointAt left.parameter
              rw [head.localSegment.pointAt_zero])
            (by
              change head.model.finish =
                segment.pointAt request.endpoint.parameter
              change head.localSegment.pointAt 1 =
                segment.pointAt request.endpoint.parameter
              rw [head.localSegment.pointAt_one])
            head.validCertificate tail.certificates }

/-- Build uniformly certified constant cells from the supplied dependent center family.

The constructor retains every actual center and cached step, then joins the cell certificates along the original
sheet-lifted subdivision. -/
def certifyCenteredSubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision ->
        CertifiedSubdivision curve differential sheet subdivision
  | .stop endpoint owner, _ =>
      { cells := []
        certificates := .nil _ }
  | .next left owner request cached ordered small remaining, centers => by
      let head : PreparedConstantModels.PreparedEdge curve
          differential :=
        { ambient := ambient
          start := start
          finish := finish
          segment := segment
          within := within
          left := left
          owner := owner
          request := request
          cached := cached
          ordered := ordered
          small := small
          sheet := sheet }
      let tail := certifyCenteredSubdivision curve differential sheet
        remaining centers.2
      exact
        { cells := head.centeredModel centers.1 :: tail.cells
          certificates := .cons
            (by
              change (head.centeredModel centers.1).start =
                segment.pointAt left.parameter
              change head.localSegment.pointAt 0 =
                segment.pointAt left.parameter
              rw [head.localSegment.pointAt_zero])
            (by
              change (head.centeredModel centers.1).finish =
                segment.pointAt request.endpoint.parameter
              change head.localSegment.pointAt 1 =
                segment.pointAt request.endpoint.parameter
              rw [head.localSegment.pointAt_one])
            (head.centeredValidCertificate curve differential centers.1)
            tail.certificates }

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Reading models from the supplied centered edges gives exactly the cells of the centered subdivision certificate. -/
theorem centeredEdges_models {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model =
        (certifyCenteredSubdivision curve differential sheet subdivision
          centers).cells
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons, certifyCenteredSubdivision,
        CenteredEdge.model]
      rw [centeredEdges_models curve differential sheet remaining centers.2]
      rfl

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Certify the original subdivision using its automatically aligned center family.

The resulting cells and uniform certificates retain the exact center states produced by the endpoint-comparison
construction. -/
def certifyAutomaticallyAlignedSubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    CertifiedSubdivision curve differential sheet subdivision :=
  certifyCenteredSubdivision curve differential sheet subdivision
    (automaticAlignedCenterStates curve differential sheet subdivision)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Retain each supplied center value as the exact constant coefficient of its certified cell. -/
def certifyCenteredSubdivision_constantCells {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      (centers : CenterStates curve differential sheet subdivision) ->
        Basic.PathModel.ConstantCells
          (certifyCenteredSubdivision curve differential sheet subdivision
            centers).cells
  | .stop _ _, _ => .nil
  | .next left owner _request _cached _ordered _small remaining, centers =>
      .cons
        { coefficient := centers.1.value
          polynomial_eq := rfl }
        (certifyCenteredSubdivision_constantCells curve differential sheet
          remaining centers.2)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- Retain the automatically aligned center values as the exact constant coefficients of the certified cells. -/
def certifyAutomaticallyAlignedSubdivision_constantCells {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    Basic.PathModel.ConstantCells
      (certifyAutomaticallyAlignedSubdivision curve differential sheet
        subdivision).cells :=
  certifyCenteredSubdivision_constantCells curve differential sheet
    subdivision
      (automaticAlignedCenterStates curve differential sheet subdivision)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Centered certification retains exactly one cell for each original subdivision step. -/
@[simp] theorem certifyCenteredSubdivision_cellCount {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    (certifyCenteredSubdivision curve differential sheet subdivision
      centers).cells.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ (inductionHypothesis centers.2)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Automatic alignment and certification retain the original subdivision step count. -/
@[simp] theorem certifyAutomaticallyAlignedSubdivision_cellCount {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (certifyAutomaticallyAlignedSubdivision curve differential sheet
      subdivision).cells.length = subdivision.stepCount :=
  certifyCenteredSubdivision_cellCount curve differential sheet subdivision
    (automaticAlignedCenterStates curve differential sheet subdivision)

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Base-reading certification retains exactly one cell for each original subdivision step. -/
@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Read the ordered cell list of a certified subdivision as a path model. -/
def pathModel {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    {sheet : Fin 2}
    {subdivision : PreparedSubdivision segment within left owner}
    (certified : CertifiedSubdivision curve differential sheet subdivision) :
    PathModel :=
  ⟨certified.cells⟩

end

end Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
