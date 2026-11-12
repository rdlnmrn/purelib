module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.List.Membership

/-! # Original physical-query distances on retained paid centered parents

The same original subdivision and center cache supply every actual edge
fraction. A segment-wide distance payment passes to these exact fractions,
then through the original covered-parent factory equality. No parent, Owner,
root observation, source model or trace is reconstructed by this proof.
-/

public section

namespace Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Actual centered child fractions preserve the original whole-segment pointwise distance payment. -/
theorem centeredEdges_distance_le {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) {ambient : Box} {start finish center : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : Subdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) {bound : Rational}
    (bounded : ∀ time : Rational, 0 ≤ time ∧ time ≤ 1 → Norm.Basic.normSq (center - segment.pointAt time) ≤ bound)
    (parent : CenteredEdge curve differential)
    (member : parent ∈ centeredEdges curve differential sheet subdivision centers)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq (center - parent.edge.point fraction) ≤ bound := by
  rewrite [centeredEdges_point curve differential sheet subdivision centers parent member fraction]
  exact bounded _ (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
    parent.edge.ordered fraction inside)

end Purelib.Riemann.Integration.PreparedSubdivisionModelCore

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges_distance_le)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
variable {ambient : Box} {start finish center : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest} {sheet : Fin 2} {count : Nat}
variable {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}

/-- Every actual stored paid parent reads the SAME original segment and inherits its all-parameter distance payment. -/
theorem point_distance_le (parents : Parents basis sheet count retained) {bound : Rational}
    (bounded : ∀ time : Rational, 0 ≤ time ∧ time ≤ 1 → Norm.Basic.normSq (center - segment.pointAt time) ≤ bound)
    (parent : CenteredEdge curve basis) (member : parent ∈ parents.covered.parents)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq (center - parent.edge.point fraction) ≤ bound := by
  rewrite [parents.parents_eq] at member
  exact centeredEdges_distance_le curve basis sheet retained.traced.prepared.subdivision parents.centers
    bounded parent member fraction inside

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
