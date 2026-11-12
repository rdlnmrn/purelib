module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Chain
public import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition.Directed
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Directed grouping of the SAME actual geometric child word

Each actual original block contributes its own positive displacement
factors and original signed subedge certificates. Literal empty branches,
whole center/Owner transports and original parent-list factories remain
separate. This proposition is finite source grouping, not a new runtime
root, query, geometry or independently canonical cycle construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements (DirectedRefinement)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Construct the all-query rooted refinement from the SAME original raw centered parents to their actual children.

The original supplied centers determine each coarse parent, without center
selection or View reconstruction. The actual acquisition supplies the
single-parent refinement and its original budget/chain/root caches. The
literal remaining geometry supplies the next block in order. All parent
and child Owners remain separate; each query comparison has its own actual
parent location and NamedEquivalent witness from the original constructor.
-/
theorem directedRefinement (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right)
    {current : PreparedSheetContinuation.Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) :
    DirectedRefinement (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)
      (parents diameter positive budget subdivision centers fits trace geometry) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : PreparedTraceBudget.Trace budget subdivision fits) →
      (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
        DirectedRefinement (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers)
          (parents diameter positive budget subdivision centers fits trace geometry))
    subdivision
    (fun _ _ _centers _fits _trace _geometry => .nil)
    (fun _current _inherited _request _cached _ordered _small remaining centers fits _trace geometry =>
      let head := geometry.1.val.acquisition.directedRefinement
      let following := directedRefinement diameter positive budget remaining centers.2 fits.2.2
        geometry.1.val.nextTrace geometry.2
      head.append following)
    centers fits trace geometry
termination_by structural subdivision

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

end
