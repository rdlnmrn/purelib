module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Chain
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Cached
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.PreparedBankRootChains

/-! # The actual signed root chain on the SAME flattened refined raw word

Every head consumes its original retained View, endpoint queries and
acquired child-root chain. The actual source and retention links connect
those SAME Owners. The original remaining Geometry supplies the literal
tail, including every stationary or repeated outer occurrence.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Construct the genuine signed root chain on the SAME flattened actual acquired children.

The direct Subdivision constructor eliminator reads its stored Owner data;
its explicit sourceOwner projection indexes the returned comparison. The
actual source/moving endpoint QueryAt records reindex the stored child
roots by their OWN original name readbacks before composition. The actual
stationary source and retention links supply both signed bridges. No View,
query, transport, reserve reset, root chain or source preparation is rerun.
-/
def roots (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right)
    {current : PreparedSheetContinuation.Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) :
    RootChain (parents diameter positive budget subdivision centers fits trace geometry)
      (ownerName subdivision.sourceOwner) (ownerName subdivision.terminalOwner) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : PreparedTraceBudget.Trace budget subdivision fits) →
      (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
        RootChain (parents diameter positive budget subdivision centers fits trace geometry)
          (ownerName subdivision.sourceOwner) (ownerName subdivision.terminalOwner))
    subdivision
    (fun _ storedOwner _centers _fits _trace _geometry => .nil (NamedEquivalent.refl (ownerName storedOwner)))
    (fun _current inherited _request _cached _ordered _small remaining centers fits _trace geometry =>
      let endpoints := geometry.1.val.endpoints
      let childRoots := PreparedBankRootChains.RootChain.castNames
        (endpoints.source.name_eq.symm.trans
          (PreparedBankRootChains.ownerName_eq_certificate endpoints.source.owner))
        (endpoints.moving.name_eq.symm.trans
          (PreparedBankRootChains.ownerName_eq_certificate endpoints.moving.owner))
        geometry.1.val.acquisition.roots
      let entry := endpoints.sourceEquivalent (curve := Fibre.frameCurve frame) (differential := basis)
      let seam := endpoints.followingEquivalent (curve := Fibre.frameCurve frame) (differential := basis)
      let first := RootChain.changeStart
        (first := ownerName inherited) (middle := ownerName endpoints.source.owner)
        (last := ownerName endpoints.moving.owner) entry childRoots
      let following := roots diameter positive budget remaining centers.2 fits.2.2
        geometry.1.val.nextTrace geometry.2
      let last := RootChain.changeStart
        (first := ownerName endpoints.moving.owner) (middle := ownerName remaining.sourceOwner)
        (last := ownerName remaining.terminalOwner) seam following
      RootChain.append
        (first := ownerName inherited) (middle := ownerName endpoints.moving.owner)
        (last := ownerName remaining.terminalOwner) first last)
    centers fits trace geometry
termination_by structural subdivision

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache.Geometry

end
