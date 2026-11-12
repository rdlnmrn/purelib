module

import all Purelib.Riemann.Paths.PreparedPathParentCaches

/-! # Whole original ordered request-row traversal

This regression reduces the original hidden row procedure solely to compare
its complete former operation at arbitrary actual Blocks and caches.
-/

namespace TestPurelib.Riemann.ParentRequestRows

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {sheet : Fin 2} {allowance : Fraction.Rational}

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Blocks

/-- The complete original request-row procedure at arbitrary retained parent caches. -/
private def former {Value : Type u}
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), RequestedParents count allowance cache.parents → Value) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks), RequestedParents count allowance caches.parents → List Value
  | _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, .cons covered tail, caches, requests =>
      let rows := requests.split caches.1.parents (ParentCaches.parents (blocks := tail) caches.2)
      read covered caches.1 rows.1 :: former read (blocks := tail) caches.2 rows.2
  | _, _, _, _, .handoff _ tail, caches, requests => former read (blocks := tail) caches requests
termination_by structural _ _ _ _ blocks _ _ => blocks

/-- The shared traversal preserves the whole former result, including stationary handoffs and literal suffixes. -/
private theorem former_eq {Value : Type u}
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), RequestedParents count allowance cache.parents → Value) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks)
      (requests : RequestedParents count allowance caches.parents),
      ParentCaches.mapRequests read caches requests = former read caches requests
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons covered tail, caches, requests =>
      congrArg (List.cons (read covered caches.1 (requests.split caches.1.parents caches.2.parents).1))
        (former_eq read (blocks := tail) caches.2 (requests.split caches.1.parents caches.2.parents).2)
  | _, _, _, _, .handoff _ tail, caches, requests => former_eq read (blocks := tail) caches requests
termination_by structural _ _ _ _ blocks _ _ => blocks

end TestPurelib.Riemann.ParentRequestRows
