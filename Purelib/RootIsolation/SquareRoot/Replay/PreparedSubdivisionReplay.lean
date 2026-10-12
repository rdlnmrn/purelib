module
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Exact prepared-spine provenance from finite requests

For a fixed segment and incoming owner, the request list determines the whole
prepared subdivision, including every canonical cached source and every
transported successor owner.  A certified dyadic bank can therefore be
associated with the original bank without rerunning its preparation merely
to compare spines.  This does not identify an unknown incoming seed owner or
prove that a saved adaptive depth was the original selected depth.

The sole import is the existing finite bank-cache/provenance interface; no
upstream algebra or generated certificate dependency is added.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedSubdivisionReplay

open Purelib.Riemann.Branches.PreparedSheetContinuation

variable {polynomial : Riemann.Branches.PreparedSheetContinuation.GaussianPolynomial} {ambient :
  Riemann.Branches.PreparedSheetContinuation.Box} {start finish : Riemann.Branches.PreparedSheetContinuation.Gaussian}

/-- The finite requests determine all executable continuation data, not just
the parameter mesh.  Cache equality follows from its canonical equation. -/
theorem subdivision_eq_of_requests_eq
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Riemann.Branches.PreparedSheetContinuation.Endpoint}
    {owner : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt left.parameter))}
    (first second : Riemann.Branches.PreparedSheetContinuation.Subdivision segment within left owner)
    (same : first.requests = second.requests) : first = second := by
  induction first with
  | stop current source =>
      cases second with
      | stop => rfl
      | next _ _ request cached ordered small remaining =>
          simp only [Riemann.Branches.PreparedSheetContinuation.Subdivision.requests_stop,
            Riemann.Branches.PreparedSheetContinuation.Subdivision.requests_next] at same
          cases same
  | next current source request cached ordered small remaining ih =>
      cases second with
      | stop =>
          simp only [Riemann.Branches.PreparedSheetContinuation.Subdivision.requests_stop,
            Riemann.Branches.PreparedSheetContinuation.Subdivision.requests_next] at same
          cases same
      | next _ _ otherRequest otherCache otherOrdered otherSmall otherRemaining =>
          change request :: remaining.requests = otherRequest :: otherRemaining.requests at same
          have requestsEqual := List.cons.inj same |>.1
          have tailsEqual := List.cons.inj same |>.2
          cases requestsEqual
          have cachesEqual := cached.eq_canonical.trans otherCache.eq_canonical.symm
          cases cachesEqual
          have tails := ih otherRemaining tailsEqual
          cases tails
          rfl

/-- The complete segment wrapper adds only the endpoint proof; it cannot
hide a different continuation history behind identical requests. -/
theorem completeSegment_eq_of_requests_eq
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval start)}
    (first second : Riemann.Paths.PreparedClearPathModels.CompleteSegment segment within owner)
    (same : first.subdivision.requests = second.subdivision.requests) : first = second := by
  cases first with
  | mk first firstEndpoint =>
    cases second with
    | mk second secondEndpoint =>
      have equal := SquareRoot.Replay.PreparedSubdivisionReplay.subdivision_eq_of_requests_eq first second same
      cases equal
      rfl

open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath

/-- Once the incoming owner, original path and dyadic requests are fixed,
all certified bank routes retain exactly the same dependent owner chain. -/
theorem preparedPath_eq_of_dyadic_requests
    (depth : Nat) (diameter : Riemann.Branches.PreparedSheetContinuation.Coordinate) (positive : 0 < diameter)
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner :
      Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval start)}
    (first second : Riemann.Paths.PreparedClearPathModels.PreparedPath path owner)
    (firstGenerated : Riemann.Paths.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth diameter positive
      first)
    (secondGenerated : Riemann.Paths.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth diameter positive
      second) : first = second := by
  induction first with
  | nil point source => cases second; rfl
  | cons head tail source within firstHead firstTail ih =>
      cases second with
      | cons _ _ _ otherWithin secondHead secondTail =>
          have heads := SquareRoot.Replay.PreparedSubdivisionReplay.completeSegment_eq_of_requests_eq firstHead
            secondHead
            (firstGenerated.1.trans secondGenerated.1.symm)
          cases heads
          have tails := ih secondTail firstGenerated.2 secondGenerated.2
          cases tails
          rfl

/-- The cached bank's existing generated-request proof supplies exact
canonical provenance automatically.  No equality of numerical root boxes or
additional caller-supplied continuation-history certificate is needed. -/
theorem bank_prepared_eq
    {depth : Nat} {diameter : Riemann.Branches.PreparedSheetContinuation.Coordinate} {positive : 0 < diameter}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner :
      Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval start)}
    (first second : Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth diameter positive path owner) :
    first.prepared = second.prepared :=
  SquareRoot.Replay.PreparedSubdivisionReplay.preparedPath_eq_of_dyadic_requests depth diameter positive first.prepared
    second.prepared
    (SquareRoot.Preparation.Bank.Cache.DyadicBank.prepared_provenance first).1
      (SquareRoot.Preparation.Bank.Cache.DyadicBank.prepared_provenance second).1

/-- Whole certified caches agree as well: after the prepared path, all their
remaining fields are proofs of its finite provenance and geometry. -/
theorem certifiedCache_eq_of_prepared_eq
    {depth : Nat} {diameter : Riemann.Branches.PreparedSheetContinuation.Coordinate} {positive : 0 < diameter}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner :
      Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval start)}
    (first second : Riemann.Paths.PreparedClearPathModels.PreparedPath.CertifiedDyadic depth diameter positive path
      owner)
    (same : first.prepared = second.prepared) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Two dyadic banks with the same original path, owner, depth and diameter retain equal certified caches.

Equality follows from their exact generated-request provenance and canonical prepared subdivisions. -/
theorem bank_cache_eq
    {depth : Nat} {diameter : Riemann.Branches.PreparedSheetContinuation.Coordinate} {positive : 0 < diameter}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner :
      Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval start)}
    (first second : Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth diameter positive path owner) :
    (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache first) = (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache
      second) :=
  SquareRoot.Replay.PreparedSubdivisionReplay.certifiedCache_eq_of_prepared_eq
    (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache first) (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache
    second) (SquareRoot.Replay.PreparedSubdivisionReplay.bank_prepared_eq first second)

end Purelib.RootIsolation.SquareRoot.Replay.PreparedSubdivisionReplay
