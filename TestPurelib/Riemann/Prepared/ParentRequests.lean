module

import Init.Data.List.OfFn
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction

/-!
# Whole retained parent requests and block-row readback

The actual covered Blocks producer supplies the original global request and
all domain, ownership and preparation evidence. Grouping its stored requests
preserves that request's cached values; no per-row aggregate is acquired.
-/

namespace TestPurelib.Riemann.Prepared.ParentRequests

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
variable {target : Owner (curve.polynomial.eval finish)}

/-- Acquire one original global request and retain its actual all-block grouped error bound.

This quantified producer covers every supplied moving or stationary block
spine, including empty parent rows. Its sole runtime result is the original
whole request, with actual owners and scalar caches unchanged.
-/
def groupedRequest (blocks : Blocks curve.polynomial start source finish target)
    (differential : Differential genus) (sheet : Fin 2) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    {request : Blocks.PrimitiveRequest blocks differential sheet accuracy //
      normSq (gaussianSum (Blocks.ParentCaches.mapRequests (fun _ _ row => gaussianSum row.increments)
        request.2.1 request.2.2.requests) -
          gaussianSum (Blocks.ParentCaches.mapRequests (fun _ _ row =>
            (PathModel.mk (row.blocks.children.map CenteredEdge.model)).integralSample)
              request.2.1 request.2.2.requests)) < accuracy} := by
  let request := blocks.primitiveRequest differential sheet accuracy positive
  have left := Blocks.PrimitiveRequest.primitiveSum_eq_rows request
  have right := Blocks.PrimitiveRequest.integralSample_eq_rows request
  have quantity := (congrArg (fun value => normSq (value - request.2.2.integralSample)) left).trans
    (congrArg (fun value => normSq (gaussianSum (Blocks.ParentCaches.mapRequests
      (fun _ _ row => gaussianSum row.increments) request.2.1 request.2.2.requests) - value)) right)
  exact ⟨request, Eq.mp (congrArg (fun value => value < accuracy) quantity) request.2.2.accurate⟩

/-- The grouped producer returns the exact complete original request, not a reconstructed aggregate or cache view. -/
example (blocks : Blocks curve.polynomial start source finish target) (differential : Differential genus)
    (sheet : Fin 2) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    (groupedRequest blocks differential sheet accuracy positive).val =
      blocks.primitiveRequest differential sheet accuracy positive := (rfl)

/-- A zero-floor request preserves the whole actual original aggregate before every row is read. -/
example {blocks : Blocks curve.polynomial start source finish target} {differential : Differential genus}
    {sheet : Fin 2} {accuracy : Fraction.Rational}
    (request : Blocks.PrimitiveRequest blocks differential sheet accuracy) :
    request.2.2.refine request.2.1.proper 0 = request.2.2 :=
  request.2.2.refine_zero request.2.1.proper

/-- Reading actual refined model indices uses the one supplied global floor at every retained parent occurrence. -/
example {blocks : Blocks curve.polynomial start source finish target} {differential : Differential genus}
    {sheet : Fin 2} {accuracy : Fraction.Rational}
    (request : Blocks.PrimitiveRequest blocks differential sheet accuracy) (minimum : Nat) :
    Blocks.ParentCaches.mapRequests (fun _ cache row =>
      (List.ofFn (fun index : Fin cache.parents.length => (row.get index).request.index))) request.2.1
        (request.2.2.requests.refine request.2.2.localTarget_positive request.2.1.proper minimum) =
      Blocks.ParentCaches.mapRequests (fun _ cache row =>
        List.ofFn (fun index : Fin cache.parents.length =>
          ((row.refine request.2.2.localTarget_positive cache.proper minimum).get index).request.index))
            request.2.1 request.2.2.requests :=
  Blocks.ParentCaches.mapRequests_refine _ request.2.1 request.2.2.requests
    request.2.2.localTarget_positive minimum

end TestPurelib.Riemann.Prepared.ParentRequests
