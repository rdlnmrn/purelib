module

import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint
import Purelib.Data.Gaussian.Norm.Basic

/-!
# Original Legendre primitive endpoint construction

The endpoint payment requests precede the common source refinement. The
three original primitive tables then consume one actual root witness and
the same retained inverse-model power cache.
-/

namespace TestPurelib.Curves.Legendre.PrimitiveEndpoints

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Curves.Legendre
open Periods.Jets.Source

/-- All three source primitive endpoints pay their targets after the original common model is selected once. -/
private theorem requestedEndpoints {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {point : Canonical}
    (sample : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (zeroOriginal : ZeroDenotation sample) (oneOriginal : OneDenotation sample)
    (scalarOriginal : ScalarDenotation sample) (floor : Nat) (target : Rational) (positive : 0 < target) :
    let requests := endpointRequests sample floor target positive
    let cache := Cache.ofPatch patch
    let request := cache.request requests.stage target positive
    let root := selectPrimitiveRoot sample request.selection.stage target positive
    let endpoint := request.attachEndpoint sample requests root zeroOriginal oneOriginal scalarOriginal
      request.selection.lower
    Norm.Basic.normSq endpoint.zero.residual < target ∧
      Norm.Basic.normSq endpoint.one.residual < target ∧
      Norm.Basic.normSq endpoint.scalar.residual < target := by
  dsimp only
  exact ⟨Request.Endpoint.zero_lt _ inside, Request.Endpoint.one_lt _ inside,
    Request.Endpoint.scalar_lt _ inside⟩

example {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {point : Canonical}
    (sample : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (zeroOriginal : ZeroDenotation sample) (oneOriginal : OneDenotation sample)
    (scalarOriginal : ScalarDenotation sample) (floor : Nat) (target : Rational) (positive : 0 < target) :
    let requests := endpointRequests sample floor target positive
    let cache := Cache.ofPatch patch
    let request := cache.request requests.stage target positive
    let root := selectPrimitiveRoot sample request.selection.stage target positive
    let endpoint := request.attachEndpoint sample requests root zeroOriginal oneOriginal scalarOriginal
      request.selection.lower
    Norm.Basic.normSq endpoint.zero.residual < target ∧
      Norm.Basic.normSq endpoint.one.residual < target ∧
      Norm.Basic.normSq endpoint.scalar.residual < target :=
  requestedEndpoints sample inside zeroOriginal oneOriginal scalarOriginal floor target positive

end TestPurelib.Curves.Legendre.PrimitiveEndpoints
