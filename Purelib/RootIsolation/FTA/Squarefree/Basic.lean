module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Retained finite squarefree root-isolation results

The numerical result retains the exact degree-sized isolation, owner-selection
procedure and finite maximality certificate for the original polynomial.
The coupled adapter keeps that same numerical result and its degree-indexed
track readbacks without selecting new owners.
-/

namespace Purelib.RootIsolation.FTA.Squarefree

set_option genInjectivity false in
/-- A complete numerical isolation retaining exact degree count, ownership and maximality.

The original isolation supplies the support and ordered owners. The owner
selector and maximality certificate refer to those same tracks and polynomial,
with their retained containment and separation conditions. -/
public structure BoxResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The exact degree-sized isolation in the polynomial's original large square. -/ isolation : Exact.Basic.Output p
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree
  /-- Every supported winding track is assigned to an original isolation owner with strict containment evidence. -/
    ownership :
    ∀ (track : Track.Basic.WindingOneTrack p
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)),
      track.initial.box.Refines isolation.support →
        Exact.Ownership.Basic.OwnerSelection isolation track
  /-- Every finite pairwise-separated winding-track family has size at most the polynomial degree. -/ maximality :
    ∀ {familyCount : Nat}
      (family : Fin familyCount → Track.Basic.WindingOneTrack p
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)),
      (∀ left right, left ≠ right →
        (family left).initial.box.Separated
          (family right).initial.box) →
      familyCount ≤ p.natDegree

constructive_injectivity BoxResult

set_option genInjectivity false in
/-- A coupled adapter retaining the exact original numerical isolation result.

The stored box result carries its degree-sized family, owner-selection
procedure and maximality certificate. Degree-indexed track readbacks use that
same original isolation and its retained count equality. -/
public structure AdapterResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original complete numerical isolation and degree-sharp ownership result. -/ boxes : FTA.Squarefree.BoxResult p

constructive_injectivity AdapterResult

namespace AdapterResult

/-- Degree-indexed access to the independently shrinking numerical track. -/
@[expose] public def trackAt {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result
  : FTA.Squarefree.AdapterResult p)
    (index : Fin p.natDegree) :
    Track.Basic.WindingOneTrack p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) :=
  result.boxes.isolation.trackAt index

/-- Distinct degree indices select original tracks with separated initial boxes. -/
public theorem trackAt_pairwiseSeparated
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      FTA.Squarefree.AdapterResult p)
    (left right : Fin p.natDegree) (different : left ≠ right) :
    (result.trackAt left).initial.box.Separated
      (result.trackAt right).initial.box :=
  result.boxes.isolation.trackAt_pairwiseSeparated left right different
end AdapterResult

end Purelib.RootIsolation.FTA.Squarefree
