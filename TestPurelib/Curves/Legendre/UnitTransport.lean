module

import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Actual cofactor advancement and retained endpoint agreement -/

namespace TestPurelib.Curves.Legendre.UnitTransport

open Purelib.Curves.Legendre.Degeneration

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain

/-- Intrinsic whole-patch admission constructs actual reference advancement and independent-reading agreement. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) :
    let advanced := UnitRoot.Transport.fromSource site point inside
    Approximation.Gaussian.Equivalence.NamedEquivalent
      (ownerRootName advanced.parameterNonzero advanced)
      (ownerRootName (Degeneration.UnitRoot.owner site point inside).parameterNonzero
        (Degeneration.UnitRoot.owner site point inside)) :=
  UnitRoot.Transport.fromSource_agrees site point inside

/-- Every radial parameter between the actual endpoints is geometrically admitted and has nonzero original cofactor. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point)
    {time : Data.Rat.Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) :
    (Degeneration.spatialBox site).Contains (UnitRoot.Transport.radialPoint site point time) ∧
      (Degeneration.unitPolynomial site).eval (UnitRoot.Transport.radialPoint site point time) ≠ 0 :=
  ⟨UnitRoot.Transport.radial_inside site point inside timeInside,
    UnitRoot.Transport.radial_nonzero site point inside timeInside⟩

/-- The uniform whole-patch reader retains both its reference box and its common computed clearance. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) :
    (UnitRoot.Transport.reading site point inside).track.initial.box = Degeneration.UnitRoot.box site ∧
      (UnitRoot.Transport.reading site point inside).track.initial.clearance.bound =
        (UnitRoot.Transport.budget site).clearance :=
  ⟨UnitRoot.Transport.reading_box site point inside,
    UnitRoot.Transport.reading_clearance site point inside⟩

/-- Every actual retained accepted chain compares its original terminal owner to the independent endpoint reading. -/
example (site : Fin 2) (first last : Canonical)
    (firstInside : (Degeneration.spatialBox site).Contains first)
    (lastInside : (Degeneration.spatialBox site).Contains last)
    (chain : Chain ⟨(Degeneration.unitPolynomial site).eval first, Degeneration.UnitRoot.owner site first firstInside⟩)
    (endpoint : chain.endpoint.parameter = (Degeneration.unitPolynomial site).eval last) :
    Approximation.Gaussian.Equivalence.NamedEquivalent
      (ownerRootName
        (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter endpoint chain.endpoint.owner).parameterNonzero
        (RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter endpoint chain.endpoint.owner))
      (ownerRootName (Degeneration.UnitRoot.owner site last lastInside).parameterNonzero
        (Degeneration.UnitRoot.owner site last lastInside)) :=
  UnitRoot.Transport.chain_agrees site first last firstInside lastInside chain endpoint

end TestPurelib.Curves.Legendre.UnitTransport
