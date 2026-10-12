module
public import Purelib.Data.Nat.List.Maximum
import all Purelib.Data.Nat.List.Maximum

import Purelib.Data.List.Map

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Boundary
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource
public import Purelib.Polynomial.Winding.Edge.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

@[expose] public section

namespace Purelib.Polynomial.Winding.Box.Resource

/-- The displayed polynomial box boundary contains exactly four oriented edges. -/
@[simp] theorem boxBoundary_length (p :
  CoefficientPolynomial) (box : Box) :
    (Dense.Gaussian.Path.Box.Boundary.boxBoundary p box).length = 4 := by
  rfl
end Purelib.Polynomial.Winding.Box.Resource

end

end

section
section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

@[expose] public section

namespace Purelib.Polynomial.Winding.Box.Resource

/-- One winding is four edge indices; each edge constructs one normalized
signed chain and evaluates it at two endpoints. -/
def boxWindingFieldOperationBudget (p :
  CoefficientPolynomial) (box : Box) : Nat :=
  (Dense.Gaussian.Path.Box.Boundary.boxBoundary p box).foldl
    (fun total edge => total +
      Dense.Rational.CauchyIndex.Resource.cauchyIndexFieldOperationBudget
        edge.realPart edge.imagPart) 0
end Purelib.Polynomial.Winding.Box.Resource

end

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Box.Resource

/-- Every original boundary edge has its signed-chain and endpoint resources within the displayed bound. -/
def BoxWindingResourcesWithin (p :
  CoefficientPolynomial)
  (box : Box)
    (bound : Nat) : Prop :=
  ∀ edge ∈ Dense.Gaussian.Path.Box.Boundary.boxBoundary p box,
    Winding.Edge.Resource.EdgeResourcesWithin edge bound
end Purelib.Polynomial.Winding.Box.Resource

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Box.Resource

/-- Compute the maximum retained magnitude budget over the four original boundary edges. -/
def boxWindingMagnitudeBudget (p :
  CoefficientPolynomial)
  (box : Box) : Nat :=
  Data.Nat.List.Maximum.listMaximum ((Dense.Gaussian.Path.Box.Boundary.boxBoundary p box).map
    Winding.Edge.Resource.edgeMagnitudeBudget)
end Purelib.Polynomial.Winding.Box.Resource

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Box.Resource

/-- The computed maximum bounds every boundary edge's retained winding resources.

The result preserves each edge's exact chain membership, endpoint envelopes and headline readback. -/
theorem boxWinding_resource (p :
  CoefficientPolynomial)
  (box : Box) :
    BoxWindingResourcesWithin p box (boxWindingMagnitudeBudget p box) := by
  intro edge member
  have budgetMember : Winding.Edge.Resource.edgeMagnitudeBudget edge ∈
      (Dense.Gaussian.Path.Box.Boundary.boxBoundary p box).map Winding.Edge.Resource.edgeMagnitudeBudget := by
    exact Data.List.Map.mem_map.mpr ⟨edge, member, rfl⟩
  let resource := Winding.Edge.Resource.edge_resource edge
  let bound := boxWindingMagnitudeBudget p box
  have edgeLe : Winding.Edge.Resource.edgeMagnitudeBudget edge ≤ bound :=
    Purelib.Data.Nat.List.Maximum.member_le_listMaximum _ _ budgetMember
  exact
    { chainMember := resource.chainMember
      startEnvelope := resource.startEnvelope.trans edgeLe
      stopEnvelope := resource.stopEnvelope.trans edgeLe
      erasesToHeadline := resource.erasesToHeadline }
end Purelib.Polynomial.Winding.Box.Resource

end
