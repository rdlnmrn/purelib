module
import Purelib.Data.Nat.Order

import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Resource
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Edge.Resource

/-- The maximum of the two endpoint magnitude envelopes for an edge. -/
def edgeMagnitudeBudget (edge :
  PolynomialEdge) : Nat :=
  max (Dense.Rational.CauchyIndex.Resource.endpointMagnitudeEnvelope
      edge.realPart edge.imagPart edge.start)
    (Dense.Rational.CauchyIndex.Resource.endpointMagnitudeEnvelope
      edge.realPart edge.imagPart edge.stop)
end Purelib.Polynomial.Winding.Edge.Resource

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Edge.Resource

/-- The signed-remainder chain for the edge's imaginary and real components.

The component order matches the finite Cauchy-index calculation. -/
def normalizedEdgeChain (edge :
  PolynomialEdge) : List (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain
    (id edge.imagPart)
    (id edge.realPart)
end Purelib.Polynomial.Winding.Edge.Resource

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Edge.Resource

/-- Resource bounds and exact winding readback for one retained polynomial edge.

The record binds every chain member to the original component pair and bounds both endpoint envelopes by the supplied
natural ceiling. -/
structure EdgeResourcesWithin (edge :
  PolynomialEdge) (bound : Nat) : Prop where
  /-- Every retained chain polynomial has the component pair's certified resource bound. -/ chainMember : ∀ {candidate :
    Dense.Rational.NormalizedPolynomial},
    candidate ∈ normalizedEdgeChain edge →
    Dense.Rational.SignedRemainder.Resource.ChainMemberResource
      (id edge.imagPart)
      (id edge.realPart) candidate
  /-- The starting-endpoint magnitude envelope lies below the supplied ceiling. -/ startEnvelope :
    Dense.Rational.CauchyIndex.Resource.endpointMagnitudeEnvelope
    edge.realPart edge.imagPart edge.start ≤ bound
  /-- The stopping-endpoint magnitude envelope lies below the supplied ceiling. -/ stopEnvelope :
    Dense.Rational.CauchyIndex.Resource.endpointMagnitudeEnvelope
    edge.realPart edge.imagPart edge.stop ≤ bound
  /-- The finite Cauchy-index readback equals the original edge's doubled winding. -/ erasesToHeadline :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 edge.realPart
      edge.imagPart edge.start edge.stop = edge.doubledWinding
end Purelib.Polynomial.Winding.Edge.Resource

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Winding.Edge.Resource

/-- Certify an edge's resources using its computed endpoint maximum.

The original chain-member resource theorem and the identical retained Cauchy-index inputs supply the guarantees. -/
theorem edge_resource (edge :
  PolynomialEdge) :
    EdgeResourcesWithin edge (edgeMagnitudeBudget edge) := by
  refine
    { chainMember := ?_
      startEnvelope := Purelib.Data.Nat.Order.le_max_left _ _
      stopEnvelope := Purelib.Data.Nat.Order.le_max_right _ _
      erasesToHeadline := rfl }
  · intro candidate member
    exact Dense.Rational.SignedRemainder.Resource.chainMember_resource
      (id edge.imagPart)
      (id edge.realPart)
      candidate member
end Purelib.Polynomial.Winding.Edge.Resource

end
