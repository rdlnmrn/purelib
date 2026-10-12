module

public import Purelib.Data.Sign.Basic

/-!
# Compatibility and conservative choices for formal sums

The zero and equality tests retain every sign restriction forced by addition.
Opposite nonzero signs leave the magnitude-dependent result unrestricted.
-/

namespace Purelib.Data.Sign

-- This declaration group retains the nominal Purelib.Data.Sign.Basic.Sign public API.

/-- Record every sign restriction forced by addition of two formal signs.

A zero summand leaves the other sign unchanged, and two equal nonzero signs force
that same sum sign. Opposite nonzero signs leave the output unrestricted because
their magnitudes are unknown. -/
@[expose] public def SumCompatible (x y z : Sign) : Prop :=
  if x = zero then z = y
  else if y = zero then z = x
  else if x = y then z = x
  else True

/-- Decide formal sum compatibility by the explicit three-sign case conditions. -/
public instance instDecidableSumCompatible (x y z : Sign) : Decidable (Sign.SumCompatible x y z) := by
  unfold Sign.SumCompatible
  infer_instance

/-- Choose the forced sign of a formal sum when the two signs determine it.

Equal signs and sums with zero retain their forced sign. Opposite nonzero signs
return zero because their magnitudes are unspecified. -/
@[expose] public def sumChoice (x y : Sign) : Sign :=
  if x = zero then y
  else if y = zero then x
  else if x = y then x
  else zero

/-- The conservative chosen sum sign satisfies the formal addition restrictions.

Zero summands and equal signs give their forced output. The remaining
opposite nonzero case has no magnitude restriction, so the retained zero
choice satisfies the same compatibility relation. -/
public theorem sumChoice_compatible (x y : Sign) :
    Sign.SumCompatible x y (Sign.sumChoice x y) := by
  cases x <;> cases y <;> decide

end Purelib.Data.Sign
