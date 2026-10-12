module

public import Init

namespace ModuleVerification

private theorem privateBridge : True = True := propext Iff.rfl

public theorem publicBridge : True = True := privateBridge

-- PROOF_VARIANT
private theorem unusedPrivate : True := by exact True.intro

public def hiddenValue : Nat := 3

public theorem hiddenValue_readback : hiddenValue = 3 := by
  with_unfolding_all rfl

@[expose] public def exposedValue : Nat := 4

end ModuleVerification
