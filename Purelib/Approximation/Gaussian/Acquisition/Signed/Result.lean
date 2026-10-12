module
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Result

set_option genInjectivity false in
/-- Mathematical negative and tolerance-relative outcomes remain distinct. This requested-accuracy API has no
fuel-exhaustion constructor. -/
inductive OutcomePayload.{u} (readyType : Type u)
  (negativeType nearType : Type) : Type u
  /-- Retain a successful acquisition result. -/ | ready (result : readyType)
  /-- Retain the displayed certificate of a negative acquisition outcome. -/ | negative (certificate : negativeType)
  /-- Retain the displayed certificate of a tolerance-relative near-boundary outcome. -/ | near (certificate : nearType)

constructive_injectivity OutcomePayload

end Purelib.Approximation.Gaussian.Acquisition.Signed.Result

end
