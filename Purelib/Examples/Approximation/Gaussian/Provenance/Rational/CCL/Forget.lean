module

public import Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.List.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
# Exact provenance regression clients

The cancellation example has a nonzero possible finite reading at its
initial state. Its symbolic identity to zero nonetheless rules out every
division preparation, demonstrating why candidate equality and operational
identity must not be conflated.
-/

namespace Purelib.Examples.Approximation.Gaussian.Provenance.Rational.CCL.Forget

open Purelib.Examples.Approximation.Gaussian

/-- Forgetting rational provenance preserves the original emitted CCL prefix.

The underlying coherent channel and machine output remain definitionally the same retained data. -/
theorem forgetting_preserves_prefix :
    Provenance.Rational.Cancellation.withSidecar.forget.channel.name.machine.emitted =
      Provenance.Rational.Cancellation.withSidecar.channel.name.machine.emitted := rfl

end Purelib.Examples.Approximation.Gaussian.Provenance.Rational.CCL.Forget

end
