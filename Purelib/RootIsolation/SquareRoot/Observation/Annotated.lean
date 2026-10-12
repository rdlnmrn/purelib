module
import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib

section
@[expose] public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Annotated

/-- Construct the selected square-root numerical channel with its retained isolation provenance.

The finite sheet index selects the occurrence; the annotation preserves the actual isolated channel and its checked
sidecar. -/
def root (parameter :
  Gaussian.Basic.Canonical) (sheet : Fin 2) : Annotated :=
  let isolated := Riemann.RootContinuation.SquareRootSidecar.isolated parameter sheet
  ⟨isolated.1, some (.inr isolated.2)⟩
end Purelib.Approximation.Gaussian.Acquisition.Annotated

end

section
@[expose] public section

/-!
# A finite expression front end for certificate acquisition

Syntactic sharing supplies cancellation and squaring evidence even for opaque
atoms. This is not equality testing for arbitrary processes, nor a reifier
for arbitrary Lean functions. The compiler preserves the numerical channel
exactly; only its optional, proved provenance is inferred.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Annotated

/-- Squaring the annotated selected square root retains the original rational parameter as its certified value. -/
theorem root_square_value (parameter :
  Gaussian.Basic.Canonical) (sheet : Fin 2) :
    (root parameter sheet).square.rationalValue = some parameter :=
  congrArg some (Riemann.RootContinuation.SquareRootSidecar.isolated_parameter parameter sheet)

end Purelib.Approximation.Gaussian.Acquisition.Annotated

end
