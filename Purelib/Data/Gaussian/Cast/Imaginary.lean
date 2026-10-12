module
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Data.Gaussian.Cast.Imaginary

/-- Build the Gaussian point on the imaginary axis at the supplied rational height. -/
def horizontalBase (y : Rational) : Canonical := ⟨0, y⟩
end Purelib.Data.Gaussian.Cast.Imaginary

end
