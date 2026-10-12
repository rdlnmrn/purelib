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

namespace Purelib.Data.Gaussian.Components.Basic
/-- Build the canonical Gaussian rational with the two supplied exact coordinates. -/
def point (x y : Rational) : Canonical := ⟨x, y⟩
end Purelib.Data.Gaussian.Components.Basic

end
