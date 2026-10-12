module

public import Purelib.Data.Nat.Positive
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Nat.Positive

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Nat.Divisibility.Witness

/-! ## The final finite orbit deduction -/

set_option genInjectivity false in
/-- Retain a natural factor witnessing a multiple of a positive degree.

The liftWinding field is executable natural data, and power_identity certifies
degree.value times that field equals the supplied circuit count. -/
structure ReturnWindingCertificate (degree : RootDegree) (circuits : Nat)
    where
  /-- The retained natural quotient of the winding by the degree. -/ liftWinding : Nat
  /-- Multiplying the retained quotient by the degree recovers the winding. -/ power_identity : degree.value *
    liftWinding = circuits

constructive_injectivity ReturnWindingCertificate

end Purelib.Data.Nat.Divisibility.Witness

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Nat.Divisibility.Witness.ReturnWindingCertificate

open Purelib.Data.Nat.Divisibility.Witness in
/-- The retained multiplication witness proves divisibility by the positive degree. -/
theorem degree_dvd
    {degree : RootDegree} {circuits : Nat}
    (certificate : ReturnWindingCertificate degree circuits) :
    degree.value ∣ circuits := by
  exact ⟨certificate.liftWinding, certificate.power_identity.symm⟩
end Purelib.Data.Nat.Divisibility.Witness.ReturnWindingCertificate

end
