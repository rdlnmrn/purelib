module
import Purelib.Data.Sign.Basic
public import Purelib.Data.Sign.ComplexProduct.Center.Basic
public import Purelib.Data.Sign.Stability

open Purelib.Data.Sign.ComplexProduct.Center.Basic

section
@[expose] public section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

section

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

/-- Certify the two retained factor centers and their computed product center against
both endpoints.

Each of the three center pairs must be nonzero and coordinatewise stable against its
corresponding lower and upper endpoint signs. -/
def AdmissibleSigns
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Data.Sign) : Prop :=
  Data.Sign.EventCenterAdmissible
      centers.factorLeftReal centers.factorLeftImag Aₗ Bₗ Aᵣ Bᵣ ∧
    Data.Sign.EventCenterAdmissible
      centers.factorRightReal centers.factorRightImag Cₗ Dₗ Cᵣ Dᵣ ∧
    Data.Sign.EventCenterAdmissible
      centers.productReal centers.productImag Eₗ Hₗ Eᵣ Hᵣ

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

namespace Purelib.RootIsolation.Cauchy.ProductCells.ProductCenterSigns

/-- Decide simultaneous admissibility of the two factor centers and their computed
product. -/
instance
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Data.Sign) :
    Decidable (centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) := by
  unfold ProductCenterSigns.AdmissibleSigns
  infer_instance

end Purelib.RootIsolation.Cauchy.ProductCells.ProductCenterSigns

end
end

end
