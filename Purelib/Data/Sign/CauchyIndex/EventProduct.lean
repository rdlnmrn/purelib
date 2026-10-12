module

public import Purelib.Data.Sign.CauchyIndex.Event
public import Purelib.Data.Sign.CauchyIndex.Product
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.Stability
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Int

/-!
# Formal two-sided Cauchy product identities

The two one-sided identities retain the same center signs. Their integer
readings combine into the two endpoint corrections of the retained event.
-/

namespace Purelib.Data.Sign

/-- The two-sided Cauchy product event identity with endpoint corrections.

The product event equals the sum of the two factor events, minus the correction at
the lower endpoint and plus the correction at the upper endpoint. -/
@[expose] public def LocalEventProductIdentity
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign) : Prop :=
  Sign.eventIndex2 Eₑ Hₑ Eₗ Hₗ Eᵣ Hᵣ =
    Sign.eventIndex2 Aₑ Bₑ Aₗ Bₗ Aᵣ Bᵣ +
      Sign.eventIndex2 Cₑ Dₑ Cₗ Dₗ Cᵣ Dᵣ -
      (productCorrection2 Hₗ Bₗ Dₗ : Int) +
      productCorrection2 Hᵣ Bᵣ Dᵣ

/-- Applying the one-sided table to both orientations around the same formal event
cancels the unrepresented center correction. -/
public theorem localProductEventTable
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign)
    (left : Sign.LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (right : Sign.LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    Sign.LocalEventProductIdentity
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have leftIdentity := Sign.localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ left
  have rightIdentity := Sign.localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ right
  unfold Sign.LocalProductIdentity at leftIdentity rightIdentity
  unfold Sign.LocalEventProductIdentity Sign.eventIndex2
  rw [leftIdentity, rightIdentity]
  ring1

/-- Two applications of the generalized one-sided table give the complete event identity
even when one or more endpoint denominator signs are zero. -/
public theorem localProductEventTable_of_endpoint_pairs_nonzero
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : Sign)
    (centerLeft : Aₑ ≠ zero ∨ Bₑ ≠ zero)
    (centerRight : Cₑ ≠ zero ∨ Dₑ ≠ zero)
    (lowerLeft : Aₗ ≠ zero ∨ Bₗ ≠ zero)
    (lowerRight : Cₗ ≠ zero ∨ Dₗ ≠ zero)
    (upperLeft : Aᵣ ≠ zero ∨ Bᵣ ≠ zero)
    (upperRight : Cᵣ ≠ zero ∨ Dᵣ ≠ zero)
    (AStableLower : Sign.Stable Aₑ Aₗ) (BStableLower : Sign.Stable Bₑ Bₗ)
    (CStableLower : Sign.Stable Cₑ Cₗ) (DStableLower : Sign.Stable Dₑ Dₗ)
    (EStableLower : Sign.Stable Eₑ Eₗ) (HStableLower : Sign.Stable Hₑ Hₗ)
    (AStableUpper : Sign.Stable Aₑ Aᵣ) (BStableUpper : Sign.Stable Bₑ Bᵣ)
    (CStableUpper : Sign.Stable Cₑ Cᵣ) (DStableUpper : Sign.Stable Dₑ Dᵣ)
    (EStableUpper : Sign.Stable Eₑ Eᵣ) (HStableUpper : Sign.Stable Hₑ Hᵣ)
    (productCenter : Sign.ComplexProductCompatible Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ)
    (productLower : Sign.ComplexProductCompatible Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (productUpper : Sign.ComplexProductCompatible Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    Sign.LocalEventProductIdentity
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have lower := Sign.localProductTable_of_target_pairs_nonzero
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
    centerLeft centerRight lowerLeft lowerRight
    AStableLower BStableLower CStableLower DStableLower
    EStableLower HStableLower productCenter productLower
  have upper := Sign.localProductTable_of_target_pairs_nonzero
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
    centerLeft centerRight upperLeft upperRight
    AStableUpper BStableUpper CStableUpper DStableUpper
    EStableUpper HStableUpper productCenter productUpper
  unfold Sign.LocalProductIdentity at lower upper
  unfold Sign.LocalEventProductIdentity Sign.eventIndex2
  rw [lower, upper]
  ring1

end Purelib.Data.Sign
