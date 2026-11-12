module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
public import Purelib.Polynomial.Recurrence.Boundary.Constant
import Purelib.Data.Gaussian.Field

/-!
# Constant and positive recurrence ledgers on the same original inventory

The original side constructor determines the branch. Constants retain the
actual empty-column normal form and its complete recurrence cancellation;
positive sources retain the original formal bank, complete mode basis and
geometrically selected boundary. Neither branch receives a supplied rank.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.Multiplicity.Side.Basic (SideResult)
open Purelib.Polynomial.Recurrence.Boundary renaming Constant → ConstantBoundary

namespace Recurrence

/-- The same actual recurrence owner selected by the original constant or positive side.

The constant owner is lifted only to the universe of the positive owner's
retained coefficient constructions. Its original value remains unchanged.
-/
@[expose] def Side {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (rows : Nat) : (side : SideResult source opposite) → (locations : SideLocations clearance side) →
      SideArgument side locations → Type 1
  | .constant _ _ _, _, _ => ULift (ConstantBoundary source rows)
  | .positive _ _, _, argument => Roots.Recurrence argument rows

namespace Side

/-- Construct the actual recurrence branch from the same retained original side and argument data. -/
@[expose] def prepare {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (normalized : source.normalize = source) (rows : Nat) (constantNonzero : 0 < rows → source.eval 0 ≠ 0) :
    (side : SideResult source opposite) → (locations : SideLocations clearance side) →
      (argument : SideArgument side locations) → Side rows side locations argument
  | .constant nonzero degreeZero _, _, _ =>
      let inverse := source.leadingCoeff⁻¹
      ⟨ConstantBoundary.prepare source rows normalized nonzero degreeZero inverse
        (Canonical.mul_inv_cancel _ (DensePolynomial.leadingCoeff_ne_zero nonzero))⟩
  | .positive _ _, _, argument => Roots.Recurrence.prepare argument rows constantNonzero

/-- Read the actual original normal form's signed complementary-target minus kernel dimension. -/
@[expose] def defect {source opposite : CoefficientPolynomial} {clearance : Certificate source} {rows : Nat} :
    {side : SideResult source opposite} → {locations : SideLocations clearance side} →
      {argument : SideArgument side locations} → Side rows side locations argument → Int
  | .constant _ _ _, _, _, retained => retained.down.normal.defect
  | .positive _ _, _, _, retained => Roots.Recurrence.defect retained

/-- The actual branch normal form has rows minus the original independently counted inside multiplicity. -/
theorem defect_eq {source opposite : CoefficientPolynomial} {clearance : Certificate source} {rows : Nat}
    (side : SideResult source opposite) (locations : SideLocations clearance side)
    (argument : SideArgument side locations) (retained : Side rows side locations argument) :
    retained.defect = (rows : Int) - (SideLocations.insideCount side locations : Int) := by
  cases side with
  | constant nonzero degreeZero oppositeNonzero =>
      exact retained.down.defect_eq.trans (by rfl)
  | positive input family => exact Roots.Recurrence.defect_eq retained

end Side
end Recurrence

/-- The actual recurrence ledger of the same retained original inventory and its sufficient argument data. -/
@[expose] def Recurrence {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) (argument : inventory.Argument) (rows : Nat) : Type 1 :=
  Recurrence.Side rows inventory.side inventory.locations argument

namespace Recurrence

variable {source : CoefficientPolynomial} {clearance : Certificate source}
variable {inventory : Inventory clearance} {argument : inventory.Argument} {rows : Nat}

/-- Prepare the actual constant or positive ledger without reconstructing the original inventory. -/
@[expose] def prepare (inventory : Inventory clearance) (argument : inventory.Argument) (rows : Nat)
    (constantNonzero : 0 < rows → source.eval 0 ≠ 0) : Recurrence inventory argument rows :=
  Side.prepare inventory.normalized rows constantNonzero inventory.side inventory.locations argument

/-- Read the actual same-inventory boundary normal form's signed defect. -/
@[expose] def defect (retained : Recurrence inventory argument rows) : Int := Side.defect retained

/-- The actual same-inventory recurrence normal form has the original pole-minus-inside sign. -/
theorem defect_eq (retained : Recurrence inventory argument rows) :
    retained.defect = (rows : Int) - (inventory.insideCount : Int) :=
  Side.defect_eq inventory.side inventory.locations argument retained

end Recurrence
end Purelib.RootIsolation.Multiplicity.Circle

end
