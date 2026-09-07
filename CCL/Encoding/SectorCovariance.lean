import CCL.Encoding.RawParser

/-!
# Constructive covariance of the finite CCL sector table

The first two angular bits encode a Gaussian quarter-turn; the third chooses
the axial or diagonal canonical row.  This module states and checks the exact
predicate covariance used by incremental angular parsing.
-/

namespace CCL.SectorCovariance

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors

/-- Gaussian unit encoded by the first two ordinary octant bits. -/
def quarterUnit : Bool → Bool → Gaussian
  | false, false => ⟨1, 0⟩
  | false, true => ⟨0, 1⟩
  | true, false => ⟨-1, 0⟩
  | true, true => ⟨0, -1⟩

/-- Its explicitly finite inverse table. -/
def inverseQuarterUnit : Bool → Bool → Gaussian
  | false, false => ⟨1, 0⟩
  | false, true => ⟨0, -1⟩
  | true, false => ⟨-1, 0⟩
  | true, true => ⟨0, 1⟩

@[simp] theorem quarterUnit_inv (first second : Bool) :
    (quarterUnit first second)⁻¹ = inverseQuarterUnit first second := by
  cases first <;> cases second <;> decide

/-- The two canonical rows selected by the final angular bit. -/
def canonicalSector : Bool → Sector
  | false => .east
  | true => .northEast

private theorem neg_one_div_two :
    (-1 / 2 : RFAP.ConstructiveFraction.Rational) = -(1 / 2) := by
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv, neg_mul]

private theorem half_le_neg_iff
    (value : RFAP.ConstructiveFraction.Rational) :
    (1 / 2 : RFAP.ConstructiveFraction.Rational) ≤ -value
      ↔ value ≤ -1 / 2 := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_le_neg_direct h
  · intro h
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_le_neg_direct h

private theorem neg_half_lt_neg_iff
    (value : RFAP.ConstructiveFraction.Rational) :
    (-1 / 2 : RFAP.ConstructiveFraction.Rational) < -value
      ↔ value < 1 / 2 := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_lt_neg_direct h
  · intro h
    exact RFAP.ConstructiveFraction.neg_lt_neg_direct h

private theorem neg_lt_half_iff
    (value : RFAP.ConstructiveFraction.Rational) :
    -value < (1 / 2 : RFAP.ConstructiveFraction.Rational)
      ↔ -1 / 2 < value := by
  rw [neg_one_div_two]
  constructor
  · intro h
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_lt_neg_direct h
  · intro h
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_lt_neg_direct h

/-- Unit covariance of all eight rows, including the exact strict and weak
boundary conventions. -/
theorem holds_covariant (first second diagonal : Bool) (value : Gaussian) :
    (CCL.RawParser.sectorOfBits first second diagonal).Holds value
      ↔
    (canonicalSector diagonal).Holds
      ((quarterUnit first second)⁻¹ * value) := by
  rw [quarterUnit_inv]
  cases first <;> cases second <;> cases diagonal <;>
    simp [CCL.RawParser.sectorOfBits, canonicalSector,
      inverseQuarterUnit,
      CCL.Sectors.Sector.Holds,
      half_le_neg_iff, neg_half_lt_neg_iff, neg_lt_half_iff,
      and_comm, and_assoc]

end CCL.SectorCovariance
