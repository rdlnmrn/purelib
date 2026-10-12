module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.Ring

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding

/-- The eight axial and diagonal Gaussian sectors in counterclockwise order from east.

Sector membership uses the retained half-coordinate boundaries; representatives and deterministic selection are defined
for this same finite nominal carrier. -/
inductive Sector where
  /-- The positive real axial sector. -/ | east /-- The positive real and positive imaginary diagonal sector. -/ |
    northEast /-- The positive imaginary axial sector. -/ | north /-- The negative real and positive imaginary diagonal
    sector. -/ | northWest
  /-- The negative real axial sector. -/ | west /-- The negative real and negative imaginary diagonal sector. -/ |
    southWest /-- The negative imaginary axial sector. -/ | south /-- The positive real and negative imaginary diagonal
    sector. -/ | southEast
deriving DecidableEq

derive_exposed_repr Sector

end Purelib.Data.ComplexContinuedFraction.Encoding
end
end

end

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector

section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
open Purelib.Data in
/-- The exact sector carrier used by the block encoder. -/
abbrev SourceEncodingEncoderSectorAlias :=
  Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data.Gaussian in
/-- Require Gaussian squared norm between one and two, including both endpoints. -/
def Band (z : Basic.Canonical) : Prop := 1 ≤
  Basic.Canonical.normSq z ∧ Basic.Canonical.normSq z ≤ 2
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector
open Purelib.Data.Gaussian in
/-- Require Gaussian squared norm at least one and strictly below two. -/
def Entry (z : Basic.Canonical) : Prop := 1 ≤
  Basic.Canonical.normSq z ∧ Basic.Canonical.normSq z < 2
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Test the retained sector's exact rational coordinate inequalities.

Axial strips exclude their half-coordinate side boundaries, while diagonal sectors include them. These conventions give
a unique sector for every point outside the central square. -/
def Holds :
  Sector → Basic.Canonical → Prop
  | east, z => 1 / 2 ≤ z.re ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | northEast, z => 1 / 2 ≤ z.re ∧ 1 / 2 ≤ z.im
  | north, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 1 / 2 ≤ z.im
  | northWest, z => z.re ≤ -1 / 2 ∧ 1 / 2 ≤ z.im
  | west, z => z.re ≤ -1 / 2 ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | southWest, z => z.re ≤ -1 / 2 ∧ z.im ≤ -1 / 2
  | south, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ z.im ≤ -1 / 2
  | southEast, z => 1 / 2 ≤ z.re ∧ z.im ≤ -1 / 2
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector
open Purelib.Data.Gaussian in
/-- Require Gaussian squared norm strictly above one and at most two. -/
def Loop (z : Basic.Canonical) : Prop := 1 <
  Basic.Canonical.normSq z ∧ Basic.Canonical.normSq z ≤ 2
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Decide the closed squared-norm band inequalities. -/
instance bandDecidable (z : Basic.Canonical) :
  Decidable (Band z) := by
  unfold Band
  infer_instance
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Decide the initial squared-norm band with strict upper endpoint. -/
instance entryDecidable (z : Basic.Canonical)
  : Decidable (Entry z) := by
  unfold Entry
  infer_instance
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Decide sector membership using the retained rational coordinate comparisons. -/
instance holdsDecidable (sector :
  Sector) (z : Basic.Canonical) :
    Decidable (sector.Holds z) := by
  cases sector <;> simp only [Holds] <;> infer_instance
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Decide the loop squared-norm band with strict lower endpoint. -/
instance loopDecidable (z : Basic.Canonical) :
  Decidable (Loop z) := by
  unfold Loop
  infer_instance
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Strict half-coordinate bounds in both directions imply Gaussian squared norm below one. -/
private theorem norm_lt_one_of_central (z :
  Basic.Canonical)
    (xLower : -1 / 2 < z.re) (xUpper : z.re < 1 / 2)
    (yLower : -1 / 2 < z.im) (yUpper : z.im < 1 / 2) :
    Basic.Canonical.normSq z < 1 := by
  have xLeftPositive : 0 < z.re + 1 / 2 := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      xLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < z.re + 1 / 2 := shifted
  have yLeftPositive : 0 < z.im + 1 / 2 := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      yLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < z.im + 1 / 2 := shifted
  have xRightPositive : 0 < 1 / 2 - z.re :=
    Fraction.Order.Arithmetic.sub_pos_direct xUpper
  have yRightPositive : 0 < 1 / 2 - z.im :=
    Fraction.Order.Arithmetic.sub_pos_direct yUpper
  have xSquare : z.re ^ 2 < (1 / 2 : Fraction.Rational) ^ 2 := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (z.re + 1 / 2) * (1 / 2 - z.re) :=
        Fraction.Order.Arithmetic.mul_pos_direct xLeftPositive xRightPositive
      _ = (1 / 2 : Fraction.Rational) ^ 2 - z.re ^ 2 := by ring1
  have ySquare : z.im ^ 2 < (1 / 2 : Fraction.Rational) ^ 2 := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (z.im + 1 / 2) * (1 / 2 - z.im) :=
        Fraction.Order.Arithmetic.mul_pos_direct yLeftPositive yRightPositive
      _ = (1 / 2 : Fraction.Rational) ^ 2 - z.im ^ 2 := by ring1
  calc
    Basic.Canonical.normSq z = z.re ^ 2 + z.im ^ 2 := by
      unfold Basic.Canonical.normSq
      ring1
    _ < (1 / 2 : Fraction.Rational) ^ 2 + (1 / 2 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.add_lt_add_direct xSquare ySquare
    _ = 1 / 2 := by decide
    _ < 1 := by decide
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Read the axial or diagonal Gaussian-integer representative of the retained sector. -/
def rep :
  Sector → Basic.Canonical
  | east => ⟨1, 0⟩
  | northEast => ⟨1, 1⟩
  | north => ⟨0, 1⟩
  | northWest => ⟨-1, 1⟩
  | west => ⟨-1, 0⟩
  | southWest => ⟨-1, -1⟩
  | south => ⟨0, -1⟩
  | southEast => ⟨1, -1⟩
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Select a sector by the retained ordered half-coordinate comparisons.

Test high and low real coordinates first, then imaginary boundaries. The central region defaults to east; the membership
theorem requires squared norm at least one and excludes that default-only region. -/
def select (z : Basic.Canonical) :
  Sector :=
  if 1 / 2 ≤ z.re then
    if 1 / 2 ≤ z.im then northEast
    else if z.im ≤ -1 / 2 then southEast
    else east
  else if z.re ≤ -1 / 2 then
    if 1 / 2 ≤ z.im then northWest
    else if z.im ≤ -1 / 2 then southWest
    else west
  else if 1 / 2 ≤ z.im then north
  else if z.im ≤ -1 / 2 then south
  else east
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A point satisfying a retained sector's inequalities selects that exact sector. -/
theorem select_eq_of_holds {sector :
  Sector} {z : Basic.Canonical}
    (holds : sector.Holds z) : select z = sector := by
  have halfNegLtHalf : (-1 / 2 : Fraction.Rational) < 1 / 2 := by decide
  cases sector with
  | east =>
      rcases holds with ⟨xHigh, yAbove, yBelow⟩
      rw [select, if_pos xHigh, if_neg (not_le_of_gt yBelow),
        if_neg (not_le_of_gt yAbove)]
  | northEast =>
      rcases holds with ⟨xHigh, yHigh⟩
      rw [select, if_pos xHigh, if_pos yHigh]
  | north =>
      rcases holds with ⟨xAbove, xBelow, yHigh⟩
      rw [select, if_neg (not_le_of_gt xBelow),
        if_neg (not_le_of_gt xAbove), if_pos yHigh]
  | northWest =>
      rcases holds with ⟨xLow, yHigh⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      rw [select, if_neg xNotHigh, if_pos xLow, if_pos yHigh]
  | west =>
      rcases holds with ⟨xLow, yAbove, yBelow⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      rw [select, if_neg xNotHigh, if_pos xLow,
        if_neg (not_le_of_gt yBelow), if_neg (not_le_of_gt yAbove)]
  | southWest =>
      rcases holds with ⟨xLow, yLow⟩
      have xNotHigh : ¬1 / 2 ≤ z.re := by
        intro xHigh
        exact (not_le_of_gt halfNegLtHalf) (xHigh.trans xLow)
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_neg xNotHigh, if_pos xLow, if_neg yNotHigh,
        if_pos yLow]
  | south =>
      rcases holds with ⟨xAbove, xBelow, yLow⟩
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_neg (not_le_of_gt xBelow),
        if_neg (not_le_of_gt xAbove), if_neg yNotHigh, if_pos yLow]
  | southEast =>
      rcases holds with ⟨xHigh, yLow⟩
      have yNotHigh : ¬1 / 2 ≤ z.im := by
        intro yHigh
        exact (not_le_of_gt halfNegLtHalf) (yHigh.trans yLow)
      rw [select, if_pos xHigh, if_neg yNotHigh, if_pos yLow]
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Two sectors containing the same Gaussian are equal. -/
theorem holds_unique {left right :
  Sector} {z : Basic.Canonical}
    (leftHolds : left.Holds z) (rightHolds : right.Holds z) :
    left = right :=
  (select_eq_of_holds leftHolds).symm.trans
    (select_eq_of_holds rightHolds)
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Every Gaussian with squared norm at least one belongs to its deterministically selected sector. -/
theorem select_spec (z : Basic.Canonical)
  (normLower : 1 ≤ Basic.Canonical.normSq z) :
    Holds
      (select z) z := by
  unfold select
  by_cases xHigh : 1 / 2 ≤ z.re
  · rw [if_pos xHigh]
    by_cases yHigh : 1 / 2 ≤ z.im
    · rw [if_pos yHigh]
      exact ⟨xHigh, yHigh⟩
    · rw [if_neg yHigh]
      by_cases yLow : z.im ≤ -1 / 2
      · rw [if_pos yLow]
        exact ⟨xHigh, yLow⟩
      · rw [if_neg yLow]
        exact ⟨xHigh, lt_of_not_ge yLow, lt_of_not_ge yHigh⟩
  · rw [if_neg xHigh]
    by_cases xLow : z.re ≤ -1 / 2
    · rw [if_pos xLow]
      by_cases yHigh : 1 / 2 ≤ z.im
      · rw [if_pos yHigh]
        exact ⟨xLow, yHigh⟩
      · rw [if_neg yHigh]
        by_cases yLow : z.im ≤ -1 / 2
        · rw [if_pos yLow]
          exact ⟨xLow, yLow⟩
        · rw [if_neg yLow]
          exact ⟨xLow, lt_of_not_ge yLow, lt_of_not_ge yHigh⟩
    · rw [if_neg xLow]
      by_cases yHigh : 1 / 2 ≤ z.im
      · rw [if_pos yHigh]
        exact ⟨lt_of_not_ge xLow, lt_of_not_ge xHigh, yHigh⟩
      · rw [if_neg yHigh]
        by_cases yLow : z.im ≤ -1 / 2
        · rw [if_pos yLow]
          exact ⟨lt_of_not_ge xLow, lt_of_not_ge xHigh, yLow⟩
        · rw [if_neg yLow]
          have normUpper := norm_lt_one_of_central z
            (lt_of_not_ge xLow) (lt_of_not_ge xHigh)
            (lt_of_not_ge yLow) (lt_of_not_ge yHigh)
          exact ((not_lt_of_ge normLower) normUpper).elim
end Sector
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every retained sector representative has squared norm at least one. -/
theorem rep_norm_lower (sector :
  Sector) :
    (1 : Fraction.Rational) ≤ Basic.Canonical.normSq sector.rep := by
  cases sector <;> decide
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
end
end

end

section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- The initial half-open norm band lies in the closed band. -/
private theorem entry_band {value :
  Basic.SourceEncodingEncoderGaussianAlias} (entry : Entry value)
  :
    Band value := ⟨entry.1, entry.2.le⟩
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

end

section
@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data in
open Purelib.Data.Gaussian in
/-- The loop half-open norm band lies in the closed band. -/
private theorem loop_band {value :
  Basic.SourceEncodingEncoderGaussianAlias} (loop : Loop value) :
    Band value := ⟨loop.1.le, loop.2⟩
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

end
