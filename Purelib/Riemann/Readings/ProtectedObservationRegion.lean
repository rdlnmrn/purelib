module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Readings.ContainedObservationPoints
public import Purelib.Riemann.Readings.PreparedObservationSeparation
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# A clear observation region inside the unchanged period ambient

The original branch states are strictly interior to their retained cells.
Their finite lower-coordinate gaps leave a positive strip at the ambient
corner. A cached polynomial neighborhood makes an explicit rectangle in that
strip clear. Every later Newton band inside those states misses it.
-/

namespace Purelib.Riemann.Readings.ProtectedObservationRegion

open Purelib.Data.Rat.Fraction

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Readings.PreparedObservationSeparation
  (minimumRadius minimumRadius_positive minimumRadius_le)
open Purelib.Riemann.Readings.ContainedObservationPoints (BoxObservationPoints)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state state_strict_cell)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A retained clear observation region below the original branch-cell bank.

The record keeps a denominator neighborhood at the original ambient anchor, the finite minimum vertical branch gap, and
a quarter-scale fitting both ambient widths, clearance and that gap. -/
structure ObservationRegion (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The retained denominator-clearance neighborhood for the original curve polynomial. -/ neighborhood :
    ObservationNeighborhood curve.polynomial genus
  /-- The neighborhood center is the exact original ambient anchor. -/ center_eq : neighborhood.center = (Cuts.Ambient
    curve).anchor
  /-- The cached common vertical gap beneath the original branch-state boxes. -/ branchGap : Fraction.Rational
  /-- The gap is the finite minimum of the original state lower sides minus the ambient lower side. -/ branchGap_eq :
    branchGap = minimumRadius branches.siteCount
    (fun index => (BranchCellWinding.state bank index).box.yLower - (Cuts.Ambient curve).yLower)
  /-- The cached positive geometric scale of the protected region. -/ size : Fraction.Rational
  /-- The size is one quarter of the minimum original clearance, widths and branch gap. -/ size_eq : size = min
    neighborhood.radius
    (min (Cuts.Ambient curve).widthX (min (Cuts.Ambient curve).widthY branchGap)) / 4

constructive_injectivity ObservationRegion

namespace ObservationRegion

variable {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial.Clearance.Box in
/-- Cache an anchored clear neighborhood and protected region scale for the original branch bank.

The root-radius boundary clearance certifies the same ambient anchor; the branch gap is computed from the exact retained
winding-state boxes. -/
def build (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) : ObservationRegion bank :=
  let clearance := Boundary.RootRadius.largeSquare_boundaryClearance (BranchIsolation.degreePositive curve)
  let clear := clearance.eval_ne_zero ⟨(Cuts.Ambient curve).contains_anchor, Or.inl rfl⟩
  let neighborhood := ObservationNeighborhood.ofPoint curve.polynomial genus (Cuts.Ambient curve).anchor clear
  let gap := minimumRadius branches.siteCount (fun index => (BranchCellWinding.state bank index).box.yLower -
    (Cuts.Ambient curve).yLower)
  ⟨neighborhood, rfl, gap, rfl,
    min neighborhood.radius (min (Cuts.Ambient curve).widthX (min (Cuts.Ambient curve).widthY gap)) / 4, rfl⟩

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- The original winding-state boxes have a positive common gap above the ambient lower side. -/
theorem branchGap_positive (region : ObservationRegion bank) : 0 < region.branchGap := by
  rw [region.branchGap_eq]
  exact minimumRadius_positive _ (fun index => Fraction.Order.Arithmetic.sub_pos_direct
    ((Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines (BranchCellWinding.state_strict_cell bank
        index) (bank.cell
      index).box_refines).bottom))

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- The retained quarter-scale fitting clearance, ambient widths and branch gap is positive.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem size_positive (region : ObservationRegion bank) : 0 < region.size := by
  rw [region.size_eq]
  have proper := Bounds.RootRadius.Box.largeSquareBox_proper curve.polynomial
  exact Fraction.Order.Field.div_pos_direct
    (Order.Basic.lt_min region.neighborhood.radius_positive (Order.Basic.lt_min
      (Fraction.Order.Arithmetic.sub_pos_direct proper.1)
      (Order.Basic.lt_min (Fraction.Order.Arithmetic.sub_pos_direct proper.2) region.branchGap_positive))) (by decide)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
/-- Four times the retained size is exactly the minimum of its original geometric restrictions. -/
private theorem four_size (region : ObservationRegion bank) : region.size * 4 = min region.neighborhood.radius
    (min (Cuts.Ambient curve).widthX (min (Cuts.Ambient curve).widthY region.branchGap)) := by
  rw [region.size_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

open Purelib.Data.Rat in
/-- Twice a positive size lies strictly below any bound paying four times that size. -/
private theorem twice_lt {size bound : Fraction.Rational} (positive : 0 < size) (paid : size * 4 ≤ bound) : 2 * size <
  bound :=
  (show 2 * size = size * 2 from Fraction.Field.mul_comm _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by
        decide : (2 : Fraction.Rational) < 4)).trans_le paid)

/-- Twice the protected region size fits strictly inside the original clear neighborhood radius.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem twice_size_lt_neighborhood (region : ObservationRegion bank) : 2 * region.size < region.neighborhood.radius :=
  twice_lt region.size_positive (region.four_size.trans_le (Order.Basic.min_le_left _ _))

section
open Purelib.Curves.Hyperelliptic.Branches
/-- Twice the protected region size is strictly smaller than the original ambient horizontal width.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem twice_size_lt_widthX (region : ObservationRegion bank) : 2 * region.size < (Cuts.Ambient curve).widthX :=
  twice_lt region.size_positive (region.four_size.trans_le ((Order.Basic.min_le_right _ _).trans
    (Order.Basic.min_le_left _ _)))

/-- Twice the protected region size is strictly smaller than the original ambient vertical width.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem twice_size_lt_widthY (region : ObservationRegion bank) : 2 * region.size < (Cuts.Ambient curve).widthY :=
  twice_lt region.size_positive (region.four_size.trans_le ((Order.Basic.min_le_right _ _).trans
    ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _))))

end

/-- Twice the protected region size lies strictly below the original minimum branch gap.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem twice_size_lt_branchGap (region : ObservationRegion bank) : 2 * region.size < region.branchGap :=
  twice_lt region.size_positive (region.four_size.trans_le ((Order.Basic.min_le_right _ _).trans
    ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _ _))))

open Purelib.Data.Rat in
/-- Adding twice a positive size gives a strictly larger endpoint than adding that size.

The comparison translates the original positive size and clearance radius
through the displayed rational endpoints. Both endpoints and their retained
geometric bounds remain those of the original region. -/
public theorem lower_lt_upper (lower : Fraction.Rational) {size : Fraction.Rational} (positive : 0 < size) :
    lower + size < lower + 2 * size :=
  ((show lower + size = (lower + size) + 0 from (add_zero _).symm).trans_lt
    (Order.Arithmetic.add_lt_add_left_direct positive (lower + size))).trans_eq (by ring1)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
/-- The original ambient-anchor square between one and two retained sizes in each coordinate. -/
def box (region : ObservationRegion bank) : Box where
  xLower := (Cuts.Ambient curve).xLower + region.size
  xUpper := (Cuts.Ambient curve).xLower + 2 * region.size
  yLower := (Cuts.Ambient curve).yLower + region.size
  yUpper := (Cuts.Ambient curve).yLower + 2 * region.size
  x_valid := (lower_lt_upper _ region.size_positive).le
  y_valid := (lower_lt_upper _ region.size_positive).le

/-- The protected region box has strictly ordered sides. -/
theorem proper (region : ObservationRegion bank) : region.box.Proper :=
  ⟨lower_lt_upper _ region.size_positive, lower_lt_upper _ region.size_positive⟩

section
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Rat
open Purelib.Geometry.Rational
/-- The protected region lies strictly inside the original ambient box.

The comparison translates the original positive size and clearance radius
through the displayed rational endpoints. Both endpoints and their retained
geometric bounds remain those of the original region. -/
theorem interior (region : ObservationRegion bank) : region.box.StrictInterior (Cuts.Ambient curve) := by
  refine ⟨(show (Cuts.Ambient curve).xLower = (Cuts.Ambient curve).xLower + 0 from (add_zero _).symm).trans_lt
    (Order.Arithmetic.add_lt_add_left_direct region.size_positive (Cuts.Ambient curve).xLower), ?_,
    (show (Cuts.Ambient curve).yLower = (Cuts.Ambient curve).yLower + 0 from (add_zero _).symm).trans_lt
    (Order.Arithmetic.add_lt_add_left_direct region.size_positive (Cuts.Ambient curve).yLower), ?_⟩
  · exact (Fraction.Order.Arithmetic.add_lt_add_left_direct region.twice_size_lt_widthX (Cuts.Ambient
      curve).xLower).trans_eq
      (by unfold Box.widthX; ring1)
  · exact (Fraction.Order.Arithmetic.add_lt_add_left_direct region.twice_size_lt_widthY (Cuts.Ambient
      curve).yLower).trans_eq
      (by unfold Box.widthY; ring1)

/-- The protected region refines the exact original centered denominator-clearance neighborhood.

The comparison translates the original positive size and clearance radius
through the displayed rational endpoints. Both endpoints and their retained
geometric bounds remain those of the original region. -/
theorem in_neighborhood (region : ObservationRegion bank) : region.box.Refines
    (Box.Square.Centered.BoxTransport.centeredBox region.neighborhood.center region.neighborhood.radius
      region.neighborhood.radius_positive.le) := by
  rw [region.center_eq]
  change (Cuts.Ambient curve).xLower - region.neighborhood.radius ≤ (Cuts.Ambient curve).xLower + region.size ∧
    (Cuts.Ambient curve).xLower + 2 * region.size ≤ (Cuts.Ambient curve).xLower + region.neighborhood.radius ∧
    (Cuts.Ambient curve).yLower - region.neighborhood.radius ≤ (Cuts.Ambient curve).yLower + region.size ∧
    (Cuts.Ambient curve).yLower + 2 * region.size ≤ (Cuts.Ambient curve).yLower + region.neighborhood.radius
  have lowerFits (lower : Fraction.Rational) : lower - region.neighborhood.radius ≤ lower + region.size := by
    calc
      lower - region.neighborhood.radius ≤ lower - 0 :=
        Order.Arithmetic.sub_le_sub_left_direct region.neighborhood.radius_positive.le lower
      _ = lower + 0 := by ring1
      _ ≤ lower + region.size := Order.Arithmetic.add_le_add_direct le_rfl region.size_positive.le
  exact ⟨lowerFits _,
    (Fraction.Order.Arithmetic.add_lt_add_left_direct region.twice_size_lt_neighborhood (Cuts.Ambient curve).xLower).le,
    lowerFits _,
    (Fraction.Order.Arithmetic.add_lt_add_left_direct region.twice_size_lt_neighborhood (Cuts.Ambient curve).yLower).le⟩

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original curve polynomial is nonzero throughout the retained protected region. -/
theorem clear (region : ObservationRegion bank) (point : Basic.Canonical) (inside : region.box.Contains point) :
    curve.polynomial.eval point ≠ 0 := by
  have bound := region.neighborhood.denominator_lower region.neighborhood.radius_positive.le le_rfl
    (region.in_neighborhood.contains inside)
  have positive := Fraction.Order.Field.div_pos_direct region.neighborhood.denominatorValue_positive
    (by decide : (0 : Fraction.Rational) < 4)
  intro zero
  rw [zero, ← Norm.Basic.normSq_eq_canonical (0 : Basic.Canonical), Norm.Basic.normSq_zero] at bound
  exact (not_lt_of_ge bound) positive

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
/-- The protected region's upper side is below the exact original winding-state box at every branch index. -/
theorem below_state (region : ObservationRegion bank) (index : BranchIsolation.Data.Index branches) :
    region.box.yUpper < (BranchCellWinding.state bank index).box.yLower := by
  have gap : region.branchGap ≤ (BranchCellWinding.state bank index).box.yLower - (Cuts.Ambient curve).yLower := by
    rw [region.branchGap_eq]
    exact minimumRadius_le _ index
  exact (Fraction.Order.Arithmetic.add_lt_add_left_direct (region.twice_size_lt_branchGap.trans_le gap)
    (Cuts.Ambient curve).yLower).trans_eq (by ring1)

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- Every point in the protected region lies outside any refinement of an original branch-state box. -/
theorem outside_refinement (region : ObservationRegion bank) (index : BranchIsolation.Data.Index branches)
    {small : Box} (refines : small.Refines (BranchCellWinding.state bank index).box)
    {point : Basic.Canonical} (inside : region.box.Contains point) : ¬ small.Contains point :=
  fun contained => (not_lt_of_ge (refines.2.2.1.trans contained.2.2.1))
    (inside.2.2.2.trans_lt (region.below_state index))

/-- Construct certified observation points inside the same original protected clear box. -/
def observations (region : ObservationRegion bank) :
    BoxObservationPoints curve.polynomial region.box genus :=
  BoxObservationPoints.build curve.polynomial curve.nonzero region.box region.proper region.clear genus

end ObservationRegion
end Purelib.Riemann.Readings.ProtectedObservationRegion
