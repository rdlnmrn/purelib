module

public import Purelib.Curves.Legendre.Polynomial
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Data.Rat.List.Minimum
import Purelib.Polynomial.Clearance.Box.Line.Translated
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # Paid Legendre variation of the original clear-grid axes

The original line certificates exclude the exact three branch coordinates
on the original coefficient square. One retained finite minimum pays the
moving branch against every original axis. The same coordinates then carry
new factored clearances on an independently supplied target ambient box.
Support in that actual box is checked separately; failure of this local
support test says nothing about a global cycle deformation.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Grid

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Clearance.Box

/-- The original coefficient-computed ambient square for this exact Legendre cubic. -/
abbrev Ambient (parameter : Canonical) : Box := RootRadius.Box.largeSquareBox (Paths.polynomial parameter)

/-- Every exact root of the cubic belongs to its original coefficient square. -/
private theorem root_inside (parameter root : Canonical)
    (vanishes : (Paths.polynomial parameter).eval root = 0) : (Ambient parameter).Contains root := by
  by_cases inside : (Ambient parameter).Contains root
  · exact inside
  · have lower := RootIsolation.Residual.Global.Bounds.outsideResidualThreshold_le
      (p := Paths.polynomial parameter) (by change 2 ≤ 3; decide +kernel) root inside
    have positive := RootIsolation.Residual.Global.Bounds.outsideResidualThreshold_pos
      (p := Paths.polynomial parameter) (by change 0 < 3; decide +kernel)
    have zero := (congrArg Norm.Basic.normSq vanishes).trans Norm.Basic.normSq_zero
    exact (not_lt_of_ge (Order.Basic.le_refl 0) (positive.trans_le (lower.trans_eq zero))).elim

/-- An original vertical-line certificate excludes the real coordinate of each actual enclosed root. -/
private theorem vertical_apart {parameter root : Canonical}
    (line : VerticalLine (Paths.polynomial parameter) (Ambient parameter))
    (vanishes : (Paths.polynomial parameter).eval root = 0) : line.coordinate ≠ root.re := by
  intro equal
  have inside := root_inside parameter root vanishes
  have located : point line.coordinate root.im = root := Data.Gaussian.Basic.ext equal rfl
  have lower := line.clearance.lower root.im inside.2.2.1 inside.2.2.2
  have zero := (congrArg Canonical.normSq
    ((congrArg (Paths.polynomial parameter).eval located).trans vanishes)).trans Canonical.normSq_zero
  exact not_lt_of_ge (Order.Basic.le_refl 0) (line.clearance.positive.trans_le (lower.trans_eq zero))

/-- An original horizontal-line certificate excludes the imaginary coordinate of each actual enclosed root. -/
private theorem horizontal_apart {parameter root : Canonical}
    (line : HorizontalLine (Paths.polynomial parameter) (Ambient parameter))
    (vanishes : (Paths.polynomial parameter).eval root = 0) : line.coordinate ≠ root.im := by
  intro equal
  have inside := root_inside parameter root vanishes
  have located : point root.re line.coordinate = root := Data.Gaussian.Basic.ext rfl equal
  have lower := line.clearance.lower root.re inside.1 inside.2.1
  have zero := (congrArg Canonical.normSq
    ((congrArg (Paths.polynomial parameter).eval located).trans vanishes)).trans Canonical.normSq_zero
  exact not_lt_of_ge (Order.Basic.le_refl 0) (line.clearance.positive.trans_le (lower.trans_eq zero))

/-- The ordered squared moving-branch gaps read the same actual vertical and horizontal line occurrences. -/
def gaps {parameter : Canonical} (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    List Rational :=
  original.vertical.map (fun line => (line.coordinate - parameter.re) ^ 2) ++
    original.horizontal.map (fun line => (line.coordinate - parameter.im) ^ 2)

/-- Each original line's moving-branch gap is strictly positive. -/
private theorem gaps_positive {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    ∀ value ∈ gaps original, 0 < value := by
  intro value member
  rcases Data.List.Membership.mem_append.mp member with vertical | horizontal
  · rcases Map.mem_map.mp vertical with ⟨line, _, equal⟩
    have apart := vertical_apart line (Paths.polynomial_lambda parameter)
    have nonzero : line.coordinate - parameter.re ≠ 0 := by
      intro zero
      apply apart
      exact (show line.coordinate = (line.coordinate - parameter.re) + parameter.re by ring1).trans
        ((congrArg (fun value : Rational => value + parameter.re) zero).trans (Field.zero_add _))
    exact equal ▸ Order.Arithmetic.exact_rational_sq_pos nonzero
  · rcases Map.mem_map.mp horizontal with ⟨line, _, equal⟩
    have apart := horizontal_apart line (Paths.polynomial_lambda parameter)
    have nonzero : line.coordinate - parameter.im ≠ 0 := by
      intro zero
      apply apart
      exact (show line.coordinate = (line.coordinate - parameter.im) + parameter.im by ring1).trans
        ((congrArg (fun value : Rational => value + parameter.im) zero).trans (Field.zero_add _))
    exact equal ▸ Order.Arithmetic.exact_rational_sq_pos nonzero

/-- The original ordered moving-branch gaps have a positive finite minimum. -/
private theorem packaged_minimum_positive {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    0 < Data.Rat.List.Minimum.positiveMinimum (gaps original) :=
  Data.Rat.List.Minimum.positiveMinimum_pos (gaps original) (gaps_positive original)

/-- The original ordered moving-branch gaps have a positive finite minimum. -/
theorem minimum_positive {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    0 < Data.Rat.List.Minimum.positiveMinimum (gaps original) := packaged_minimum_positive original

/-- Retain one actual gap list, its original positive minimum and the corresponding quarter request.

The original grid remains the index. These are scalar caches only; no
Point, root isolation, source preparation or original line acquisition is
replayed. The whole factory predicates retain the exact ordered inputs.
-/
@[expose] def Range {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) : Type :=
  (values : { values : List Rational // values = gaps original }) ×
  (floor : { value : Rational // value = Data.Rat.List.Minimum.positiveMinimum values.val ∧ 0 < value }) ×
  { request : AccuracyRequest // request.tolerance = floor.val / 4 }

namespace Range

/-- Cache the original ordered gaps, one positive finite minimum and one actual quarter request. -/
def build {parameter : Canonical} (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    Range original :=
  let values := gaps original
  let floor := Data.Rat.List.Minimum.positiveMinimum values
  have positive := minimum_positive original
  let request : AccuracyRequest := ⟨floor / 4, Data.Rat.Bounds.Quarter.quarter_pos positive⟩
  ⟨⟨values, rfl⟩, ⟨floor, rfl, positive⟩, ⟨request, rfl⟩⟩

/-- Read the same cached finite minimum without another fold over the original lines. -/
def floor {parameter : Canonical} {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)}
    (retained : Range original) : Rational := retained.2.1.val

/-- The cached common line gap is strictly positive, including an empty original axis bank. -/
private theorem packaged_floor_positive {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original) :
    0 < retained.floor := retained.2.1.property.2

/-- The cached common line gap is strictly positive, including an empty original axis bank. -/
theorem floor_positive {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original) :
    0 < retained.floor := packaged_floor_positive retained

/-- Read the same original finite quarter request, keeping its actual tolerance and positivity. -/
def request {parameter : Canonical} {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)}
    (retained : Range original) : AccuracyRequest := retained.2.2.val

/-- The request pays one quarter of the retained actual common squared gap. -/
private theorem packaged_request_tolerance {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original) :
    retained.request.tolerance = retained.floor / 4 := retained.2.2.property

/-- The request pays one quarter of the retained actual common squared gap. -/
theorem request_tolerance {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original) :
    retained.request.tolerance = retained.floor / 4 := packaged_request_tolerance retained

/-- The retained common gap is bounded by this exact original vertical occurrence. -/
private theorem packaged_floor_le_vertical {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : VerticalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.vertical) :
    retained.floor ≤ (line.coordinate - parameter.re) ^ 2 := by
  have present : (line.coordinate - parameter.re) ^ 2 ∈ gaps original :=
    Membership.mem_append.mpr (Or.inl
    (Map.mem_map_of_mem (f := fun line => (line.coordinate - parameter.re) ^ 2) member))
  have originalBound := Data.Rat.List.Minimum.positiveMinimum_le_of_mem present
  have same := retained.2.1.property.1.trans
    (congrArg Data.Rat.List.Minimum.positiveMinimum retained.1.property)
  exact same.trans_le originalBound

/-- The retained common gap is bounded by this exact original vertical occurrence. -/
theorem floor_le_vertical {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : VerticalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.vertical) :
    retained.floor ≤ (line.coordinate - parameter.re) ^ 2 := packaged_floor_le_vertical retained line member

/-- The retained common gap is bounded by this exact original horizontal occurrence. -/
private theorem packaged_floor_le_horizontal {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : HorizontalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.horizontal) :
    retained.floor ≤ (line.coordinate - parameter.im) ^ 2 := by
  have present : (line.coordinate - parameter.im) ^ 2 ∈ gaps original :=
    Membership.mem_append.mpr (Or.inr
    (Map.mem_map_of_mem (f := fun line => (line.coordinate - parameter.im) ^ 2) member))
  have originalBound := Data.Rat.List.Minimum.positiveMinimum_le_of_mem present
  have same := retained.2.1.property.1.trans
    (congrArg Data.Rat.List.Minimum.positiveMinimum retained.1.property)
  exact same.trans_le originalBound

/-- The retained common gap is bounded by this exact original horizontal occurrence. -/
theorem floor_le_horizontal {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : HorizontalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.horizontal) :
    retained.floor ≤ (line.coordinate - parameter.im) ^ 2 := packaged_floor_le_horizontal retained line member

/-- The same original request pays every unit-interval interpolated increment. -/
private theorem packaged_interpolated_admitted {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ retained.request.tolerance := by
  have scalar := (Norm.Basic.normSq_eq_canonical (⟨time, 0⟩ : Canonical)).trans_le
    (RationalEmbedding.Bounds.unit_parameter inside.1 inside.2)
  have multiplied := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalar
    (Norm.Basic.normSq_nonneg increment)
  exact (Norm.Basic.normSq_mul _ _).trans_le
    ((multiplied.trans_eq (Field.one_mul _)).trans paid)

/-- The same original request pays every unit-interval interpolated increment. -/
theorem interpolated_admitted {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    Norm.Basic.normSq ((⟨time, 0⟩ : Canonical) * increment) ≤ retained.request.tolerance :=
  packaged_interpolated_admitted retained time inside paid

/-- A quarter-paid increment cannot move the parameter root onto the same original vertical line. -/
private theorem vertical_shift_apart {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : VerticalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.vertical)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    line.coordinate ≠ (parameter + increment).re := by
  intro equal
  have difference : line.coordinate - parameter.re = increment.re := by
    change line.coordinate = parameter.re + increment.re at equal
    exact (congrArg (fun value : Rational => value - parameter.re) equal).trans (by ring1)
  have coordinate : increment.re ^ 2 ≤ Norm.Basic.normSq increment := by
    change increment.re ^ 2 ≤ increment.re ^ 2 + increment.im ^ 2
    exact (show increment.re ^ 2 = increment.re ^ 2 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
        (Order.Arithmetic.sq_nonneg_direct _))
  have lower := (retained.floor_le_vertical line member).trans
    ((congrArg (fun value : Rational => value ^ 2) difference).trans_le coordinate)
  have upper := paid.trans_eq retained.request_tolerance
  have small := Data.Rat.Bounds.Quarter.quarter_lt_self retained.floor_positive
  exact not_lt_of_ge (Order.Basic.le_refl retained.floor) ((lower.trans upper).trans_lt small)

/-- A quarter-paid increment cannot move the parameter root onto the same original horizontal line. -/
private theorem horizontal_shift_apart {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : HorizontalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.horizontal)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    line.coordinate ≠ (parameter + increment).im := by
  intro equal
  have difference : line.coordinate - parameter.im = increment.im := by
    change line.coordinate = parameter.im + increment.im at equal
    exact (congrArg (fun value : Rational => value - parameter.im) equal).trans (by ring1)
  have coordinate : increment.im ^ 2 ≤ Norm.Basic.normSq increment := by
    change increment.im ^ 2 ≤ increment.re ^ 2 + increment.im ^ 2
    exact (show increment.im ^ 2 = 0 + increment.im ^ 2 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (Order.Arithmetic.sq_nonneg_direct _)
        (Order.Basic.le_refl _))
  have lower := (retained.floor_le_horizontal line member).trans
    ((congrArg (fun value : Rational => value ^ 2) difference).trans_le coordinate)
  have upper := paid.trans_eq retained.request_tolerance
  have small := Data.Rat.Bounds.Quarter.quarter_lt_self retained.floor_positive
  exact not_lt_of_ge (Order.Basic.le_refl retained.floor) ((lower.trans upper).trans_lt small)

/-- Re-clear the same old vertical coordinate under the changed cubic on the supplied actual target box. -/
def verticalClearance {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : VerticalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.vertical)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box) :
    Line.Basic.VerticalLineClearance
      (Paths.polynomial (parameter + increment)) target line.coordinate :=
  let zero := Line.Translated.translatedCoordinate_verticalLineClearance 0 target line.coordinate
    (vertical_apart line (Paths.polynomial_zero parameter))
  let moving := Line.Translated.translatedCoordinate_verticalLineClearance
    (parameter + increment) target line.coordinate
    (retained.vertical_shift_apart line member paid)
  let one := Line.Translated.translatedCoordinate_verticalLineClearance 1 target line.coordinate
    (vertical_apart line (Paths.polynomial_one parameter))
  Eq.mp (congrArg (fun polynomial => Line.Basic.VerticalLineClearance
      polynomial target line.coordinate)
      (polynomial_eq_factorsAt (parameter + increment)).symm)
    ((zero.mul moving).mul one)

/-- Re-clear the same old horizontal coordinate under the changed cubic on the supplied actual target box. -/
def horizontalClearance {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (line : HorizontalLine (Paths.polynomial parameter) (Ambient parameter)) (member : line ∈ original.horizontal)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box) :
    Line.Basic.HorizontalLineClearance
      (Paths.polynomial (parameter + increment)) target line.coordinate :=
  let zero := Line.Translated.translatedCoordinate_horizontalLineClearance 0 target line.coordinate
    (horizontal_apart line (Paths.polynomial_zero parameter))
  let moving := Line.Translated.translatedCoordinate_horizontalLineClearance
    (parameter + increment) target line.coordinate
    (retained.horizontal_shift_apart line member paid)
  let one := Line.Translated.translatedCoordinate_horizontalLineClearance 1 target line.coordinate
    (horizontal_apart line (Paths.polynomial_one parameter))
  Eq.mp (congrArg (fun polynomial => Line.Basic.HorizontalLineClearance
      polynomial target line.coordinate)
      (polynomial_eq_factorsAt (parameter + increment)).symm)
    ((zero.mul moving).mul one)

/-- The whole scalar range factory retains its original gap table, one minimum and quarter request. -/
private theorem packaged_build_factory {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    build original =
      let values := gaps original
      let floor := Data.Rat.List.Minimum.positiveMinimum values
      have positive := minimum_positive original
      let request : AccuracyRequest := ⟨floor / 4, Data.Rat.Bounds.Quarter.quarter_pos positive⟩
      ⟨⟨values, rfl⟩, ⟨floor, rfl, positive⟩, ⟨request, rfl⟩⟩ := by rfl

/-- The whole scalar range factory retains its original gap table, one minimum and quarter request. -/
theorem build_factory {parameter : Canonical}
    (original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)) :
    build original =
      let values := gaps original
      let floor := Data.Rat.List.Minimum.positiveMinimum values
      have positive := minimum_positive original
      let request : AccuracyRequest := ⟨floor / 4, Data.Rat.Bounds.Quarter.quarter_pos positive⟩
      ⟨⟨values, rfl⟩, ⟨floor, rfl, positive⟩, ⟨request, rfl⟩⟩ := packaged_build_factory original

/-- Retain both changed-polynomial line lists on the supplied actual target box.

Only original line occurrences are visited. Each output keeps that same
coordinate and constructs its three factor clearances once. The two whole
list factory laws preserve the original order and repeated occurrences.
-/
@[expose] def Lines {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box)
    (support : (Ambient parameter).Refines target) : Type :=
  (_vertical : { values : List (VerticalLine (Paths.polynomial (parameter + increment)) target) //
    values = original.vertical.attach.map (fun line =>
      ⟨line.val.coordinate, ⟨support.1.trans line.val.inside.1, line.val.inside.2.trans support.2.1⟩,
        retained.verticalClearance line.val line.property paid target⟩) }) ×
  { values : List (HorizontalLine (Paths.polynomial (parameter + increment)) target) //
    values = original.horizontal.attach.map (fun line =>
      ⟨line.val.coordinate, ⟨support.2.2.1.trans line.val.inside.1, line.val.inside.2.trans support.2.2.2⟩,
        retained.horizontalClearance line.val line.property paid target⟩) }

namespace Lines

/-- Construct the two actual new line banks once, consuming the same retained range and support certificate. -/
def build {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box)
    (support : (Ambient parameter).Refines target) : Lines retained paid target support :=
  let vertical : List (VerticalLine (Paths.polynomial (parameter + increment)) target) :=
    original.vertical.attach.map (fun line =>
      ⟨line.val.coordinate, ⟨support.1.trans line.val.inside.1, line.val.inside.2.trans support.2.1⟩,
        retained.verticalClearance line.val line.property paid target⟩)
  let horizontal : List (HorizontalLine (Paths.polynomial (parameter + increment)) target) :=
    original.horizontal.attach.map (fun line =>
      ⟨line.val.coordinate, ⟨support.2.2.1.trans line.val.inside.1, line.val.inside.2.trans support.2.2.2⟩,
        retained.horizontalClearance line.val line.property paid target⟩)
  ⟨⟨vertical, rfl⟩, ⟨horizontal, rfl⟩⟩

/-- The complete two-list factory retains each old occurrence and both actual new factor-clearance lists. -/
private theorem packaged_build_factory
    {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box)
    (support : (Ambient parameter).Refines target) :
    build retained paid target support =
      let vertical : List (VerticalLine (Paths.polynomial (parameter + increment)) target) :=
        original.vertical.attach.map (fun line =>
          ⟨line.val.coordinate, ⟨support.1.trans line.val.inside.1, line.val.inside.2.trans support.2.1⟩,
            retained.verticalClearance line.val line.property paid target⟩)
      let horizontal : List (HorizontalLine (Paths.polynomial (parameter + increment)) target) :=
        original.horizontal.attach.map (fun line =>
          ⟨line.val.coordinate, ⟨support.2.2.1.trans line.val.inside.1, line.val.inside.2.trans support.2.2.2⟩,
            retained.horizontalClearance line.val line.property paid target⟩)
      ⟨⟨vertical, rfl⟩, ⟨horizontal, rfl⟩⟩ := by rfl

/-- The complete two-list factory retains each old occurrence and both actual new factor-clearance lists. -/
theorem build_factory
    {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance) (target : Box)
    (support : (Ambient parameter).Refines target) :
    build retained paid target support =
      let vertical : List (VerticalLine (Paths.polynomial (parameter + increment)) target) :=
        original.vertical.attach.map (fun line =>
          ⟨line.val.coordinate, ⟨support.1.trans line.val.inside.1, line.val.inside.2.trans support.2.1⟩,
            retained.verticalClearance line.val line.property paid target⟩)
      let horizontal : List (HorizontalLine (Paths.polynomial (parameter + increment)) target) :=
        original.horizontal.attach.map (fun line =>
          ⟨line.val.coordinate, ⟨support.2.2.1.trans line.val.inside.1, line.val.inside.2.trans support.2.2.2⟩,
            retained.horizontalClearance line.val line.property paid target⟩)
      ⟨⟨vertical, rfl⟩, ⟨horizontal, rfl⟩⟩ := packaged_build_factory retained paid target support

/-- Read the same retained changed-polynomial vertical lines without replaying their factor factories. -/
def vertical {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) := lines.1.val

/-- Read the same retained changed-polynomial horizontal lines without replaying their factor factories. -/
def horizontal {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) := lines.2.val

/-- All original vertical coordinates remain in their original order in the new line bank. -/
private theorem packaged_vertical_coordinates {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) :
    lines.vertical.map VerticalLine.coordinate = original.vertical.map VerticalLine.coordinate := by
  have factory := congrArg (List.map VerticalLine.coordinate) lines.1.property
  have attached := congrArg (List.map VerticalLine.coordinate) (attach_map_subtype_val original.vertical)
  apply factory.trans
  calc
    _ = (original.vertical.attach.map Subtype.val).map VerticalLine.coordinate := by
      refine (Map.map_map _ _ _).trans ?_
      refine (Map.map_congr_left ?_).trans (Map.map_map _ _ _).symm
      intro line _member
      rfl
    _ = _ := attached

/-- All original vertical coordinates remain in their original order in the new line bank. -/
theorem vertical_coordinates {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) :
    lines.vertical.map VerticalLine.coordinate = original.vertical.map VerticalLine.coordinate :=
  packaged_vertical_coordinates lines

/-- All original horizontal coordinates remain in their original order in the new line bank. -/
private theorem packaged_horizontal_coordinates {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) :
    lines.horizontal.map HorizontalLine.coordinate = original.horizontal.map HorizontalLine.coordinate := by
  have factory := congrArg (List.map HorizontalLine.coordinate) lines.2.property
  have attached := congrArg (List.map HorizontalLine.coordinate) (attach_map_subtype_val original.horizontal)
  apply factory.trans
  calc
    _ = (original.horizontal.attach.map Subtype.val).map HorizontalLine.coordinate := by
      refine (Map.map_map _ _ _).trans ?_
      refine (Map.map_congr_left ?_).trans (Map.map_map _ _ _).symm
      intro line _member
      rfl
    _ = _ := attached

/-- All original horizontal coordinates remain in their original order in the new line bank. -/
theorem horizontal_coordinates {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support) :
    lines.horizontal.map HorizontalLine.coordinate = original.horizontal.map HorizontalLine.coordinate :=
  packaged_horizontal_coordinates lines

/-- Extend the actual target grid using only the two supplied retained new line banks. -/
def extend {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) :
    ClearGrid (Paths.polynomial (parameter + increment)) target :=
  Extension.extend current lines.vertical lines.horizontal

/-- The extended grid retains all coordinates of the original actual target grid. -/
private theorem packaged_extend_inclusion {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) :
    Extension.CoordinateInclusion current (lines.extend current) :=
  Extension.extend_inclusion current lines.vertical lines.horizontal

/-- The extended grid retains all coordinates of the original actual target grid. -/
theorem extend_inclusion {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) :
    Extension.CoordinateInclusion current (lines.extend current) := packaged_extend_inclusion lines current

/-- Each original source vertical coordinate belongs to this same extended target grid. -/
private theorem packaged_extend_vertical {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) {coordinate : Rational}
    (member : coordinate ∈ original.vertical.map VerticalLine.coordinate) :
    coordinate ∈ (lines.extend current).vertical.map VerticalLine.coordinate :=
  Extension.extend_vertical current lines.vertical lines.horizontal
    (Eq.mpr (congrArg (fun values : List Rational => coordinate ∈ values) lines.vertical_coordinates) member)

/-- Each original source vertical coordinate belongs to this same extended target grid. -/
theorem extend_vertical {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) {coordinate : Rational}
    (member : coordinate ∈ original.vertical.map VerticalLine.coordinate) :
    coordinate ∈ (lines.extend current).vertical.map VerticalLine.coordinate :=
  packaged_extend_vertical lines current member

/-- Each original source horizontal coordinate belongs to this same extended target grid. -/
private theorem packaged_extend_horizontal {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) {coordinate : Rational}
    (member : coordinate ∈ original.horizontal.map HorizontalLine.coordinate) :
    coordinate ∈ (lines.extend current).horizontal.map HorizontalLine.coordinate :=
  Extension.extend_horizontal current lines.vertical lines.horizontal
    (Eq.mpr (congrArg (fun values : List Rational => coordinate ∈ values) lines.horizontal_coordinates) member)

/-- Each original source horizontal coordinate belongs to this same extended target grid. -/
theorem extend_horizontal {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    (current : ClearGrid (Paths.polynomial (parameter + increment)) target) {coordinate : Rational}
    (member : coordinate ∈ original.horizontal.map HorizontalLine.coordinate) :
    coordinate ∈ (lines.extend current).horizontal.map HorizontalLine.coordinate :=
  packaged_extend_horizontal lines current member

/-- Extend an existing framed target cache while retaining both of its original coordinate inclusions and states.

Only the existing extension operation constructs a new sorted grid. The
original state list, source target-grid owner and supplied frame are kept;
no branch isolation, root acquisition or state search is replayed.
-/
def framed {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    {current : ClearGrid (Paths.polynomial (parameter + increment)) target}
    {states : List (FromStates.BranchState (Paths.polynomial (parameter + increment)) target)}
    (reference : FramedClearGrid.FramedExtension current states) : FramedClearGrid.FramedExtension current states :=
  let grid := lines.extend reference.grid
  let included := lines.extend_inclusion reference.grid
  ⟨grid, reference.originalIncluded.trans included, reference.statesIncluded.trans included,
    ⟨included.vertical _ reference.frame.xLower, included.vertical _ reference.frame.xUpper,
      included.horizontal _ reference.frame.yLower, included.horizontal _ reference.frame.yUpper⟩⟩

/-- The whole framed extension retains the two line lists and all original state and frame certificates. -/
private theorem packaged_framed_factory
    {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    {current : ClearGrid (Paths.polynomial (parameter + increment)) target}
    {states : List (FromStates.BranchState (Paths.polynomial (parameter + increment)) target)}
    (reference : FramedClearGrid.FramedExtension current states) :
    lines.framed reference =
      let grid := lines.extend reference.grid
      let included := lines.extend_inclusion reference.grid
      ⟨grid, reference.originalIncluded.trans included, reference.statesIncluded.trans included,
        ⟨included.vertical _ reference.frame.xLower, included.vertical _ reference.frame.xUpper,
          included.horizontal _ reference.frame.yLower, included.horizontal _ reference.frame.yUpper⟩⟩ := by rfl

/-- The whole framed extension retains the two line lists and all original state and frame certificates. -/
theorem framed_factory
    {parameter increment : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} {retained : Range original}
    {paid : Norm.Basic.normSq increment ≤ retained.request.tolerance} {target : Box}
    {support : (Ambient parameter).Refines target} (lines : Lines retained paid target support)
    {current : ClearGrid (Paths.polynomial (parameter + increment)) target}
    {states : List (FromStates.BranchState (Paths.polynomial (parameter + increment)) target)}
    (reference : FramedClearGrid.FramedExtension current states) :
    lines.framed reference =
      let grid := lines.extend reference.grid
      let included := lines.extend_inclusion reference.grid
      ⟨grid, reference.originalIncluded.trans included, reference.statesIncluded.trans included,
        ⟨included.vertical _ reference.frame.xLower, included.vertical _ reference.frame.xUpper,
          included.horizontal _ reference.frame.yLower, included.horizontal _ reference.frame.yUpper⟩⟩ :=
  packaged_framed_factory lines reference

end Lines

/-- One actual paid/support-certified line extension, or the original failed local payment or box-support condition.

Both failures retain the original request, increment and ambient owners as
indices. They disprove only the displayed sufficient finite check. No
period equality, sheet relation or global obstruction is part of the type.
-/
@[expose] def Attempt {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target) :
    Type :=
  ((paid : { _unit : Unit // Norm.Basic.normSq increment ≤ retained.request.tolerance }) ×
    (support : { _unit : Unit // (Ambient parameter).Refines target }) ×
    (lines : Lines retained paid.property target support.property) ×
    { grid : ClearGrid (Paths.polynomial (parameter + increment)) target // grid = lines.extend current }) ⊕
  ({ _unit : Unit // ¬Norm.Basic.normSq increment ≤ retained.request.tolerance } ⊕
    { _unit : Unit // ¬(Ambient parameter).Refines target })

/-- Check the actual two scalar/support conditions before constructing either new line list and one grid extension. -/
def attempt {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target) :
    Attempt retained increment current := by
  letI : Decidable ((Ambient parameter).Refines target) := by unfold Box.Refines; infer_instance
  if paid : Norm.Basic.normSq increment ≤ retained.request.tolerance then
    if support : (Ambient parameter).Refines target then
      let lines := Lines.build retained paid target support
      let grid := lines.extend current
      exact .inl ⟨⟨(), paid⟩, ⟨(), support⟩, lines, ⟨grid, rfl⟩⟩
    else
      exact .inr (.inr ⟨(), support⟩)
  else
    exact .inr (.inl ⟨(), paid⟩)

/-- The successful finite branch builds the two line lists and the target grid extension exactly once. -/
private theorem packaged_attempt_paid
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance)
    (support : (Ambient parameter).Refines target) :
    attempt retained increment current =
      .inl (let lines := Lines.build retained paid target support
        let grid := lines.extend current
        ⟨⟨(), paid⟩, ⟨(), support⟩, lines, ⟨grid, rfl⟩⟩) := by
  unfold attempt
  rewrite [dif_pos paid, dif_pos support]
  rfl

/-- The successful finite branch builds the two line lists and the target grid extension exactly once. -/
theorem attempt_paid
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance)
    (support : (Ambient parameter).Refines target) :
    attempt retained increment current =
      .inl (let lines := Lines.build retained paid target support
        let grid := lines.extend current
        ⟨⟨(), paid⟩, ⟨(), support⟩, lines, ⟨grid, rfl⟩⟩) :=
  packaged_attempt_paid retained increment current paid support

/-- An unpaid actual increment returns that original failed scalar comparison before any new line construction. -/
private theorem packaged_attempt_unpaid
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (unpaid : ¬Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    attempt retained increment current = .inr (.inl ⟨(), unpaid⟩) := by
  unfold attempt
  rewrite [dif_neg unpaid]
  rfl

/-- An unpaid actual increment returns that original failed scalar comparison before any new line construction. -/
theorem attempt_unpaid
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (unpaid : ¬Norm.Basic.normSq increment ≤ retained.request.tolerance) :
    attempt retained increment current = .inr (.inl ⟨(), unpaid⟩) :=
  packaged_attempt_unpaid retained increment current unpaid

/-- An unsupported actual target box returns that failed local support condition before new line construction. -/
private theorem packaged_attempt_unsupported
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance)
    (unsupported : ¬(Ambient parameter).Refines target) :
    attempt retained increment current = .inr (.inr ⟨(), unsupported⟩) := by
  unfold attempt
  rewrite [dif_pos paid, dif_neg unsupported]
  rfl

/-- An unsupported actual target box returns that failed local support condition before new line construction. -/
theorem attempt_unsupported
    {parameter : Canonical}
    {original : ClearGrid (Paths.polynomial parameter) (Ambient parameter)} (retained : Range original)
    (increment : Canonical) {target : Box} (current : ClearGrid (Paths.polynomial (parameter + increment)) target)
    (paid : Norm.Basic.normSq increment ≤ retained.request.tolerance)
    (unsupported : ¬(Ambient parameter).Refines target) :
    attempt retained increment current = .inr (.inr ⟨(), unsupported⟩) :=
  packaged_attempt_unsupported retained increment current paid unsupported

end Range

end Purelib.Curves.Legendre.Polynomial.Grid

end
