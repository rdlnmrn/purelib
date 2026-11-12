module

public import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Topology.Mesh.TriangleCut
public import Purelib.Geometry.Rational.Affine
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Membership
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

/-! # Total rational cuts of original oriented coordinate triangles

Finite signs distinguish on-line, one-sided and crossing triangles. A
crossing retains its cyclic apex, two exact fractions and both affine
points once. The three child occurrences use the original sewn cut patch;
endpoint crossings retain explicit zero-area children rather than hiding
stationary occurrences or identifying signed root owners.
-/

public section

namespace Purelib.Geometry.Triangles.AffineCut

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Topology.Polygon
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Topology.Mesh
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing

/-- The exact oriented affine-line reading; zero means incidence with that same line. -/
def level (first last point : Canonical) : Rational :=
  (last.re - first.re) * (point.im - first.im) -
    (last.im - first.im) * (point.re - first.re)

/-- Reverse only the sign convention when the opposite apex is selected. -/
def reading (positive : Bool) (first last point : Canonical) : Rational :=
  if positive then level first last point else -level first last point

/-- The same affine segment has the exact affine interpolation of its line readings. -/
theorem reading_affine (positive : Bool) (first last start finish : Canonical) (time : Rational) :
    reading positive first last (Affine.line start (finish - start) time) =
      reading positive first last start + time *
        (reading positive first last finish - reading positive first last start) := by
  have original : level first last (Affine.line start (finish - start) time) =
      level first last start + time * (level first last finish - level first last start) := by
    simp only [level, Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im]
    ring1
  cases positive with
  | false =>
    simp only [-eq_self, -iff_self, reading, if_neg (by decide +kernel : (false : Bool) ≠ true)]
    rewrite [original]
    ring1
  | true =>
    simp only [-eq_self, -iff_self, reading, if_pos (show (true : Bool) = true from rfl)]
    exact original

/-- Reversing the selected half-plane negates the same original line reading. -/
theorem reading_opposite (positive : Bool) (first last point : Canonical) :
    reading (!positive) first last point = -reading positive first last point := by
  cases positive with
  | false =>
    change reading true first last point = -reading false first last point
    simp only [-eq_self, -iff_self, reading, if_pos (show (true : Bool) = true from rfl),
      if_neg (by decide +kernel : (false : Bool) ≠ true)]
    ring1
  | true =>
    change reading false first last point = -reading true first last point
    simp only [-eq_self, -iff_self, reading, if_pos (show (true : Bool) = true from rfl),
      if_neg (by decide +kernel : (false : Bool) ≠ true)]
    rfl

/-- A zero selected-side reading is exact incidence on the same original affine line. -/
theorem reading_zero {positive : Bool} {first last point : Canonical}
    (zero : reading positive first last point = 0) : level first last point = 0 := by
  cases positive with
  | true => exact zero
  | false =>
      have negated := congrArg (fun value : Rational => -value) zero
      exact (show level first last point = -(-level first last point) by ring1).trans
        (negated.trans (by ring1))

/-- Read one literal original coordinate-corner occurrence. -/
def corner (triangle : CoordinateTriangle) : Fin 3 → Canonical :=
  Fin.cases triangle.first (Fin.cases triangle.second (Fin.cases triangle.third Fin.elim0))

/-- The original corner index of each actual cyclic occurrence. -/
def cornerIndex : Fin 3 → Fin 3 → Fin 3 :=
  Fin.cases (fun index => index)
    (Fin.cases (Fin.cases 1 (Fin.cases 2 (Fin.cases 0 Fin.elim0)))
      (Fin.cases (Fin.cases 2 (Fin.cases 0 (Fin.cases 1 Fin.elim0))) Fin.elim0))

/-- Retain an original triangle in one of its three cyclic orientations. -/
def rotate (triangle : CoordinateTriangle) : Fin 3 → CoordinateTriangle :=
  Fin.cases triangle (Fin.cases ⟨triangle.second, triangle.third, triangle.first⟩
    (Fin.cases ⟨triangle.third, triangle.first, triangle.second⟩ Fin.elim0))

/-- Every cyclic corner retains its exact original bounded corner occurrence.

This is an explicit occurrence map, rather than a coordinate search or a
sheet/root identification. It accounts for all three cyclic start choices.
-/
theorem rotate_corners (triangle : CoordinateTriangle) : ∀ turn index,
    corner (rotate triangle turn) index = corner triangle (cornerIndex turn index) :=
  Fin.cases
    (Fin.cases (by rfl) (Fin.cases (by rfl) (Fin.cases (by rfl) (fun impossible => nomatch impossible))))
    (Fin.cases
      (Fin.cases (by rfl) (Fin.cases (by rfl) (Fin.cases (by rfl) (fun impossible => nomatch impossible))))
      (Fin.cases
        (Fin.cases (by rfl) (Fin.cases (by rfl)
          (Fin.cases (by rfl) (fun impossible => nomatch impossible))))
        (fun impossible => nomatch impossible)))

/-- Cyclic orientation zero is the whole original triangle. -/
theorem rotate_zero (triangle : CoordinateTriangle) : rotate triangle 0 = triangle := by rfl

/-- A cyclic change of starting occurrence preserves the exact oriented area. -/
theorem rotate_area (triangle : CoordinateTriangle) : ∀ turn,
    coordinateTriangleArea (rotate triangle turn).first (rotate triangle turn).second
      (rotate triangle turn).third = coordinateTriangleArea triangle.first triangle.second triangle.third :=
  Fin.cases (by rfl)
    (Fin.cases
      (by
        change coordinateTriangleArea triangle.second triangle.third triangle.first = _
        unfold coordinateTriangleArea
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1)
      (Fin.cases
        (by
          change coordinateTriangleArea triangle.third triangle.first triangle.second = _
          unfold coordinateTriangleArea
          simp only [Fraction.Field.div_eq_mul_inv_direct]
          ring1) (fun impossible => nomatch impossible)))

/-- All three original occurrences lie on the same supplied affine line. -/
abbrev OnLine (first last : Canonical) (triangle : CoordinateTriangle) : Prop :=
  level first last triangle.first = 0 ∧ level first last triangle.second = 0 ∧ level first last triangle.third = 0

/-- The three actual triangle occurrences lie in the selected closed half-plane. -/
abbrev InHalf (positive : Bool) (first last : Canonical) (triangle : CoordinateTriangle) : Prop :=
  0 ≤ reading positive first last triangle.first ∧
    0 ≤ reading positive first last triangle.second ∧ 0 ≤ reading positive first last triangle.third

/-- One actual cyclic apex is strictly on one side and both other occurrences are weakly opposite. -/
abbrev Apex (first last : Canonical) (triangle : CoordinateTriangle) :=
  Σ turn : Fin 3, {positive : Bool //
    0 < reading positive first last (rotate triangle turn).first ∧
      reading positive first last (rotate triangle turn).second ≤ 0 ∧
        reading positive first last (rotate triangle turn).third ≤ 0}

/-- Negating a negative canonical rational gives a positive one. -/
private theorem negative_pos {value : Rational} (negative : value < 0) : 0 < -value := by
  have zero : -(0 : Rational) = 0 := by ring1
  exact Eq.mp (congrArg (fun lower => lower < -value) zero) (Arithmetic.neg_lt_neg_direct negative)

/-- Negating a nonnegative canonical rational gives a nonpositive one. -/
private theorem nonnegative_neg {value : Rational} (nonnegative : 0 ≤ value) : -value ≤ 0 := by
  have zero : -(0 : Rational) = 0 := by ring1
  exact (Arithmetic.neg_le_neg_direct nonnegative).trans_eq zero

/-- Negating a nonpositive canonical rational gives a nonnegative one. -/
private theorem nonpositive_neg {value : Rational} (nonpositive : value ≤ 0) : 0 ≤ -value := by
  have zero : -(0 : Rational) = 0 := by ring1
  exact Eq.mp (congrArg (fun lower => lower ≤ -value) zero) (Arithmetic.neg_le_neg_direct nonpositive)

/-- Select an actual cyclic apex by finite scalar comparisons when both half-plane tests fail. -/
private def findApex (first last : Canonical) (triangle : CoordinateTriangle)
    (notUpper : ¬ (0 ≤ level first last triangle.first ∧ 0 ≤ level first last triangle.second ∧
      0 ≤ level first last triangle.third))
    (notLower : ¬ (level first last triangle.first ≤ 0 ∧ level first last triangle.second ≤ 0 ∧
      level first last triangle.third ≤ 0)) : Apex first last triangle := by
  let a := level first last triangle.first
  let b := level first last triangle.second
  let c := level first last triangle.third
  if firstNonnegative : 0 ≤ a then
    if secondNonnegative : 0 ≤ b then
      have thirdNegative : c < 0 := Arithmetic.lt_of_not_ge_direct
        (fun third => notUpper ⟨firstNonnegative, secondNonnegative, third⟩)
      exact ⟨2, false, negative_pos thirdNegative,
        nonnegative_neg firstNonnegative, nonnegative_neg secondNonnegative⟩
    else
      have secondNegative : b < 0 := Arithmetic.lt_of_not_ge_direct secondNonnegative
      if thirdNonnegative : 0 ≤ c then
        exact ⟨1, false, negative_pos secondNegative,
          nonnegative_neg thirdNonnegative, nonnegative_neg firstNonnegative⟩
      else
        have thirdNegative : c < 0 := Arithmetic.lt_of_not_ge_direct thirdNonnegative
        have firstPositive : 0 < a := Arithmetic.lt_of_not_ge_direct
          (fun first => notLower ⟨first, secondNegative.le, thirdNegative.le⟩)
        exact ⟨0, true, firstPositive, secondNegative.le, thirdNegative.le⟩
  else
    have firstNegative : a < 0 := Arithmetic.lt_of_not_ge_direct firstNonnegative
    if secondNonnegative : 0 ≤ b then
      if thirdNonnegative : 0 ≤ c then
        exact ⟨0, false, negative_pos firstNegative,
          nonnegative_neg secondNonnegative, nonnegative_neg thirdNonnegative⟩
      else
        have thirdNegative : c < 0 := Arithmetic.lt_of_not_ge_direct thirdNonnegative
        have secondPositive : 0 < b := Arithmetic.lt_of_not_ge_direct
          (fun second => notLower ⟨firstNegative.le, second, thirdNegative.le⟩)
        exact ⟨1, true, secondPositive, thirdNegative.le, firstNegative.le⟩
    else
      have secondNegative : b < 0 := Arithmetic.lt_of_not_ge_direct secondNonnegative
      have thirdPositive : 0 < c := Arithmetic.lt_of_not_ge_direct
        (fun third => notLower ⟨firstNegative.le, secondNegative.le, third⟩)
      exact ⟨2, true, thirdPositive, firstNegative.le, secondNegative.le⟩

/-- The total actual finite alternatives: on-line, nontrivial one-sided, or an actual crossing apex. -/
abbrev Classification (first last : Canonical) (triangle : CoordinateTriangle) :=
  {_value : Unit // OnLine first last triangle} ⊕
    ({positive : Bool // InHalf positive first last triangle ∧ ¬ OnLine first last triangle} ⊕
      Apex first last triangle)

/-- Classify every original triangle by its actual rational line readings.

All-on-line is explicit. Boundary ties belong to the selected closed half;
only a genuine sign crossing selects an apex. This performs no root work.
-/
def classify (first last : Canonical) (triangle : CoordinateTriangle) : Classification first last triangle :=
  if onLine : OnLine first last triangle then .inl ⟨(), onLine⟩
  else if upper : 0 ≤ level first last triangle.first ∧ 0 ≤ level first last triangle.second ∧
      0 ≤ level first last triangle.third then .inr (.inl ⟨true, upper, onLine⟩)
  else if lower : level first last triangle.first ≤ 0 ∧ level first last triangle.second ≤ 0 ∧
      level first last triangle.third ≤ 0 then
    .inr (.inl ⟨false, ⟨nonpositive_neg lower.1,
      nonpositive_neg lower.2.1, nonpositive_neg lower.2.2⟩, onLine⟩)
  else .inr (.inr (findApex first last triangle upper lower))

/-- The exact fraction from a strict positive apex reading to a weak opposite endpoint. -/
def fraction (first last : Rational) : Rational := first / (first - last)

/-- A genuine crossing fraction is positive and at most one, including its endpoint case. -/
theorem fraction_bounds {first last : Rational} (positive : 0 < first) (opposite : last ≤ 0) :
    0 < fraction first last ∧ fraction first last ≤ 1 := by
  have denominator := Arithmetic.sub_pos_direct (opposite.trans_lt positive)
  refine ⟨Field.div_pos_direct positive denominator, (Field.div_le_iff_pos denominator).mpr ?_⟩
  have lower := Arithmetic.sub_le_sub_left_direct opposite first
  exact (show first = first - 0 by ring1).trans_le (lower.trans_eq (by ring1))

/-- The computed affine fraction has exactly zero interpolated reading. -/
theorem fraction_zero {first last : Rational} (positive : 0 < first) (opposite : last ≤ 0) :
    first + fraction first last * (last - first) = 0 := by
  have denominator := Arithmetic.sub_pos_direct (opposite.trans_lt positive)
  have cancel := Fraction.Field.div_mul_cancel_of_ne first (first - last) denominator.ne'
  unfold fraction
  calc
    first + first / (first - last) * (last - first) =
        first - (first / (first - last) * (first - last)) := by ring1
    _ = 0 := by rw [cancel]; ring1

/-- The exact three oriented children of the original two-edge cut.

The middle and final children triangulate the opposite quadrilateral on
its literal diagonal. Endpoint coincidences are not removed.
-/
def childFactory (triangle : CoordinateTriangle) (firstCut lastCut : Canonical) :
    CoordinateTriangle × CoordinateTriangle × CoordinateTriangle :=
  (⟨triangle.first, firstCut, lastCut⟩,
    ⟨firstCut, triangle.second, triangle.third⟩, ⟨firstCut, triangle.third, lastCut⟩)

/-- Retain both original fraction computations, both actual affine points, and the complete sewn patch.

The three children remain distinct occurrences. If a fraction is one, its
point is the original endpoint and the corresponding zero-area child is
retained explicitly; no root or observation equality follows from labels.
-/
abbrev CrossingCache (first last : Canonical) (triangle : CoordinateTriangle) (apex : Apex first last triangle) :=
  Σ original : {value : CoordinateTriangle // value = rotate triangle apex.1},
  Σ fractions : {value : Rational × Rational // value =
    (fraction (reading apex.2.val first last original.val.first) (reading apex.2.val first last original.val.second),
      fraction (reading apex.2.val first last original.val.first) (reading apex.2.val first last original.val.third))},
  Σ points : {value : Canonical × Canonical // value =
    (Affine.line original.val.first (original.val.second - original.val.first) fractions.val.1,
      Affine.line original.val.first (original.val.third - original.val.first) fractions.val.2)},
  Σ _children : {value : CoordinateTriangle × CoordinateTriangle × CoordinateTriangle //
    value = childFactory original.val points.val.1 points.val.2},
  {value : CutPatch TriangleCut.faces [0, 1, 2] TriangleCut.boundary // value = TriangleCut.build}

/-- Compute each actual cut fraction and point once, then retain the original sewn patch once. -/
def acquireCrossing (first last : Canonical) (triangle : CoordinateTriangle) (apex : Apex first last triangle) :
    CrossingCache first last triangle apex :=
  let original := rotate triangle apex.1
  let fractions :=
    (fraction (reading apex.2.val first last original.first) (reading apex.2.val first last original.second),
      fraction (reading apex.2.val first last original.first) (reading apex.2.val first last original.third))
  let points :=
    (Affine.line original.first (original.second - original.first) fractions.1,
      Affine.line original.first (original.third - original.first) fractions.2)
  let children := childFactory original points.1 points.2
  let patch := TriangleCut.build
  ⟨⟨original, rfl⟩, ⟨fractions, rfl⟩, ⟨points, rfl⟩, ⟨children, rfl⟩, ⟨patch, rfl⟩⟩

namespace CrossingCache

variable {first last : Canonical} {triangle : CoordinateTriangle} {apex : Apex first last triangle}
variable (cached : CrossingCache first last triangle apex)

/-- Read the whole retained cyclic copy of the original triangle. -/
def original : CoordinateTriangle := cached.1.val

/-- Read both actual once-computed rational cut fractions. -/
def fractions : Rational × Rational := cached.2.1.val

/-- Read both actual once-computed affine intersection points. -/
def points : Canonical × Canonical := cached.2.2.1.val

/-- Read the complete ordered child-triangle product. -/
def children : CoordinateTriangle × CoordinateTriangle × CoordinateTriangle := cached.2.2.2.1.val

/-- Read the actual original sewn cut patch with its complete refined source bank. -/
def patch : CutPatch TriangleCut.faces [0, 1, 2] TriangleCut.boundary := cached.2.2.2.2.val

/-- The retained original triangle is its exact cyclic occurrence. -/
theorem original_eq : cached.original = rotate triangle apex.1 := cached.1.property

/-- The whole original cyclic occurrence has exactly the old triangle's oriented area. -/
theorem original_area :
    coordinateTriangleArea cached.original.first cached.original.second cached.original.third =
      coordinateTriangleArea triangle.first triangle.second triangle.third :=
  (congrArg (fun value : CoordinateTriangle =>
    coordinateTriangleArea value.first value.second value.third) cached.original_eq).trans
      (rotate_area triangle apex.1)

/-- Both retained fractions are their actual original rational division factories. -/
theorem fractions_eq : cached.fractions =
    (fraction (reading apex.2.val first last cached.original.first)
      (reading apex.2.val first last cached.original.second),
      fraction (reading apex.2.val first last cached.original.first)
        (reading apex.2.val first last cached.original.third)) := cached.2.1.property

/-- Both retained points are their exact original affine factories at the SAME cached fractions. -/
theorem points_eq : cached.points =
    (Affine.line cached.original.first (cached.original.second - cached.original.first) cached.fractions.1,
      Affine.line cached.original.first (cached.original.third - cached.original.first) cached.fractions.2) :=
  cached.2.2.1.property

/-- The retained child product is its exact original ordered factory on those SAME cached points. -/
theorem children_eq : cached.children = childFactory cached.original cached.points.1 cached.points.2 :=
  cached.2.2.2.1.property

/-- The whole retained patch is the original two-seam constructor. -/
theorem patch_eq : cached.patch = TriangleCut.build := cached.2.2.2.2.property

/-- The retained cyclic apex has its actual strict/weak line readings. -/
theorem readings : 0 < reading apex.2.val first last cached.original.first ∧
    reading apex.2.val first last cached.original.second ≤ 0 ∧
      reading apex.2.val first last cached.original.third ≤ 0 :=
  Eq.mpr (congrArg (fun value : CoordinateTriangle =>
    0 < reading apex.2.val first last value.first ∧
      reading apex.2.val first last value.second ≤ 0 ∧ reading apex.2.val first last value.third ≤ 0)
        cached.original_eq) apex.2.property

/-- Both actual intersection fractions lie in their original closed sides and are strictly after the apex. -/
theorem bounds : (0 < cached.fractions.1 ∧ cached.fractions.1 ≤ 1) ∧
    (0 < cached.fractions.2 ∧ cached.fractions.2 ≤ 1) := by
  rw [cached.fractions_eq]
  exact ⟨fraction_bounds cached.readings.1 cached.readings.2.1,
    fraction_bounds cached.readings.1 cached.readings.2.2⟩

/-- Both actual intersections lie on the SAME supplied affine line. -/
theorem points_onLine : reading apex.2.val first last cached.points.1 = 0 ∧
    reading apex.2.val first last cached.points.2 = 0 := by
  rw [cached.points_eq, reading_affine, reading_affine, cached.fractions_eq]
  exact ⟨fraction_zero cached.readings.1 cached.readings.2.1,
    fraction_zero cached.readings.1 cached.readings.2.2⟩

/-- Both computed intersections have actual zero reading on the original line, independently of the side flag. -/
theorem points_level : level first last cached.points.1 = 0 ∧ level first last cached.points.2 = 0 :=
  ⟨reading_zero cached.points_onLine.1, reading_zero cached.points_onLine.2⟩

/-- The apex child and both opposite children lie in their actual selected closed half-planes. -/
theorem children_halves :
    InHalf apex.2.val first last cached.children.1 ∧
      InHalf (!apex.2.val) first last cached.children.2.1 ∧
        InHalf (!apex.2.val) first last cached.children.2.2 := by
  have opposite (point : Canonical) (nonpositive : reading apex.2.val first last point ≤ 0) :
      0 ≤ reading (!apex.2.val) first last point := by
    rw [reading_opposite]
    exact nonpositive_neg nonpositive
  rw [cached.children_eq]
  exact ⟨⟨cached.readings.1.le, cached.points_onLine.1.symm.le, cached.points_onLine.2.symm.le⟩,
    ⟨opposite _ cached.points_onLine.1.le, opposite _ cached.readings.2.1,
      opposite _ cached.readings.2.2⟩,
    ⟨opposite _ cached.points_onLine.1.le, opposite _ cached.readings.2.2,
      opposite _ cached.points_onLine.2.le⟩⟩

/-- A unit first fraction retains the original second corner as its actual point. -/
theorem first_endpoint (atEnd : cached.fractions.1 = 1) : cached.points.1 = cached.original.second := by
  rw [cached.points_eq, atEnd]
  exact Affine.line_one _ _

/-- A unit last fraction retains the original third corner as its actual point. -/
theorem last_endpoint (atEnd : cached.fractions.2 = 1) : cached.points.2 = cached.original.third := by
  rw [cached.points_eq, atEnd]
  exact Affine.line_one _ _

/-- Both actual new points remain in every original box containing the three retained corners. -/
theorem inside {box : Box} (contained : box.Contains cached.original.first ∧
    box.Contains cached.original.second ∧ box.Contains cached.original.third) :
    box.Contains cached.points.1 ∧ box.Contains cached.points.2 := by
  rw [cached.points_eq]
  exact ⟨Box.contains_line contained.1 contained.2.1 ⟨cached.bounds.1.1.le, cached.bounds.1.2⟩,
    Box.contains_line contained.1 contained.2.2 ⟨cached.bounds.2.1.le, cached.bounds.2.2⟩⟩

/-- Reverse only the affine parameter on the SAME original third-to-first side. -/
theorem reverse_last :
    Affine.line cached.original.third (cached.original.first - cached.original.third)
      (1 - cached.fractions.2) = cached.points.2 := by
  rw [cached.points_eq]
  apply Gaussian.Basic.ext <;>
    simp only [Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im] <;> ring1

/-- The three original side occurrences retain their literal five oriented subintervals.

Rows are second-cut/apex, apex/first-cut, first-cut/second-corner,
second/third corner, and third-corner/second-cut. Unit fractions keep the
zero-width last occurrence explicitly. These are pure derived metadata.
-/
def sidePieces : List (Stokes.OrientedEdge 3 × Rational × Rational) :=
  [(⟨2, 0⟩, 1 - cached.fractions.2, 1), (⟨0, 1⟩, 0, cached.fractions.1),
    (⟨0, 1⟩, cached.fractions.1, 1), (⟨1, 2⟩, 0, 1), (⟨2, 0⟩, 0, 1 - cached.fractions.2)]

/-- Every actual retained side subinterval is weakly ordered inside its SAME original side parameter. -/
theorem sidePieces_bounds : ∀ piece ∈ cached.sidePieces,
    0 ≤ piece.2.1 ∧ piece.2.1 ≤ piece.2.2 ∧ piece.2.2 ≤ 1 := by
  have remaining : 0 ≤ 1 - cached.fractions.2 := Arithmetic.sub_nonneg_direct cached.bounds.2.2
  have remainingUpper : 1 - cached.fractions.2 ≤ 1 :=
    (Arithmetic.sub_le_sub_left_direct cached.bounds.2.1.le 1).trans_eq (by ring1)
  intro piece member
  rcases List.Membership.mem_cons.mp member with same | member
  · cases same
    exact ⟨remaining, remainingUpper, Basic.le_refl 1⟩
  · rcases List.Membership.mem_cons.mp member with same | member
    · cases same
      exact ⟨Basic.le_refl 0, cached.bounds.1.1.le, cached.bounds.1.2⟩
    · rcases List.Membership.mem_cons.mp member with same | member
      · cases same
        exact ⟨cached.bounds.1.1.le, cached.bounds.1.2, Basic.le_refl 1⟩
      · rcases List.Membership.mem_cons.mp member with same | member
        · cases same
          exact ⟨Basic.le_refl 0, (by decide +kernel : (0 : Rational) ≤ 1), Basic.le_refl 1⟩
        · rcases List.Membership.mem_cons.mp member with same | member
          · cases same
            exact ⟨Basic.le_refl 0, remaining, remainingUpper⟩
          · exact (List.not_mem_nil member).elim

/-- Read one of the three actual retained child occurrences without rebuilding it. -/
def child : Fin 3 → CoordinateTriangle :=
  Fin.cases cached.children.1 (Fin.cases cached.children.2.1 (Fin.cases cached.children.2.2 Fin.elim0))

/-- Read a retained original/cut coordinate at its literal five-slot occurrence. -/
def coordinate : Fin 5 → Canonical :=
  Fin.cases cached.original.first (Fin.cases cached.points.1
    (Fin.cases cached.original.second (Fin.cases cached.original.third (Fin.cases cached.points.2 Fin.elim0))))

/-- The original refined source faces have the SAME three cached coordinate children in order. -/
theorem child_coordinates : ∀ index,
    cached.child index =
      (⟨cached.coordinate (TriangleCut.faces index).first,
        cached.coordinate (TriangleCut.faces index).second,
        cached.coordinate (TriangleCut.faces index).third⟩ : CoordinateTriangle) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible)))
  · unfold child
    rw [TriangleCut.faces_zero, cached.children_eq]
    rfl
  · change cached.child (1 : Fin 3) =
      (⟨cached.coordinate (TriangleCut.faces 1).first,
        cached.coordinate (TriangleCut.faces 1).second,
        cached.coordinate (TriangleCut.faces 1).third⟩ : CoordinateTriangle)
    unfold child
    rw [TriangleCut.faces_one, cached.children_eq]
    rfl
  · change cached.child (2 : Fin 3) =
      (⟨cached.coordinate (TriangleCut.faces 2).first,
        cached.coordinate (TriangleCut.faces 2).second,
        cached.coordinate (TriangleCut.faces 2).third⟩ : CoordinateTriangle)
    unfold child
    rw [TriangleCut.faces_two, cached.children_eq]
    rfl

/-- The actual source perimeter reads the same five ordered original/cut coordinate occurrences. -/
theorem boundary_coordinates : TriangleCut.boundary.map
    (fun edge => (cached.coordinate edge.start, cached.coordinate edge.finish)) =
      [(cached.points.2, cached.original.first), (cached.original.first, cached.points.1),
        (cached.points.1, cached.original.second), (cached.original.second, cached.original.third),
        (cached.original.third, cached.points.2)] := by
  rw [TriangleCut.perimeter_eq]
  rfl

/-- The SAME retained patch projects its actual child faces to the actual refined bank. -/
theorem patch_triangles : cached.patch.triangles.map
    (VertexSewing.OrientedTriangle.map cached.patch.vertexLabels) =
      [TriangleCut.faces 0, TriangleCut.faces 1, TriangleCut.faces 2] := cached.patch.triangles_eq

/-- The SAME retained patch projects its complete ordered perimeter to the actual refined bank. -/
theorem patch_boundary : cached.patch.boundary.map
    (VertexSewing.OrientedEdge.map cached.patch.vertexLabels) = TriangleCut.boundary :=
  cached.patch.boundary_eq

/-- The exact oriented areas of all three retained child occurrences.

These equations also identify a collapsed boundary child when one cut is
an original endpoint. No primitive-value area identity is asserted.
-/
theorem areas :
    coordinateTriangleArea cached.children.1.first cached.children.1.second cached.children.1.third =
      cached.fractions.1 * cached.fractions.2 *
        coordinateTriangleArea cached.original.first cached.original.second cached.original.third ∧
    coordinateTriangleArea cached.children.2.1.first cached.children.2.1.second cached.children.2.1.third =
      (1 - cached.fractions.1) *
        coordinateTriangleArea cached.original.first cached.original.second cached.original.third ∧
    coordinateTriangleArea cached.children.2.2.first cached.children.2.2.second cached.children.2.2.third =
      cached.fractions.1 * (1 - cached.fractions.2) *
        coordinateTriangleArea cached.original.first cached.original.second cached.original.third := by
  rw [cached.children_eq, cached.points_eq]
  dsimp only [childFactory, coordinateTriangleArea, Affine.line, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
    Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Cast.ofCoordinate_re,
    Gaussian.Cast.ofCoordinate_im]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  exact ⟨by ring1, by ring1, by ring1⟩

/-- A nonnegative original orientation gives nonnegative orientation of every actual child occurrence. -/
theorem nonnegative (positive : 0 ≤ coordinateTriangleArea triangle.first triangle.second triangle.third) :
    0 ≤ coordinateTriangleArea cached.children.1.first cached.children.1.second cached.children.1.third ∧
    0 ≤ coordinateTriangleArea cached.children.2.1.first cached.children.2.1.second cached.children.2.1.third ∧
    0 ≤ coordinateTriangleArea cached.children.2.2.first cached.children.2.2.second cached.children.2.2.third := by
  have original : 0 ≤ coordinateTriangleArea cached.original.first cached.original.second cached.original.third :=
    Eq.mpr (congrArg (fun area : Rational => 0 ≤ area) cached.original_area) positive
  rw [cached.areas.1, cached.areas.2.1, cached.areas.2.2]
  exact ⟨Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct cached.bounds.1.1.le cached.bounds.2.1.le) original,
    Arithmetic.mul_nonneg_direct (Arithmetic.sub_nonneg_direct cached.bounds.1.2) original,
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct cached.bounds.1.1.le
        (Arithmetic.sub_nonneg_direct cached.bounds.2.2)) original⟩

/-- The computed child coordinate areas sum to the exact original oriented area. -/
theorem area_sum :
    coordinateTriangleArea cached.children.1.first cached.children.1.second cached.children.1.third +
      coordinateTriangleArea cached.children.2.1.first cached.children.2.1.second cached.children.2.1.third +
        coordinateTriangleArea cached.children.2.2.first cached.children.2.2.second cached.children.2.2.third =
          coordinateTriangleArea triangle.first triangle.second triangle.third := by
  rw [cached.areas.1, cached.areas.2.1, cached.areas.2.2]
  have sum : cached.fractions.1 * cached.fractions.2 *
      coordinateTriangleArea cached.original.first cached.original.second cached.original.third +
      (1 - cached.fractions.1) *
        coordinateTriangleArea cached.original.first cached.original.second cached.original.third +
      cached.fractions.1 * (1 - cached.fractions.2) *
        coordinateTriangleArea cached.original.first cached.original.second cached.original.third =
      coordinateTriangleArea cached.original.first cached.original.second cached.original.third := by ring1
  exact sum.trans cached.original_area

/-- A unit first fraction records the actual collapsed second child; no occurrence is discarded. -/
theorem second_degenerate (atEnd : cached.fractions.1 = 1) :
    coordinateTriangleArea cached.children.2.1.first cached.children.2.1.second cached.children.2.1.third = 0 := by
  rw [cached.areas.2.1, atEnd]
  ring1

/-- A unit last fraction records the actual collapsed third child; no occurrence is discarded. -/
theorem third_degenerate (atEnd : cached.fractions.2 = 1) :
    coordinateTriangleArea cached.children.2.2.first cached.children.2.2.second cached.children.2.2.third = 0 := by
  rw [cached.areas.2.2, atEnd]
  ring1

/-- Strict interior crossings preserve strictly positive orientation of all three actual children. -/
theorem positive (originalPositive : 0 < coordinateTriangleArea triangle.first triangle.second triangle.third)
    (firstInterior : cached.fractions.1 < 1) (lastInterior : cached.fractions.2 < 1) :
    0 < coordinateTriangleArea cached.children.1.first cached.children.1.second cached.children.1.third ∧
    0 < coordinateTriangleArea cached.children.2.1.first cached.children.2.1.second cached.children.2.1.third ∧
    0 < coordinateTriangleArea cached.children.2.2.first cached.children.2.2.second cached.children.2.2.third := by
  have original : 0 < coordinateTriangleArea cached.original.first cached.original.second cached.original.third :=
    Eq.mpr (congrArg (fun area : Rational => 0 < area) cached.original_area) originalPositive
  rw [cached.areas.1, cached.areas.2.1, cached.areas.2.2]
  exact ⟨Arithmetic.mul_pos_direct
      (Arithmetic.mul_pos_direct cached.bounds.1.1 cached.bounds.2.1) original,
    Arithmetic.mul_pos_direct (Arithmetic.sub_pos_direct firstInterior) original,
    Arithmetic.mul_pos_direct
      (Arithmetic.mul_pos_direct cached.bounds.1.1 (Arithmetic.sub_pos_direct lastInterior)) original⟩

end CrossingCache

/-- The original one-face patch and its whole factory for on-line or uncut alternatives.

Its three coordinate occurrences come from the SAME retained input
triangle. Coincident values do not merge the three original cut slots.
-/
abbrev WholeCache :=
  {value : CutPatch (fun _ : Fin 1 => (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3)) [0]
      (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3).boundary //
    value = CutPatch.triangle (fun _ : Fin 1 =>
      (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3)) 0}

/-- The actual cached work selected by one retained finite classification.

A common dependent type keeps the whole-cut index and its readback on the
same branch family. Only a crossing carries newly computed fractions and
points; the other two alternatives retain one original triangle patch.
-/
abbrev Classification.Work (first last : Canonical) (triangle : CoordinateTriangle) :
    Classification first last triangle → Type
  | .inl _ => WholeCache
  | .inr (.inl _) => WholeCache
  | .inr (.inr apex) =>
      {value : CrossingCache first last triangle apex // value = acquireCrossing first last triangle apex}

/-- Retain the whole original triangle, total classification and actual branch work with factory equations. -/
abbrev Cut (first last : Canonical) (triangle : CoordinateTriangle) :=
  Σ original : {value : CoordinateTriangle // value = triangle},
  Σ branch : {value : Classification first last original.val // value = classify first last original.val},
    Classification.Work first last original.val branch.val

/-- Construct the total finite cut, retaining crossing work only in its genuine crossing branch. -/
def build (first last : Canonical) (triangle : CoordinateTriangle) : Cut first last triangle := by
  let original := triangle
  let branch := classify first last original
  let work : Classification.Work first last original branch :=
    match branch with
    | .inl _ =>
        let patch := CutPatch.triangle (fun _ : Fin 1 =>
          (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3)) 0
        ⟨patch, rfl⟩
    | .inr (.inl _) =>
        let patch := CutPatch.triangle (fun _ : Fin 1 =>
          (⟨0, 1, 2⟩ : Stokes.OrientedTriangle 3)) 0
        ⟨patch, rfl⟩
    | .inr (.inr apex) =>
        let cached := acquireCrossing first last original apex
        ⟨cached, rfl⟩
  exact ⟨⟨original, rfl⟩, ⟨branch, rfl⟩, work⟩

namespace Cut

variable {first last : Canonical} {triangle : CoordinateTriangle} (cached : Cut first last triangle)

/-- Read the complete original coordinate triangle retained in every alternative. -/
def original : CoordinateTriangle := cached.1.val

/-- The retained input is the whole original triangle. -/
theorem original_eq : cached.original = triangle := cached.1.property

/-- Read the actual finite alternative; no scalar classifier is rerun. -/
def classification : Classification first last cached.original := cached.2.1.val

/-- The stored alternative is the complete original finite classification factory. -/
theorem classification_eq : cached.classification = classify first last cached.original := cached.2.1.property

/-- Read the actual stored branch work, including the whole crossing cache where present. -/
def work : Classification.Work first last cached.original cached.classification := by
  unfold classification original
  exact cached.2.2

end Cut

/-- A nonconstant affine rational reading has only one parameter with value zero. -/
private theorem parameter_unique {first last before after : Rational} (distinct : first ≠ last)
    (beforeZero : first + before * (last - first) = 0)
    (afterZero : first + after * (last - first) = 0) : before = after := by
  have denominator : last - first ≠ 0 := by
    intro zero
    apply distinct
    calc
      first = (last - first) + first := by rw [zero]; ring1
      _ = last := by ring1
  apply Fraction.Field.mul_right_cancel_of_ne denominator
  calc
    before * (last - first) = (first + before * (last - first)) - first := by ring1
    _ = -first := by rw [beforeZero]; ring1
    _ = (first + after * (last - first)) - first := by rw [afterZero]; ring1
    _ = after * (last - first) := by ring1

/-- Reversing an actual affine segment reverses its retained parameter. -/
private theorem reverse_line (first last : Canonical) (time : Rational) :
    Affine.line last (first - last) time = Affine.line first (last - first) (1 - time) := by
  apply Gaussian.Basic.ext <;>
    simp only [Affine.line, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im] <;> ring1

/-- The original oriented line reading is affine in the original side parameter. -/
private theorem level_affine (first last start finish : Canonical) (time : Rational) :
    level first last (Affine.line start (finish - start) time) =
      level first last start + time * (level first last finish - level first last start) :=
  reading_affine true first last start finish time

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Sewing

/-- The original first coordinate corner is read without body reduction in callers. -/
theorem corner_zero (triangle : CoordinateTriangle) : corner triangle 0 = triangle.first := by rfl

/-- The original second coordinate corner is read without body reduction in callers. -/
theorem corner_one (triangle : CoordinateTriangle) : corner triangle 1 = triangle.second := by rfl

/-- The original third coordinate corner is read without body reduction in callers. -/
theorem corner_two (triangle : CoordinateTriangle) : corner triangle 2 = triangle.third := by rfl

namespace Apex

/-- Select the original finishing corner of one of the two cut side occurrences. -/
private def finishCorner : Fin 2 → Fin 3 := Fin.cases 1 (Fin.cases 2 (fun impossible => nomatch impossible))

/-- Read the actual signed indexed side from the original triangle and its retained cyclic apex. -/
def edge {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {vertexCount : Nat} (indices : OrientedTriangle vertexCount) (side : Fin 2) :
    OrientedEdge vertexCount :=
  ⟨SewnPrimitiveFaces.corner indices (cornerIndex apex.1 0),
    SewnPrimitiveFaces.corner indices (cornerIndex apex.1 (finishCorner side))⟩

/-- Retain the original source face and exact ordered corners of this actual cut-side occurrence. -/
def source {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {faceCount : Nat} (face : Fin faceCount) (side : Fin 2) :
    SewnPrimitiveContacts.SourceEdge faceCount :=
  ⟨face, cornerIndex apex.1 0, cornerIndex apex.1 (finishCorner side)⟩

/-- The retained source occurrence projects to its literal SAME signed indexed edge. -/
theorem source_project {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {vertexCount faceCount : Nat}
    (faces : Fin faceCount → OrientedTriangle vertexCount) (face : Fin faceCount) (side : Fin 2) :
    (apex.source face side).project faces = apex.edge (faces face) side := by rfl

/-- The actual finishing index is the original cyclic corner occurrence, before any coordinate or root reading. -/
theorem edge_finish {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {vertexCount : Nat} (indices : OrientedTriangle vertexCount)
    (side : Fin 2) : (apex.edge indices side).finish =
      SewnPrimitiveFaces.corner indices
        (cornerIndex apex.1 (Fin.cases (1 : Fin 3) (Fin.cases 2 (fun impossible => nomatch impossible)) side)) := by rfl

/-- Decide equality of two actual indexed edge occurrences by their complete bounded endpoints. -/
private def equalEdge {count : Nat} (first last : OrientedEdge count) : Decidable (first = last) :=
  if start : first.start = last.start then
    if finish : first.finish = last.finish then .isTrue (by
      cases first
      cases last
      cases start
      cases finish
      rfl)
    else .isFalse (fun same => finish (congrArg OrientedEdge.finish same))
  else .isFalse (fun same => start (congrArg OrientedEdge.start same))

/-- One original cut-side occurrence and its literal forward/reverse orientation at a requested indexed edge. -/
abbrev SideMatch {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {count : Nat} (indices : OrientedTriangle count)
    (target : OrientedEdge count) :=
  Σ side : Fin 2, {reversed : Bool // target =
    if reversed then (apex.edge indices side).reverse else apex.edge indices side}

/-- No original side occurrence has this exact requested indexed edge in either direction. -/
abbrev SideMissing {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {count : Nat} (indices : OrientedTriangle count)
    (target : OrientedEdge count) :=
  {_value : Unit // ∀ side, target ≠ apex.edge indices side ∧ target ≠ (apex.edge indices side).reverse}

/-- Select the first actual cut-side provider by ordered side and orientation, or retain all exact rejected cases.

This is finite indexed metadata. It compares neither coordinates nor root
Owners, performs no preparation, and never identifies repeated formal
source occurrences merely because their labels happen to coincide.
-/
def findSide {first last : Canonical} {triangle : CoordinateTriangle}
    (apex : Apex first last triangle) {count : Nat} (indices : OrientedTriangle count)
    (target : OrientedEdge count) : apex.SideMatch indices target ⊕ apex.SideMissing indices target :=
  match equalEdge target (apex.edge indices 0) with
  | .isTrue same => .inl ⟨0, ⟨false, same⟩⟩
  | .isFalse zero =>
      match equalEdge target (apex.edge indices 0).reverse with
      | .isTrue same => .inl ⟨0, ⟨true, same⟩⟩
      | .isFalse zeroReverse =>
          match equalEdge target (apex.edge indices 1) with
          | .isTrue same => .inl ⟨1, ⟨false, same⟩⟩
          | .isFalse one =>
              match equalEdge target (apex.edge indices 1).reverse with
              | .isTrue same => .inl ⟨1, ⟨true, same⟩⟩
              | .isFalse oneReverse =>
                  .inr ⟨(), Fin.cases ⟨zero, zeroReverse⟩
                    (Fin.cases ⟨one, oneReverse⟩ (fun impossible => nomatch impossible))⟩

end Apex

namespace CrossingCache

variable {first last : Canonical} {triangle : CoordinateTriangle} {apex : Apex first last triangle}
variable (cached : CrossingCache first last triangle apex)

/-- Read the stored fraction of the first or second original side occurrence. -/
def time : Fin 2 → Rational :=
  Fin.cases cached.fractions.1 (Fin.cases cached.fractions.2 (fun impossible => nomatch impossible))

/-- Read the stored Point coordinate of that SAME original side occurrence. -/
def point : Fin 2 → Canonical :=
  Fin.cases cached.points.1 (Fin.cases cached.points.2 (fun impossible => nomatch impossible))

/-- Read the original opposite endpoint of that actual rotated side occurrence. -/
def finish : Fin 2 → Canonical :=
  Fin.cases cached.original.second (Fin.cases cached.original.third (fun impossible => nomatch impossible))

/-- The first occurrence reads the original first stored fraction. -/
theorem time_zero : cached.time 0 = cached.fractions.1 := by rfl

/-- The second occurrence reads the original second stored fraction. -/
theorem time_one : cached.time 1 = cached.fractions.2 := by rfl

/-- The first occurrence reads the original first stored cut point. -/
theorem point_zero : cached.point 0 = cached.points.1 := by rfl

/-- The second occurrence reads the original second stored cut point. -/
theorem point_one : cached.point 1 = cached.points.2 := by rfl

/-- Each actual side occurrence uses its SAME stored positive fraction bounded by one. -/
theorem time_bounds : ∀ side, 0 < cached.time side ∧ cached.time side ≤ 1 := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact cached.bounds.1
  · exact cached.bounds.2

/-- Each actual cut coordinate is its SAME original side and stored fraction, without another computation. -/
theorem point_eq : ∀ side, cached.point side =
    Affine.line cached.original.first (cached.finish side - cached.original.first) (cached.time side) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact congrArg Prod.fst cached.points_eq
  · exact congrArg Prod.snd cached.points_eq

/-- Each selected actual cut point lies on the original cutting line. -/
theorem point_level : ∀ side, level first last (cached.point side) = 0 := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact cached.points_level.1
  · exact cached.points_level.2

/-- An actual side's opposite endpoint has the retained weak reading opposite its strict apex. -/
theorem finish_reading : ∀ side, reading apex.2.val first last (cached.finish side) ≤ 0 := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact cached.readings.2.1
  · exact cached.readings.2.2

/-- The original line readings at the actual side endpoints are distinct. -/
theorem level_distinct (side : Fin 2) :
    level first last cached.original.first ≠ level first last (cached.finish side) := by
  intro equal
  have read := congrArg (fun value : Rational => if apex.2.val then value else -value) equal
  change reading apex.2.val first last cached.original.first =
    reading apex.2.val first last (cached.finish side) at read
  exact cached.readings.1.2 (Eq.mpr (congrArg (fun value : Rational => value ≤ 0) read)
    (cached.finish_reading side))

/-- A unit stored fraction is the literal old endpoint occurrence. -/
theorem endpoint (side : Fin 2) (atEnd : cached.time side = 1) : cached.point side = cached.finish side := by
  rw [cached.point_eq side, atEnd]
  exact Affine.line_one _ _

/-- The finite alternatives are a strict interior fraction or the SAME old endpoint. -/
abbrev PointCase (side : Fin 2) :=
  {_value : Unit // cached.time side < 1} ⊕ {_value : Unit // cached.time side = 1}

/-- Decide the actual stored fraction once, retaining a proof of its exact strict/endpoint branch. -/
def pointCase (side : Fin 2) : cached.PointCase side :=
  if equal : cached.time side = 1 then .inr ⟨(), equal⟩
  else .inl ⟨(), Arithmetic.lt_of_not_ge_direct (fun reverse =>
    equal (Fraction.Order.Basic.le_antisymm _ _ (cached.time_bounds side).2 reverse))⟩

/-- The same oriented original side has the SAME actual rational cut fraction in both retained caches. -/
theorem time_same {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (side otherSide : Fin 2)
    (same : cached.original.first = other.original.first ∧ cached.finish side = other.finish otherSide) :
    cached.time side = other.time otherSide := by
  have leftZero : level first last cached.original.first + cached.time side *
      (level first last (cached.finish side) - level first last cached.original.first) = 0 :=
    (level_affine first last cached.original.first (cached.finish side) (cached.time side)).symm.trans
      ((congrArg (level first last) (cached.point_eq side)).symm.trans (cached.point_level side))
  have rightZero :=
    (level_affine first last other.original.first (other.finish otherSide) (other.time otherSide)).symm.trans
    ((congrArg (level first last) (other.point_eq otherSide)).symm.trans (other.point_level otherSide))
  rw [← same.1, ← same.2] at rightZero
  exact parameter_unique (cached.level_distinct side) leftZero rightZero

/-- The same actual oriented side gives equal coordinates, allowing reindexing of ONE retained Point cache. -/
theorem point_same {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (side otherSide : Fin 2)
    (same : cached.original.first = other.original.first ∧ cached.finish side = other.finish otherSide) :
    cached.point side = other.point otherSide := by
  rw [cached.point_eq side, other.point_eq otherSide, ← same.1, ← same.2,
    cached.time_same other side otherSide same]

/-- Opposite occurrences of the SAME original side reverse the actual stored rational cut parameter. -/
theorem time_reverse {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (side otherSide : Fin 2)
    (opposite : cached.original.first = other.finish otherSide ∧ cached.finish side = other.original.first) :
    cached.time side = 1 - other.time otherSide := by
  have leftZero : level first last cached.original.first + cached.time side *
      (level first last (cached.finish side) - level first last cached.original.first) = 0 :=
    (level_affine first last cached.original.first (cached.finish side) (cached.time side)).symm.trans
      ((congrArg (level first last) (cached.point_eq side)).symm.trans (cached.point_level side))
  have rightPoint : other.point otherSide = Affine.line cached.original.first
      (cached.finish side - cached.original.first) (1 - other.time otherSide) := by
    rw [other.point_eq otherSide, ← opposite.1, ← opposite.2]
    exact reverse_line _ _ _
  have rightZero :=
    (level_affine first last cached.original.first (cached.finish side) (1 - other.time otherSide)).symm.trans
    ((congrArg (level first last) rightPoint).symm.trans (other.point_level otherSide))
  exact parameter_unique (cached.level_distinct side) leftZero rightZero

/-- Opposite actual side occurrences meet at the same coordinate without equating independent root Owners. -/
theorem point_reverse {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (side otherSide : Fin 2)
    (opposite : cached.original.first = other.finish otherSide ∧ cached.finish side = other.original.first) :
    cached.point side = other.point otherSide := by
  have rightPoint : other.point otherSide = Affine.line cached.original.first
      (cached.finish side - cached.original.first) (1 - other.time otherSide) := by
    rw [other.point_eq otherSide, ← opposite.1, ← opposite.2]
    exact reverse_line _ _ _
  exact (cached.point_eq side).trans
    ((congrArg (fun time => Affine.line cached.original.first (cached.finish side - cached.original.first) time)
      (cached.time_reverse other side otherSide opposite)).trans rightPoint.symm)

/-- Coordinate lookup of an indexed original triangle respects its literal three corner occurrences. -/
private theorem coordinate_corner {vertexCount : Nat} (coordinate : Fin vertexCount → Canonical)
    (indices : OrientedTriangle vertexCount) : ∀ position,
    corner (⟨coordinate indices.first, coordinate indices.second, coordinate indices.third⟩ : CoordinateTriangle)
      position = coordinate (SewnPrimitiveFaces.corner indices position) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) <;> rfl

/-- The actual rotated coordinate corner reads the SAME original indexed corner. -/
theorem original_corner {vertexCount : Nat} (coordinate : Fin vertexCount → Canonical)
    (indices : OrientedTriangle vertexCount)
    (factory : triangle = ⟨coordinate indices.first, coordinate indices.second, coordinate indices.third⟩)
    (position : Fin 3) : corner cached.original position =
      coordinate (SewnPrimitiveFaces.corner indices (cornerIndex apex.1 position)) :=
  (congrArg (fun value => corner value position) cached.original_eq).trans
    ((rotate_corners triangle apex.1 position).trans
      ((congrArg (fun value => corner value (cornerIndex apex.1 position)) factory).trans
        (coordinate_corner coordinate indices (cornerIndex apex.1 position))))

/-- Literal signed edge indices, rather than coordinate search, select the two original geometric endpoints. -/
theorem edge_coordinates {vertexCount : Nat} (coordinate : Fin vertexCount → Canonical)
    (indices : OrientedTriangle vertexCount)
    (factory : triangle = ⟨coordinate indices.first, coordinate indices.second, coordinate indices.third⟩) :
    ∀ side, (coordinate (apex.edge indices side).start, coordinate (apex.edge indices side).finish) =
      (cached.original.first, cached.finish side) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact Prod.ext (cached.original_corner coordinate indices factory 0).symm
      (cached.original_corner coordinate indices factory 1).symm
  · exact Prod.ext (cached.original_corner coordinate indices factory 0).symm
      (cached.original_corner coordinate indices factory 2).symm

/-- Equal literal signed side occurrences allow the same cached cut Point to be reindexed in both patches. -/
theorem point_same_of_edge_eq {vertexCount : Nat} (coordinate : Fin vertexCount → Canonical)
    (indices : OrientedTriangle vertexCount)
    (factory : triangle = ⟨coordinate indices.first, coordinate indices.second, coordinate indices.third⟩)
    {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (otherIndices : OrientedTriangle vertexCount)
    (otherFactory : otherTriangle =
      ⟨coordinate otherIndices.first, coordinate otherIndices.second, coordinate otherIndices.third⟩)
    (side otherSide : Fin 2) (same : apex.edge indices side = otherApex.edge otherIndices otherSide) :
    cached.point side = other.point otherSide := by
  have endpoints := (cached.edge_coordinates coordinate indices factory side).symm.trans
    ((congrArg (fun edge : OrientedEdge vertexCount => (coordinate edge.start, coordinate edge.finish)) same).trans
      (other.edge_coordinates coordinate otherIndices otherFactory otherSide))
  exact cached.point_same other side otherSide ⟨congrArg Prod.fst endpoints, congrArg Prod.snd endpoints⟩

/-- Opposite literal signed side occurrences share one cut coordinate with reversed original orientation. -/
theorem point_reverse_of_edge_eq {vertexCount : Nat} (coordinate : Fin vertexCount → Canonical)
    (indices : OrientedTriangle vertexCount)
    (factory : triangle = ⟨coordinate indices.first, coordinate indices.second, coordinate indices.third⟩)
    {otherTriangle : CoordinateTriangle} {otherApex : Apex first last otherTriangle}
    (other : CrossingCache first last otherTriangle otherApex) (otherIndices : OrientedTriangle vertexCount)
    (otherFactory : otherTriangle =
      ⟨coordinate otherIndices.first, coordinate otherIndices.second, coordinate otherIndices.third⟩)
    (side otherSide : Fin 2) (opposite : apex.edge indices side = (otherApex.edge otherIndices otherSide).reverse) :
    cached.point side = other.point otherSide := by
  have left := cached.edge_coordinates coordinate indices factory side
  have right := other.edge_coordinates coordinate otherIndices otherFactory otherSide
  have start := (congrArg (fun edge : OrientedEdge vertexCount => coordinate edge.start) opposite).trans
    (congrArg coordinate (OrientedEdge.reverse_start (otherApex.edge otherIndices otherSide)))
  have finish := (congrArg (fun edge : OrientedEdge vertexCount => coordinate edge.finish) opposite).trans
    (congrArg coordinate (OrientedEdge.reverse_finish (otherApex.edge otherIndices otherSide)))
  exact cached.point_reverse other side otherSide
    ⟨(congrArg Prod.fst left).symm.trans (start.trans (congrArg Prod.snd right)),
      (congrArg Prod.snd left).symm.trans (finish.trans (congrArg Prod.fst right))⟩

/-- The first cut-bank slot reads the original rotated apex. -/
theorem coordinate_zero : cached.coordinate 0 = cached.original.first := by rfl

/-- The second cut-bank slot reads the SAME first retained cut point. -/
theorem coordinate_one : cached.coordinate 1 = cached.point 0 := by rfl

/-- The third cut-bank slot reads the original second rotated corner. -/
theorem coordinate_two : cached.coordinate 2 = cached.original.second := by rfl

/-- The fourth cut-bank slot reads the original third rotated corner. -/
theorem coordinate_three : cached.coordinate 3 = cached.original.third := by rfl

/-- The last cut-bank slot reads the SAME second retained cut point. -/
theorem coordinate_four : cached.coordinate 4 = cached.point 1 := by rfl

/-- A unit first cut has the literal b-slot coordinate in the original five-slot word. -/
theorem unit_first_coordinate (atEnd : cached.time 0 = 1) : cached.point 0 = cached.coordinate 2 :=
  (cached.endpoint 0 atEnd).trans cached.coordinate_two.symm

/-- A unit second cut has the literal c-slot coordinate in the original five-slot word. -/
theorem unit_last_coordinate (atEnd : cached.time 1 = 1) : cached.point 1 = cached.coordinate 3 :=
  (cached.endpoint 1 atEnd).trans cached.coordinate_three.symm

end CrossingCache

end Purelib.Geometry.Triangles.AffineCut

end
