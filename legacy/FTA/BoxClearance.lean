import FTA.LocalExtraction
import FTA.PathClearance
import FTA.Winding

/-!
# Quantitative clearance on rational axis lines

Safe rectangular grids reuse boundary lines many times.  These small wrapper
structures turn a path-clearance certificate into a geometric vertical or
horizontal line certificate, restrict it to subboxes, and combine four such
lines into one box-boundary certificate.
-/

namespace FTA.BoxClearance

open CCL CCL.GaussianRat
open FTA.LocalExtraction
open FTA.PathClearance
open FTA.PathPolynomial
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

/-- A polynomial zero contained in a box with certified clear boundary lies
strictly inside all four sides. -/
theorem BoxBoundaryClearanceCertificate.root_strictContains
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (certificate : BoxBoundaryClearanceCertificate p B) {z : QI}
    (contains : B.Contains z) (root : p.eval z = 0) :
    B.StrictContains z := by
  have notBoundary : ¬OnBoxBoundary B z := by
    intro boundary
    have lower := certificate.lower z boundary
    rw [root, normSq_zero] at lower
    linarith [certificate.positive]
  refine ⟨lt_of_le_of_ne contains.1 ?_, lt_of_le_of_ne contains.2.1 ?_,
    lt_of_le_of_ne contains.2.2.1 ?_, lt_of_le_of_ne contains.2.2.2 ?_⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inl equal.symm⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inl equal)⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inr (Or.inl equal.symm))⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inr (Or.inr equal))⟩

structure VerticalLineClearance
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (x : ℚ) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ y : ℚ, ambient.yLower ≤ y → y ≤ ambient.yUpper →
    bound ≤ normSq (p.eval (CCL.GaussianRat.mk x y))

structure HorizontalLineClearance
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (y : ℚ) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ x : ℚ, ambient.xLower ≤ x → x ≤ ambient.xUpper →
    bound ≤ normSq (p.eval (CCL.GaussianRat.mk x y))

def VerticalLineClearance.restrict
    {p : GaussianPolynomial} {ambient small : CCL.RatBox} {x : ℚ}
    (certificate : VerticalLineClearance p ambient x)
    (hrefines : small.Refines ambient) : VerticalLineClearance p small x where
  bound := certificate.bound
  positive := certificate.positive
  lower := fun y hLower hUpper => certificate.lower y
    (hrefines.2.2.1.trans hLower) (hUpper.trans hrefines.2.2.2)

def HorizontalLineClearance.restrict
    {p : GaussianPolynomial} {ambient small : CCL.RatBox} {y : ℚ}
    (certificate : HorizontalLineClearance p ambient y)
    (hrefines : small.Refines ambient) : HorizontalLineClearance p small y where
  bound := certificate.bound
  positive := certificate.positive
  lower := fun x hLower hUpper => certificate.lower x
    (hrefines.1.trans hLower) (hUpper.trans hrefines.2.1)

/-- Convert the executable path certificate for `x + it` into geometric
vertical-line clearance. -/
def verticalOfPathCertificate
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (x : ℚ)
    (certificate : Certificate
      (pathReal p (verticalBase x) verticalDirection)
      (pathImag p (verticalBase x) verticalDirection)
      ⟨ambient.yLower, ambient.yUpper⟩) :
    VerticalLineClearance p ambient x where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro y hLower hUpper
    have h := certificate.lower y hLower hUpper
    simpa only [normSq, eval_pathReal, eval_pathImag, line_vertical] using h

/-- Convert the executable path certificate for `t + iy` into geometric
horizontal-line clearance. -/
def horizontalOfPathCertificate
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (y : ℚ)
    (certificate : Certificate
      (pathReal p (horizontalBase y) horizontalDirection)
      (pathImag p (horizontalBase y) horizontalDirection)
      ⟨ambient.xLower, ambient.xUpper⟩) :
    HorizontalLineClearance p ambient y where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x hLower hUpper
    have h := certificate.lower x hLower hUpper
    simpa only [normSq, eval_pathReal, eval_pathImag, line_horizontal] using h

def leftOfBoundary
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (certificate : BoxBoundaryClearanceCertificate p B) :
    VerticalLineClearance p B B.xLower where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro y hLower hUpper
    apply certificate.lower
    exact ⟨⟨le_rfl, B.x_valid, hLower, hUpper⟩, Or.inl rfl⟩

def rightOfBoundary
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (certificate : BoxBoundaryClearanceCertificate p B) :
    VerticalLineClearance p B B.xUpper where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro y hLower hUpper
    apply certificate.lower
    exact ⟨⟨B.x_valid, le_rfl, hLower, hUpper⟩, Or.inr (Or.inl rfl)⟩

def bottomOfBoundary
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (certificate : BoxBoundaryClearanceCertificate p B) :
    HorizontalLineClearance p B B.yLower where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x hLower hUpper
    apply certificate.lower
    exact ⟨⟨hLower, hUpper, le_rfl, B.y_valid⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩

def topOfBoundary
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (certificate : BoxBoundaryClearanceCertificate p B) :
    HorizontalLineClearance p B B.yUpper where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x hLower hUpper
    apply certificate.lower
    exact ⟨⟨hLower, hUpper, B.y_valid, le_rfl⟩,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Four quantitative side certificates combine by a finite minimum into a
single box-boundary certificate. -/
def boundaryOfLines
    {p : GaussianPolynomial} {B : CCL.RatBox}
    (left : VerticalLineClearance p B B.xLower)
    (right : VerticalLineClearance p B B.xUpper)
    (bottom : HorizontalLineClearance p B B.yLower)
    (top : HorizontalLineClearance p B B.yUpper) :
    BoxBoundaryClearanceCertificate p B := by
  let bound := min left.bound (min right.bound (min bottom.bound top.bound))
  exact
    { bound := bound
      positive := lt_min left.positive
        (lt_min right.positive (lt_min bottom.positive top.positive))
      lower := by
        intro z hz
        rcases hz.1 with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
        rcases hz.2 with hleft | hright | hbottom | htop
        · calc
            bound ≤ left.bound := min_le_left _ _
            _ ≤ normSq (p.eval z) := by
              have h := left.lower z.im hyLower hyUpper
              have hzEq : CCL.GaussianRat.mk B.xLower z.im = z := by
                ext
                · exact hleft.symm
                · rfl
              simpa only [hzEq] using h
        · calc
            bound ≤ right.bound :=
              (min_le_right _ _).trans (min_le_left _ _)
            _ ≤ normSq (p.eval z) := by
              have h := right.lower z.im hyLower hyUpper
              have hzEq : CCL.GaussianRat.mk B.xUpper z.im = z := by
                ext
                · exact hright.symm
                · rfl
              simpa only [hzEq] using h
        · calc
            bound ≤ bottom.bound :=
              (min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_left _ _))
            _ ≤ normSq (p.eval z) := by
              have h := bottom.lower z.re hxLower hxUpper
              have hzEq : CCL.GaussianRat.mk z.re B.yLower = z := by
                ext
                · rfl
                · exact hbottom.symm
              simpa only [hzEq] using h
        · calc
            bound ≤ top.bound :=
              (min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_right _ _))
            _ ≤ normSq (p.eval z) := by
              have h := top.lower z.re hxLower hxUpper
              have hzEq : CCL.GaussianRat.mk z.re B.yUpper = z := by
                ext
                · rfl
                · exact htop.symm
              simpa only [hzEq] using h }

end FTA.BoxClearance
