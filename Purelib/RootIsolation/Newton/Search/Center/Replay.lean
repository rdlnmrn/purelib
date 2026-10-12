module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Geometry.Rational.Box.Budget.Center
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational.Box.Band.Basic (BandBox)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
Expose the original candidate's winding request before clearance construction.
The pending value caches its selected band. Supplying a source-certified
winding restores exactly the original complete optional refinement, including
the original clearance constructors. No alternative owner is substituted.
-/

namespace Purelib.RootIsolation.Newton.Search.Center.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
  (center : Gaussian.Basic.Canonical) (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)

set_option genInjectivity false in
/-- A retained center candidate passing radius, containment and accuracy checks.

The band is exactly the original eliminant-selected band; its winding check is still pending. -/
structure Pending where
  /-- The original center radius is strictly positive. -/ positive : 0 < Box.Budget.Center.radius current.box epsilon
    center
  /-- The retained eliminant-safe band at the original center and radius. -/ band : BandBox center
    (Box.Budget.Center.radius current.box epsilon center)
  /-- The retained band equals the exact eliminant-selected band. -/ band_eq : band = Elimination.Axis.Band.selectedBand
    elimination center _ positive
  /-- The selected band lies strictly inside the original current box. -/ strict : band.box.StrictInterior current.box
  /-- The selected band meets the original squared-diagonal request. -/ accurate : band.box.diagonalSq ≤ epsilon ^ 2

constructive_injectivity Pending

set_option genInjectivity false in
/-- A displayed failed condition of the original finite center check.

Each outcome retains the attempted radius or selected band and the precise failed positivity, containment, accuracy or
winding test. -/
inductive Rejection where
  /-- The original computed center radius fails positivity. -/ | nonpositive (failed : ¬ 0 < Box.Budget.Center.radius
    current.box epsilon center)
  /-- The exact selected band fails strict containment in the original current box. -/ | containment (positive : 0 <
    Box.Budget.Center.radius current.box epsilon center)
      (band : BandBox center (Box.Budget.Center.radius current.box epsilon center))
      (source : band = Elimination.Axis.Band.selectedBand elimination center _ positive)
      (failed : ¬ band.box.StrictInterior current.box)
  /-- The contained selected band fails the original squared-diagonal request. -/ | accuracy (positive : 0 <
    Box.Budget.Center.radius current.box epsilon center)
      (band : BandBox center (Box.Budget.Center.radius current.box epsilon center))
      (source : band = Elimination.Axis.Band.selectedBand elimination center _ positive)
      (strict : band.box.StrictInterior current.box)
      (failed : ¬ band.box.diagonalSq ≤ epsilon ^ 2)
  /-- The retained pending band has a displayed raw winding different from four. -/ | winding (candidate :
    Pending elimination current epsilon center) (value : Int)
      (source : value = Winding.Box.Basic.quadrupledBoxWinding p candidate.band.box)
      (failed : value ≠ 4)

constructive_injectivity Rejection

set_option genInjectivity false in
/-- The result of the geometric portion of a finite center check.

Rejection retains the original checker equation; a pending value retains the exact band awaiting winding evaluation. -/
inductive Preparation where
  /-- A typed geometric rejection with the original checker's exact none result. -/ | rejected (reason :
    Rejection elimination current epsilon center)
      (equation : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
  /-- The retained geometric candidate awaiting its winding check. -/ | pending (value :
    Pending elimination current epsilon center)

constructive_injectivity Preparation

set_option genInjectivity false in
/-- A failed candidate identifies its violated finite condition. It makes
no claim about a pole, the total extractor or later proposals. -/
inductive Outcome where
  /-- The exact accepted refinement, identified with the original checker result. -/ | accepted (value :
    Refinement current epsilon)
      (equation : some value = Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances)
  /-- A typed rejection, identified with the original checker's none result. -/ | rejected (reason :
    Rejection elimination current epsilon center)
      (equation : none = Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances)

constructive_injectivity Outcome

/-- Run the radius, containment and accuracy checks for the original proposed center.

Retain the exact selected band on success, or a typed failed condition and original checker equation. -/
def prepare : Preparation
  elimination current epsilon center clearances :=
  if positive : 0 < Box.Budget.Center.radius current.box epsilon center then
    let band := Elimination.Axis.Band.selectedBand elimination center _ positive
    if strict : band.box.StrictInterior current.box then
      if accurate : band.box.diagonalSq ≤ epsilon ^ 2 then
        .pending ⟨positive, band, rfl, strict, accurate⟩
      else .rejected (.accuracy positive band rfl strict accurate) (by
        dsimp only [band, Box.Budget.Center.radius] at strict accurate
        unfold Newton.Search.Center.Basic.checkCenter
        change (if h : 0 < Box.Budget.Center.radius current.box epsilon center then _ else _) = _
        rewrite [dif_pos positive, dif_pos strict, dif_neg accurate]
        exact Eq.refl _)
    else .rejected (.containment positive band rfl strict) (by
      dsimp only [band, Box.Budget.Center.radius] at strict
      unfold Newton.Search.Center.Basic.checkCenter
      change (if h : 0 < Box.Budget.Center.radius current.box epsilon center then _ else _) = _
      rewrite [dif_pos positive, dif_neg strict]
      exact Eq.refl _)
  else .rejected (.nonpositive positive) (by
    unfold Newton.Search.Center.Basic.checkCenter
    change (if h : 0 < Box.Budget.Center.radius current.box epsilon center then _ else _) = _
    exact dif_neg positive)

set_option genInjectivity false in
/-- The four cached ambient line clearances for one retained pending band.

Each cache is identified with the original clearance provider at the band's exact selected coordinate. -/
structure Lines (pending : Pending
  elimination current epsilon center) where
  /-- The original ambient vertical clearance at the selected left side. -/ left :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient pending.band.box.xLower
  /-- The original ambient vertical clearance at the selected right side. -/ right :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient pending.band.box.xUpper
  /-- The original ambient horizontal clearance at the selected bottom side. -/ bottom :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient pending.band.box.yLower
  /-- The original ambient horizontal clearance at the selected top side. -/ top :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient pending.band.box.yUpper
  /-- The cached left clearance equals the original provider's result. -/ left_eq : left = clearances.vertical ambient
    pending.band.box.xLower (by
      rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_left_nonzero elimination center pending.positive)
  /-- The cached right clearance equals the original provider's result. -/ right_eq : right = clearances.vertical
    ambient pending.band.box.xUpper (by
      rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_right_nonzero elimination center pending.positive)
  /-- The cached bottom clearance equals the original provider's result. -/ bottom_eq : bottom = clearances.horizontal
    ambient pending.band.box.yLower (by
      rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_bottom_nonzero elimination center pending.positive)
  /-- The cached top clearance equals the original provider's result. -/ top_eq : top = clearances.horizontal ambient
    pending.band.box.yUpper (by
      rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_top_nonzero elimination center pending.positive)

constructive_injectivity Lines

/-- Finish a pending center check from its retained exact winding value.

Winding four restores the original cached line clearances and yields the certified refinement; every other value records
its failed winding test. -/
def Pending.finish (pending :
  Pending elimination current epsilon center)
    (index : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p pending.band.box })
    (restore : index.val = 4 → Lines elimination current epsilon center clearances pending)
      :
    Outcome elimination current epsilon center clearances :=
  if four : index.val = 4 then
    let lines := restore four
    let nested := (Geometry.Rational.Box.Refinement.StrictInterior.refines pending.strict).trans current.refinesAmbient
    let left := lines.left
    let right := lines.right
    let bottom := lines.bottom
    let top := lines.top
    let result : Refinement current epsilon :=
      { state :=
          { box := pending.band.box
            refinesAmbient := nested
            proper := pending.band.proper pending.positive
            clearance := Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict nested)
              (right.restrict nested) (bottom.restrict nested) (top.restrict nested)
            rawWindingFour := index.property.symm.trans four
            ambientLeftClearance := left
            ambientRightClearance := right
            ambientBottomClearance := bottom
            ambientTopClearance := top }
        strict := pending.strict
        accurate := pending.accurate }
    .accepted result (by
      have bandEq := pending.band_eq
      dsimp only [Box.Budget.Center.radius] at bandEq
      unfold Newton.Search.Center.Basic.checkCenter
      change _ = (if h : 0 < Box.Budget.Center.radius current.box epsilon center then _ else _)
      rw [dif_pos pending.positive]
      simp only [← bandEq, dif_pos pending.strict, dif_pos pending.accurate,
        dif_pos (index.property.symm.trans four)]
      dsimp only [result, left, right, bottom, top]
      rw [lines.left_eq, lines.right_eq, lines.bottom_eq, lines.top_eq]
      rcases pending with ⟨positive, band, equation, strict, accurate⟩
      subst band
      rfl)
  else .rejected (.winding pending index.val index.property four) (by
    have bandEq := pending.band_eq
    dsimp only [Box.Budget.Center.radius] at bandEq
    have failed : Winding.Box.Basic.quadrupledBoxWinding p pending.band.box ≠ 4 := by
      rw [← index.property]; exact four
    unfold Newton.Search.Center.Basic.checkCenter
    change _ = (if h : 0 < Box.Budget.Center.radius current.box epsilon center then _ else _)
    rw [dif_pos pending.positive]
    conv_rhs => simp only [← bandEq, dif_pos pending.strict, dif_pos pending.accurate, dif_neg failed])

end Purelib.RootIsolation.Newton.Search.Center.Replay

end
