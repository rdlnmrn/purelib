module

public import Purelib.RootIsolation.Newton.Search.Center.Basic
public import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Band.State
public import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.Approximation.Gaussian.Grid.Box
public import Purelib.Data.Rat.Dyadic.Basic
public import Purelib.Geometry.Rational.Box.Budget.Center
public import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Bounded dyadic proposals checked against the original refinement request

Both the proposal grid and the pre-band radius are genuine reciprocal powers
of two. Their bit-length scale estimates supply no acceptance assumptions.
The original finite band checker certifies the same polynomial and current
owner; the returned state is checked again at the original accuracy. A finite
unsuccessful attempt leaves its caller's total subdivision fallback intact.
-/

public section

namespace Purelib.RootIsolation.Newton.Search.Dyadic

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Polynomial
open Purelib.RootIsolation

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}

/-- Choose one speculative dyadic grid budget from the original tolerance and both current widths. -/
@[expose] def gridBudget (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) :
    Fraction.Rational :=
  Data.Rat.Dyadic.Basic.magnitudeScale (min epsilon (min current.box.widthX current.box.widthY))

/-- A grid budget below both widths is selected unchanged by the original grid constructor. -/
theorem grid_eq_budget (current : State.Raw.RawWindingState p ambient) (basis : Fraction.Rational)
    (widthX : basis ≤ current.box.widthX) (widthY : basis ≤ current.box.widthY) (bits : Nat) :
    Grid.Box.grid current.box basis bits = basis / (64 * 2 ^ bits) := by
  unfold Grid.Box.grid
  rewrite [Fraction.Order.Basic.min_eq_left (Fraction.Order.Basic.le_min widthX widthY)]
  rfl

/-- Choose a speculative dyadic radius before constructing any candidate band. -/
@[expose] def radius (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  Data.Rat.Dyadic.Basic.magnitudeScale (Box.Budget.Center.radius current.box epsilon center)

/-- A radius below the original budget is below the original quarter-margin. -/
theorem radius_le_margin (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational)
    (within : r ≤ Box.Budget.Center.radius current.box epsilon center) :
    r ≤ min (center.re - current.box.xLower)
      (min (current.box.xUpper - center.re)
        (min (center.im - current.box.yLower) (current.box.yUpper - center.im))) / 4 :=
  within.trans (Fraction.Order.Basic.min_le_right _ _)

/-- The unchanged old checker uses exactly the supplied radius at target eight times that radius. -/
theorem radius_at_target (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational)
    (within : r ≤ Box.Budget.Center.radius current.box epsilon center) :
    Box.Budget.Center.radius current.box (8 * r) center = r := by
  have cancellation : (8 * r) / 8 = r := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide : (8 : Fraction.Rational) ≠ 0)
    exact (Fraction.Field.div_mul_cancel_of_ne (8 * r) 8 (by decide)).trans
      (Fraction.Field.mul_comm 8 r)
  change min ((8 * r) / 8) _ = r
  rewrite [cancellation]
  exact Fraction.Order.Basic.min_eq_left (radius_le_margin current epsilon center r within)

/-- Check one dyadic-radius candidate with the original band checker and the original requested accuracy.

The old checker at eight times the radius supplies winding four, full ambient
line clearances and strict containment. Only its same actual state is wrapped
with the final direct squared-diagonal comparison against the original epsilon.
-/
@[expose] def check
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Data.Gaussian.Basic.Canonical) (r : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Option (Refinement current epsilon) :=
  if 0 < r then
    if r ≤ Box.Budget.Center.radius current.box epsilon center then
      match Center.Basic.checkCenter elimination current (8 * r) center clearances with
      | none => none
      | some accepted =>
          if accurate : accepted.state.box.diagonalSq ≤ epsilon ^ 2 then
            some ⟨accepted.state, accepted.strict, accurate⟩
          else none
    else none
  else none

/-- Inspect a bounded sequence of rounded Newton proposals using the retained grid budget.

The complete attempt checks this budget against both box widths before using
it, so each executed grid is genuinely dyadic. Every accepted state is checked
at the original epsilon; rejection makes no claim of global failure.
-/
@[expose] def search
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon basis : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (fuel bits : Nat) (proposal : Data.Gaussian.Basic.Canonical) : Option (Refinement current epsilon) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let center := Grid.Box.roundedCenter current.box basis bits proposal
      let r := radius current epsilon center
      match check elimination current epsilon center r clearances with
      | some accepted => some accepted
      | none =>
          if Data.Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then
            none
          else search elimination current epsilon basis clearances fuel (bits + 2)
            (Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center))
termination_by structural fuel

attribute [local irreducible] check radius Grid.Box.roundedCenter
  Data.Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter

/-- The zero-fuel bounded dyadic search executes no candidate. -/
theorem search_zero
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon basis : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (bits : Nat) (proposal : Data.Gaussian.Basic.Canonical) :
    search elimination current epsilon basis clearances 0 bits proposal = none := rfl

/-- One dyadic search step retains the exact proposed center, radius, acceptance and next update. -/
theorem search_succ
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon basis : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (fuel bits : Nat) (proposal : Data.Gaussian.Basic.Canonical) :
    search elimination current epsilon basis clearances (fuel + 1) bits proposal =
      (let center := Grid.Box.roundedCenter current.box basis bits proposal
       let r := radius current epsilon center
       match check elimination current epsilon center r clearances with
       | some accepted => some accepted
       | none => if Data.Gaussian.Basic.value
           (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
         else search elimination current epsilon basis clearances fuel (bits + 2)
           (Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center))) := rfl

/-- Try at most six genuinely dyadic proposals before returning a finite inconclusive result.

The grid budget is checked against both original widths. The first midpoint,
original polynomial, selected occurrence and requested epsilon remain fixed;
only speculative coordinates change. A caller retains its total fallback.
-/
@[expose] def attempt
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Option (Refinement current epsilon) :=
  let basis := gridBudget current epsilon
  if 0 < basis then
    if basis ≤ current.box.widthX then
      if basis ≤ current.box.widthY then
        search elimination current epsilon basis clearances 6 0
          ⟨(current.box.xLower + current.box.xUpper) / 2,
            (current.box.yLower + current.box.yUpper) / 2⟩
      else none
    else none
  else none

/-- Refine an original raw region by finite dyadic proposals with total Newton extraction fallback.

An accepted proposal retains its complete checked result at the original
accuracy. Only finite rejection selects the existing total extraction on that
same raw source and request. No preliminary winding-one track or fixed
canonical extraction is required before the attempt.
-/
@[expose] def refineRaw (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Refinement current epsilon :=
  match attempt elimination current epsilon with
  | some accepted => accepted
  | none => Newton.Band.State.refinementOfOutput
      (Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive)

/-- A successful finite attempt supplies the identical complete raw refinement. -/
theorem refineRaw_accept (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (accepted : Refinement current epsilon) (found : attempt elimination current epsilon = some accepted) :
    refineRaw input elimination current epsilon positive = accepted := by
  unfold refineRaw
  rewrite [found]
  rfl

/-- Finite rejection uses the complete extraction on the unchanged raw request. -/
theorem refineRaw_fallback (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (missing : attempt elimination current epsilon = none) :
    refineRaw input elimination current epsilon positive = Newton.Band.State.refinementOfOutput
      (Newton.Band.Build.extract input.degreeAtLeastTwo input.squarefree elimination current positive) := by
  unfold refineRaw
  rewrite [missing]
  rfl

end Purelib.RootIsolation.Newton.Search.Dyadic
