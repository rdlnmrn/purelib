module

public import Purelib.Curves.Legendre.Degeneration
public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Constants
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.RootIsolation.Owner.Local.Split
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.RootIsolation.State.WindingOne.Transport
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Tactic.Ring

/-!
# Original cofactor root owners on Legendre collision patches

The zero collision chooses the root near i of the original cofactor Z-1;
the one collision chooses the root near one of the original cofactor Z.
Their half-radius root squares have source clearance 9/16, while the original
spatial patch bounds the cofactor variation by 1/2. The resulting Rouché
bridges construct actual winding-one tracks of those unchanged cofactor values.

For a retained result `root := owner site point inside`, the existing
`CertifiedSquareRoot.rawRoot root.track` returns its executable coherent
channel, and `rawRoot_square root.track` supplies the operational square
equation. Both use that same retained track. No matrix action chooses its sign.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.UnitRoot

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

/-- The original cofactor's signed reference root at the selected zero or one node. -/
@[expose] def seed (site : Fin 2) : Canonical := Data.Fin.cases Constants.imaginaryUnit (fun _ => 1) site

/-- The same reference root has the exact square of the original cofactor at the node. -/
theorem seed_square (site : Fin 2) : seed site ^ 2 = (unitPolynomial site).eval (criticalValue site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The computed half-radius square about the retained signed reference root. -/
@[expose] def box (site : Fin 2) : Box :=
  Box.Square.Centered.Affine.centeredSquare (seed site) (1 / 2) (by decide +kernel)

/-- The opposite original reference root has a computed strict outside side on the selected root square. -/
def oppositeSide : (site : Fin 2) → (box site).OutsideSide (-seed site) :=
  Data.Fin.casesDependent (.bottom (by decide +kernel))
    (Data.Fin.casesDependent (.left (by decide +kernel)) (fun index => Fin.elim0 index))

/-- The original opposite-root side has exact squared gap nine quarters. -/
theorem oppositeSide_margin (site : Fin 2) : (oppositeSide site).margin = 9 / 4 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The original reference power polynomial is exactly its retained two affine factors. -/
theorem sourcePolynomial_eq (site : Fin 2) :
    Polynomial.Power.Gaussian.rootPolynomial (seed site ^ 2) SquareRootDegree.degreeTwo =
      Dense.Gaussian.Linear.Translated.translatedCoordinate (seed site) *
        Dense.Gaussian.Linear.Translated.translatedCoordinate (-seed site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Construct the signed reference owner from the original two-factor polynomial and opposite-root exclusion.

Exact polynomial-index transport retains the split-pair owner's root box,
clearance and winding. The original reference root and its opposite remain
the two displayed affine factors of the same reference power polynomial.
-/
def sourceOwner (site : Fin 2) :
    Owner.Local.Basic.LocalOwner
      (Polynomial.Power.Gaussian.rootPolynomial (seed site ^ 2) SquareRootDegree.degreeTwo) :=
  Owner.Local.Transport.castOwner (sourcePolynomial_eq site).symm
    (Owner.Local.Basic.LocalOwner.ofSplitPair (seed site) (-seed site)
      (by decide +kernel : (0 : Rat.Fraction.Rational) < 1 / 2) (oppositeSide site))

/-- The signed reference owner retains its original half-radius root square. -/
theorem sourceOwner_box (site : Fin 2) : (sourceOwner site).box = box site := by
  unfold sourceOwner
  rewrite [Owner.Local.Transport.castOwner_box, Owner.Local.Basic.LocalOwner.ofSplitPair_box]
  rfl

/-- The original signed reference owner has the computed boundary clearance nine sixteenths. -/
theorem sourceOwner_bound (site : Fin 2) : (sourceOwner site).clearance.bound = 9 / 16 := by
  unfold sourceOwner
  rewrite [Owner.Local.Transport.castOwner_clearance_bound,
    Owner.Local.Basic.LocalOwner.ofSplitPair_clearance_bound]
  change (1 / 2 : Rat.Fraction.Rational) ^ 2 * (oppositeSide site).margin = 9 / 16
  rewrite [oppositeSide_margin site]
  decide +kernel

/-- Cofactor variation is exactly the original spatial displacement, with its retained orientation. -/
theorem displacement (site : Fin 2) (point : Canonical) :
    seed site ^ 2 - (unitPolynomial site).eval point = -(point - criticalValue site) := by
  rewrite [seed_square, unitPolynomial, Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
    Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
  ring1

/-- The whole original collision square bounds the cofactor parameter displacement by one half. -/
theorem variation_bound (site : Fin 2) {point : Canonical} (inside : (spatialBox site).Contains point) :
    Norm.Basic.normSq (seed site ^ 2 - (unitPolynomial site).eval point) ≤ 1 / 2 := by
  rewrite [displacement, Norm.Basic.normSq_neg]
  have lower := Box.Square.Centered.centeredSquare_normSq_sub_center_le (criticalValue site)
    (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 1 / 2) inside
  exact lower.trans (by decide +kernel)

/-- Every residual-certified original cofactor candidate on the spatial patch has squared norm at least one sixteenth.

The original polynomial's one-quarter clearance bounds the retained square
residual threshold. The existing constructive square-residual law then gives
the same positive candidate floor without selecting another root or sheet.
-/
theorem root_normSq_lower (site : Fin 2) {point root : Canonical} (inside : (spatialBox site).Contains point)
    (residual : Norm.Basic.normSq (root * root - (unitPolynomial site).eval point) ≤
      Riemann.Branches.SquareRootSheets.residualTarget ((unitPolynomial site).eval point)) :
    (1 / 16 : Rat.Fraction.Rational) ≤ Norm.Basic.normSq root := by
  have unitLower := unit_lower site inside
  have quarter : (1 / 16 : Rat.Fraction.Rational) ≤
      Riemann.Branches.SquareRootSheets.residualTarget ((unitPolynomial site).eval point) := by
    unfold Riemann.Branches.SquareRootSheets.residualTarget
    rewrite [← Norm.Basic.normSq_eq_canonical, Algebra.Field.ExplicitField.div_eq_mul_inv]
    exact (show (1 / 16 : Rat.Fraction.Rational) = (1 / 4) * (4 : Rat.Fraction.Rational)⁻¹ by decide +kernel).trans_le
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct unitLower (by decide +kernel))
  have sampleLower := Riemann.Branches.SquareRootSheets.normSq_lower_of_square_residual (by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact residual)
  rewrite [← Norm.Basic.normSq_eq_canonical] at sampleLower
  exact ((Order.Basic.le_min (by decide +kernel) quarter).trans
    (Order.Basic.le_max_left _ _)).trans sampleLower

/-- Two readings in the same original signed cofactor box have sum squared norm at least one.

At zero both imaginary coordinates are at least one half; at one both real
coordinates are at least one half. The original signed boxes thus select
compatible readings without identifying their owners or finite samples.
-/
theorem box_sum_lower (site : Fin 2) {first last : Canonical}
    (firstInside : (box site).Contains first) (lastInside : (box site).Contains last) :
    (1 : Rat.Fraction.Rational) ≤ Norm.Basic.normSq (first + last) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    have firstLower := firstInside.2.2.1
    have lastLower := lastInside.2.2.1
    rewrite [show (box 0).yLower = (1 / 2 : Rat.Fraction.Rational) by decide +kernel] at firstLower lastLower
    have sumLower : (1 : Rat.Fraction.Rational) ≤ first.im + last.im :=
      (show (1 : Rat.Fraction.Rational) = 1 / 2 + 1 / 2 by decide +kernel).trans_le
        (Order.Arithmetic.add_le_add_direct firstLower lastLower)
    have squared := Order.Arithmetic.pow_le_pow_direct (by decide +kernel) sumLower 2
    rewrite [one_pow] at squared
    change (1 : Rat.Fraction.Rational) ≤ (first.re + last.re) ^ 2 + (first.im + last.im) ^ 2
    exact squared.trans ((show (first.im + last.im) ^ 2 = 0 + (first.im + last.im) ^ 2 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (Order.Arithmetic.sq_nonneg_direct _)
        (Order.Basic.le_refl _)))
  · subst site
    have firstLower := firstInside.1
    have lastLower := lastInside.1
    rewrite [show (box 1).xLower = (1 / 2 : Rat.Fraction.Rational) by decide +kernel] at firstLower lastLower
    have sumLower : (1 : Rat.Fraction.Rational) ≤ first.re + last.re :=
      (show (1 : Rat.Fraction.Rational) = 1 / 2 + 1 / 2 by decide +kernel).trans_le
        (Order.Arithmetic.add_le_add_direct firstLower lastLower)
    have squared := Order.Arithmetic.pow_le_pow_direct (by decide +kernel) sumLower 2
    rewrite [one_pow] at squared
    change (1 : Rat.Fraction.Rational) ≤ (first.re + last.re) ^ 2 + (first.im + last.im) ^ 2
    exact squared.trans ((show (first.re + last.re) ^ 2 = (first.re + last.re) ^ 2 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
        (Order.Arithmetic.sq_nonneg_direct _)))

/-- Construct the original cofactor's signed root bridge everywhere on the retained collision square.

The internally derived whole-square variation bound is strictly below the
computed reference clearance. Generic power-parameter comparison therefore
retains both original cofactor readings on the same signed root square.
-/
def bridge (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    Owner.Bridge.Basic.OwnerBridge
      (Polynomial.Power.Gaussian.rootPolynomial (seed site ^ 2) SquareRootDegree.degreeTwo)
      (Polynomial.Power.Gaussian.rootPolynomial ((unitPolynomial site).eval point) SquareRootDegree.degreeTwo) :=
  Owner.Bridge.Basic.OwnerBridge.ofForward (sourceOwner site)
    (Progressive.Power.Owner.Transport.ownerMoveRouche SquareRootDegree.degreeTwo (sourceOwner site) (by
      rewrite [sourceOwner_bound]
      exact (variation_bound site inside).trans_lt (by decide +kernel)))

/-- Every cofactor bridge retains the same original signed reference-root square. -/
theorem bridge_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (bridge site point inside).box = box site := by
  unfold bridge
  exact (Owner.Bridge.Basic.OwnerBridge.ofForward_box _ _).trans (sourceOwner_box site)

-- Use the retained box laws instead of reducing the original polynomial-index
-- transport and its full Rouché calculation while checking dependent states.
attribute [local irreducible] sourceOwner bridge

/-- Retain the bridge's original target state at its proved signed ambient-box index.

Exact equality transport keeps the complete original state and its four
ambient-line certificates. The displayed box index avoids unfolding the
computed source-owner comparison while checking subsequent track interfaces.
-/
def initialState (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    State.WindingOne.Basic.WindingOneState
      (Polynomial.Power.Gaussian.rootPolynomial ((unitPolynomial site).eval point) SquareRootDegree.degreeTwo)
      (box site) :=
  State.WindingOne.Transport.castWindingOneState rfl (bridge_box site point inside)
    (bridge site point inside).rightOwner.initialState

/-- The reindexed target state has the same original signed root box. -/
theorem initialState_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (initialState site point inside).box = box site := by
  unfold initialState
  rewrite [State.WindingOne.Transport.castWindingOneState_box]
  exact bridge_box site point inside

/-- Construct an actual executable root owner of the original cofactor from its computed signed bridge.

The original cofactor nonvanishing and retained target state provide the
existing total quadratic track constructor. Its checked acceleration retains
the same initial state and the same selected root occurrence.
-/
def owner (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    SquareRootContinuationChain.Owner ((unitPolynomial site).eval point) :=
  SquareRootContinuationChain.Owner.ofState (unit_ne_zero site inside) (initialState site point inside)

/-- The actual cofactor-root owner retains its original signed root square as ambient. -/
theorem owner_ambient (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (owner site point inside).ambient = box site := by
  unfold owner
  exact SquareRootContinuationChain.Owner.ofState_ambient _ _

/-- Checked quadratic acceleration retains the same original signed root square as the track's initial box. -/
theorem owner_initial_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (owner site point inside).track.initial.box = box site := by
  unfold owner
  rewrite [SquareRootContinuationChain.Owner.ofState_initial]
  exact initialState_box site point inside

attribute [local irreducible] owner

/-- Every state of the same original cofactor track refines its signed reference-root square. -/
theorem owner_state_refines_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point)
    (index : Nat) : (CoherentRoot.state (owner site point inside).track index).box.Refines (box site) := by
  have nested := CoherentRoot.state_refines_of_le (owner site point inside).track (Nat.zero_le index)
  change (CoherentRoot.state (owner site point inside).track index).box.Refines
    (owner site point inside).track.initial.box at nested
  rewrite [owner_initial_box] at nested
  exact nested

/-- Every actual tailed root sample lies in the same original signed reference-root square. -/
theorem sample_contains_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point)
    (index : Nat) :
    (box site).Contains ((CertifiedSquareRoot.approximation (owner site point inside).track).sample index) := by
  rewrite [CertifiedSquareRoot.approximation_sample]
  exact (owner_state_refines_box site point inside _).contains
    (CoherentRoot.state _ _).box.contains_anchor

/-- Zero has a computed strict outside side on the original signed root square. -/
def zeroSide : (site : Fin 2) → (box site).OutsideSide 0 :=
  Data.Fin.casesDependent (.bottom (by decide +kernel))
    (Data.Fin.casesDependent (.left (by decide +kernel)) (fun index => Fin.elim0 index))

/-- The original zero-exclusion side has exact squared gap one quarter. -/
theorem zeroSide_margin (site : Fin 2) : (zeroSide site).margin = 1 / 4 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Every actual point in the retained signed cofactor square has quadrance at least one quarter. -/
theorem box_normSq_lower (site : Fin 2) {value : Canonical} (inside : (box site).Contains value) :
    (1 / 4 : Rat.Fraction.Rational) ≤ Norm.Basic.normSq value := by
  have bound := (zeroSide site).margin_le_normSq_sub inside
  rewrite [zeroSide_margin, Basic.sub_zero] at bound
  exact bound

/-- Every actual point in the original signed cofactor square has quadrance at most three.

The original half-radius square bounds displacement from the retained seed.
Its exact unit quadrance and the two-term norm estimate give this uniform
finite ceiling without selecting another root or replacing the sample.
-/
theorem box_normSq_upper (site : Fin 2) {value : Canonical} (inside : (box site).Contains value) :
    Norm.Basic.normSq value ≤ (3 : Rat.Fraction.Rational) := by
  have movement := Box.Square.Centered.centeredSquare_normSq_sub_center_le (seed site)
    (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 1 / 2) inside
  have seedNorm : Norm.Basic.normSq (seed site) = (1 : Rat.Fraction.Rational) := by
    rcases Fin.Two.finTwo_cases site with zero | one
    · subst site
      decide +kernel
    · subst site
      decide +kernel
  have identity : value = seed site + (value - seed site) := by ring1
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct seedNorm.le movement)
      (by decide +kernel)).trans_eq (by decide +kernel))

/-- Every actual cofactor-root sample has the same uniform positive squared-norm bound on the whole collision patch.

The bound follows from the retained signed root square and its original
zero-exclusion side. It applies at every tailed sample index of the same
track, with no independently selected roots or supplied sample inequalities.
-/
theorem sample_lower (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) (index : Nat) :
    (1 / 4 : Rat.Fraction.Rational) ≤
      Norm.Basic.normSq ((CertifiedSquareRoot.approximation (owner site point inside).track).sample index) := by
  have lower := (zeroSide site).margin_le_normSq_sub (sample_contains_box site point inside index)
  rewrite [zeroSide_margin, Gaussian.Basic.sub_zero] at lower
  exact lower

end Purelib.Curves.Legendre.Degeneration.UnitRoot
