module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition
public import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Distance
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Quadrature
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Neighboring target-window evidence on original constructed layers

The actual layerAt midpoint chain makes source-time separation an original
span width. Its finite depth bound pays normalized-center displacement into
the same cached anchor windows. Every candidate of both original normalized
target processes then retains a common positive sum floor. This is local
window evidence, separate from constructing a target continuation path.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {radicand : CoefficientPolynomial}

variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

/-- A complete original quarter containment bounds its retained initial span width squared by one. -/
private theorem initial_width_sq_le_one (initial : Radial.Differential.Refinement.Piece data actual accuracy) :
    initial.span.width ^ 2 ≤ 1 := by
  have first := initial.within initial.span.lower ⟨Fraction.Order.Basic.le_refl _, initial.span.valid⟩
  have last := initial.within initial.span.upper ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩
  let unit : Interval.Bounds := ⟨0, 1, by decide +kernel⟩
  have bounded := Interval.parameter_sub_sq_le_width_sq unit last first
  have unitWidth : unit.width = 1 := by
    change (1 : Fraction.Rational) - 0 = 1
    ring1
  rewrite [unitWidth] at bounded
  rewrite [one_pow] at bounded
  exact bounded

/-- At depth at least eight, every original retained layer span has squared width at most one over 65536. -/
theorem span_width_sq_le (initial : Radial.Differential.Refinement.Piece data actual accuracy)
    (depth : Nat) (depthBound : 8 ≤ depth) (node : Fin (initial.layerAt depth).pieces.length) :
    ((initial.layerAt depth).node node).span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536 := by
  have member : (initial.layerAt depth).node node ∈ (initial.layerAt depth).pieces := List.getElem_mem node.isLt
  have eight : Geometric.Basic.quarterRadius (1 : Fraction.Rational) 8 = 1 / Fraction.Cast.fromInt 65536 := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Fraction.Field.one_mul]
    decide +kernel
  rewrite [(initial.layerAt depth).widths _ member]
  exact ((Geometric.Basic.quarterRadius_scale_mono (initial_width_sq_le_one initial) depth).trans
    (Geometric.Basic.quarterRadius_antitone (by decide +kernel) depthBound)).trans_eq eight

/-- Consecutive original layer nodes differ in chart time by the exact retained first span width. -/
private theorem node_step_width (initial : Radial.Differential.Refinement.Piece data actual accuracy)
    (depth : Nat) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) :
    ((initial.layerAt depth).node last).span.lower - ((initial.layerAt depth).node first).span.lower =
      ((initial.layerAt depth).node first).span.width := by
  cases last with
  | mk index bound =>
      cases next
      exact initial.layerAt_step_width depth first.val first.isLt bound

/-- The same constructed neighboring source ordinates are close within their retained source anchor radius.

The original midpoint seams and depth pay the normalized ellipse displacement.
The actual source anchor's geometric radius lower bound supplies the same budget.
-/
theorem ordinate_near (initial : Radial.Differential.Refinement.Piece data actual accuracy)
    (depth : Nat) (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1)
    (anchor : Radial.Parameter.Anchor ((initial.layerAt depth).node first).source.lift) :
    Norm.Basic.normSq
      ((Radial.Parameter.sourcePoint site parameter
          (Waist.direction quarter ((initial.layerAt depth).node last).span.lower)).ordinate -
        (Radial.Parameter.sourcePoint site parameter
          (Waist.direction quarter ((initial.layerAt depth).node first).span.lower)).ordinate) ≤
      anchor.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256 := by
  apply anchor.ordinate_near
  rewrite [node_step_width initial depth first last next]
  exact span_width_sq_le initial depth depthBound first

namespace Samples

variable {initial : Radial.Differential.Refinement.Piece data actual accuracy} {depth : Nat}
variable {regular : parameter ≠ criticalValue site}
variable {admitted : Radial.Parameter.IncrementBound site parameter increment} {nonzero : increment ≠ 0}

/-- Every neighboring original normalized target candidate pair has a common cached source-radius sum floor.

The retained steps place their candidates in the two original anchor windows.
Internally bounded center displacement pays the cross-window sum certificate;
no root is re-isolated and neither selected state or source owner is replaced.
-/
theorem target_neighbor_sum (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) {left right : Canonical}
    {leftState : (samples.steps.get first).val.root.value.name.process.State}
    {rightState : (samples.steps.get last).val.root.value.name.process.State}
    (leftPossible : (samples.steps.get first).val.root.value.name.process.Possible leftState left)
    (rightPossible : (samples.steps.get last).val.root.value.name.process.Possible rightState right) :
    (samples.anchors.get first).val.seed.separation.radius ^ 2 ≤ Norm.Basic.normSq (left + right) :=
  ((samples.anchors.get first).val.seed.separation).near_sum_normSq_lower
    (samples.anchors.get last).val.seed.separation
    (ordinate_near initial depth depthBound first last next (samples.anchors.get first).val)
    ((samples.steps.get first).val.target_candidate_inside leftPossible)
    ((samples.steps.get last).val.target_candidate_inside rightPossible)

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

end
