module

import Purelib.Curves.Legendre.Degeneration
import Purelib.Curves.Legendre.Degeneration.Coordinates
import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Cells
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Curves.Legendre.Paths
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Derivative

/-! # Original Legendre nodal factors, patch owners and quadratic smoothing winding -/

namespace TestPurelib.Curves.Legendre.Degeneration

open Purelib
open Purelib.Curves.Legendre
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre.Periods.Jets.Specification
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

/-- Every local factorization reads the original cubic and the same original ordered branch labels. -/
example (site : Fin 2) (parameter point : Canonical) :
    (Paths.polynomial parameter).eval point =
      (Degeneration.coordinate site parameter point ^ 2 - Degeneration.smoothing site parameter) *
        (Degeneration.unitPolynomial site).eval point ∧
      Degeneration.center site parameter - Degeneration.halfGap site parameter =
        Paths.branchPoint parameter (Degeneration.fixedLabel site) ∧
      Degeneration.center site parameter + Degeneration.halfGap site parameter = Paths.branchPoint parameter 1 :=
  ⟨Degeneration.polynomial_centered site parameter point, Degeneration.center_sub_halfGap site parameter,
    Degeneration.center_add_halfGap site parameter⟩

/-- The full retained spatial patch has a computed unit bound and no third-root pole. -/
example (site : Fin 2) {point : Canonical} (inside : (Degeneration.spatialBox site).Contains point) :
    (1 / 4 : Data.Rat.Fraction.Rational) ≤ Norm.Basic.normSq ((Degeneration.unitPolynomial site).eval point) ∧
      (Degeneration.unitPolynomial site).eval point ≠ 0 :=
  ⟨Degeneration.unit_lower site inside, Degeneration.unit_ne_zero site inside⟩

/-- Patch preparation retains the original polynomial and both actual collision-root owners. -/
example (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ Degeneration.criticalValue site)
    (inside : (Degeneration.parameterBox site).Contains parameter) :
    let frame := Degeneration.frameOnPatch site parameter regular inside
    frame.chamber.polynomial = Paths.polynomial parameter ∧
      (frame.chamber.owner (frame.labels.forward (Degeneration.fixedLabel site))).box.Contains
        (Degeneration.criticalValue site) ∧
      (frame.chamber.owner (frame.labels.forward 1)).box.Contains parameter := by
  intro frame
  have fixed := frame.owner_contains (Degeneration.fixedLabel site)
  rewrite [← Degeneration.criticalValue_eq_branchPoint site parameter] at fixed
  have moving := frame.owner_contains 1
  rewrite [Paths.branchPoint_one] at moving
  exact ⟨frame.polynomial_eq, fixed, moving⟩

/-- Every admitted patch parameter puts the same original moving root strictly inside the spatial patch. -/
example (site : Fin 2) {parameter : Canonical} (inside : (Degeneration.parameterBox site).Contains parameter) :
    (Degeneration.spatialBox site).StrictContains parameter ∧ parameter ≠ Degeneration.remainingValue site :=
  ⟨Degeneration.moving_strictContains site inside, Degeneration.parameter_ne_remaining site inside⟩

/-- The original dense derivative algorithm certifies each selected critical fibre's double root. -/
example (site : Fin 2) :
    (Paths.polynomial (Degeneration.criticalValue site)).eval (Degeneration.criticalValue site) = 0 ∧
      (Polynomial.Dense.Derivative.derivative
        (Paths.polynomial (Degeneration.criticalValue site))).eval (Degeneration.criticalValue site) = 0 ∧
      (Polynomial.Dense.Derivative.derivative (Polynomial.Dense.Derivative.derivative
        (Paths.polynomial (Degeneration.criticalValue site)))).eval (Degeneration.criticalValue site) ≠ 0 :=
  Degeneration.critical_fibre_node site

/-- Both labelled parameter families have the retained nontransverse finite-variation identity. -/
example (site : Fin 2) (increment : Canonical) :
    (Paths.polynomial (Degeneration.criticalValue site + increment)).eval (Degeneration.criticalValue site) =
      (Paths.polynomial (Degeneration.criticalValue site)).eval (Degeneration.criticalValue site) :=
  Degeneration.parameter_variation_at_node site increment

/-- The remaining original branch stays simple on the selected critical fibre. -/
example (site : Fin 2) :
    (Paths.polynomial (Degeneration.criticalValue site)).eval (Degeneration.remainingValue site) = 0 ∧
      (Polynomial.Dense.Derivative.derivative (Paths.polynomial (Degeneration.criticalValue site))).eval
        (Degeneration.remainingValue site) ≠ 0 := Degeneration.remaining_fibre_simple site

/-- The same computed positive-square smoothing program has winding two, for either original critical value. -/
example (site : Fin 2) {radius : Data.Rat.Fraction.Rational} (positive : 0 < radius) :
    Polynomial.Winding.Box.Basic.boxWinding (Degeneration.smoothingPolynomial site)
      (Box.Square.Centered.Affine.centeredSquare (Degeneration.criticalValue site) radius positive.le) = 2 :=
  Degeneration.smoothing_winding site positive

/-- At zero the computed squared half-gap is the exact imaginary Gaussian one over 128. -/
example : Degeneration.smoothing 0 (⟨1 / 8, 1 / 8⟩ : Canonical) = (⟨0, 1 / 128⟩ : Canonical) := by
  decide +kernel

/-- At one the same retained displacement has the same exact smoothing reading. -/
example : Degeneration.smoothing 1 (⟨9 / 8, 1 / 8⟩ : Canonical) = (⟨0, 1 / 128⟩ : Canonical) := by
  decide +kernel

/-- The actual coordinate constructor retains both complete original owners, including the chosen cubic sheet. -/
example (site : Fin 2) (parameter point : Canonical) (inside : (Degeneration.spatialBox site).Contains point)
    (source : Owner ((Paths.polynomial parameter).eval point)) :
    let actual := Degeneration.Coordinates.build site parameter point inside source
    actual.sourceOwner = source ∧ actual.unitOwner = Degeneration.UnitRoot.owner site point inside :=
  ⟨(Degeneration.Coordinates.build site parameter point inside source).sourceOwner_eq,
    (Degeneration.Coordinates.build site parameter point inside source).unitOwner_eq⟩

/-- Original cubic and cofactor owners internally construct conic coordinates with the computed smoothing product. -/
example (site : Fin 2) (parameter point : Canonical) (inside : (Degeneration.spatialBox site).Contains point)
    (source : Owner ((Paths.polynomial parameter).eval point)) :
    let actual := Degeneration.Coordinates.build site parameter point inside source
    NamedEquivalent (actual.plus.mul actual.minus).name (Named.exact (Degeneration.smoothing site parameter)) :=
  (Degeneration.Coordinates.build site parameter point inside source).product

/-- A transported cofactor and its independent endpoint reading give agreeing actual normalized ordinate programs. -/
example {site : Fin 2} (parameter first last : Canonical)
    (path : Degeneration.UnitRoot.PreparedTransport.Path site first last) (within : path.WithinAmbient)
    (inside : (Degeneration.spatialBox site).Contains first)
    (traced : TracedPath path (Degeneration.UnitRoot.owner site first inside))
    (source : Owner ((Paths.polynomial parameter).eval last)) :
    let transported := Degeneration.Coordinates.ofOwners site parameter last source traced.finishOwner
    let independent := Degeneration.Coordinates.build site parameter last
      (Degeneration.UnitRoot.PreparedTransport.path_finish_inside path within inside) source
    NamedEquivalent transported.ordinate.name independent.ordinate.name :=
  Degeneration.Coordinates.path_ordinate_agrees path within inside traced source
    (Degeneration.Coordinates.ofOwners site parameter last source traced.finishOwner)
    (Degeneration.Coordinates.build site parameter last
      (Degeneration.UnitRoot.PreparedTransport.path_finish_inside path within inside) source)

/-- The original fixed branch constructs its zero ordinate internally and recovers the original base coordinate. -/
example (site : Fin 2) (parameter : Canonical) :
    let actual := Degeneration.CoordinateChannels.atFixed site parameter
    NamedEquivalent actual.ordinate.name (Named.exact 0) ×
      NamedEquivalent actual.readPoint.name (Named.exact (Degeneration.criticalValue site)) :=
  ⟨(Degeneration.CoordinateChannels.atFixed site parameter).ordinate_zero,
    (Degeneration.CoordinateChannels.atFixed site parameter).readPoint_agrees⟩

/-- The admitted original moving branch, including the critical parameter, has actual conic and ordinate recovery. -/
example (site : Fin 2) (parameter : Canonical) (inside : (Degeneration.parameterBox site).Contains parameter) :
    let actual := Degeneration.CoordinateChannels.atMoving site parameter inside
    NamedEquivalent (actual.plus.mul actual.minus).name (Named.exact (Degeneration.smoothing site parameter)) ×
      NamedEquivalent actual.readOrdinate.name (Named.exact 0) :=
  ⟨(Degeneration.CoordinateChannels.atMoving site parameter inside).product,
    (Degeneration.CoordinateChannels.atMoving site parameter inside).readOrdinate_agrees⟩

/-- Original owner-based coordinate caches recover the same original cubic sheet's actual numerical channel. -/
example (site : Fin 2) (parameter point : Canonical) (inside : (Degeneration.spatialBox site).Contains point)
    (source : Owner ((Paths.polynomial parameter).eval point)) :
    let actual := Degeneration.Coordinates.build site parameter point inside source
    NamedEquivalent actual.toChannels.readPoint.name (Named.exact point) ×
      NamedEquivalent actual.toChannels.readOrdinate.name actual.sourceRoot.value.name :=
  ⟨(Degeneration.Coordinates.build site parameter point inside source).toChannels.readPoint_agrees,
    (Degeneration.Coordinates.build site parameter point inside source).toChannels.readOrdinate_agrees⟩

/-- Bounded conic inputs construct the original cubic ordinate and recover both original inputs operationally. -/
example (site : Fin 2) (parameter : Canonical) (point : Degeneration.Conic.Point site parameter)
    (parameterInside : (Degeneration.parameterBox site).Contains parameter)
    (plusInside : Degeneration.Conic.coordinateBox.Contains point.plus)
    (minusInside : Degeneration.Conic.coordinateBox.Contains point.minus) :
    let lift := Degeneration.Conic.Lift.onPatch point parameterInside plusInside minusInside
    NamedEquivalent (lift.value.mul lift.value).name (Named.exact ((Paths.polynomial parameter).eval point.base)) ×
      NamedEquivalent lift.coordinates.plus.name (Named.exact point.plus) ×
      NamedEquivalent lift.coordinates.minus.name (Named.exact point.minus) := by
  intro lift
  exact ⟨lift.square, lift.plus_agrees, lift.minus_agrees⟩

/-- Forward reconstruction retains the exact original signed cofactor owner and full certificate cached by the lift. -/
example (site : Fin 2) (parameter : Canonical) (point : Degeneration.Conic.Point site parameter)
    (parameterInside : (Degeneration.parameterBox site).Contains parameter)
    (plusInside : Degeneration.Conic.coordinateBox.Contains point.plus)
    (minusInside : Degeneration.Conic.coordinateBox.Contains point.minus) :
    let inside := point.base_inside parameterInside plusInside minusInside
    let lift := Degeneration.Conic.Lift.onPatch point parameterInside plusInside minusInside
    lift.unitOwner = Degeneration.UnitRoot.owner site point.base inside ∧
      lift.coordinates.unitRoot = lift.unitRoot := by
  intro inside lift
  exact ⟨lift.unitOwner_eq, lift.coordinates_unitRoot⟩

/-- Independently constructed exchanged lifts compare their actual cubic channels using the same original cofactor. -/
example (site : Fin 2) (parameter : Canonical) (point : Degeneration.Conic.Point site parameter)
    (parameterInside : (Degeneration.parameterBox site).Contains parameter)
    (plusInside : Degeneration.Conic.coordinateBox.Contains point.plus)
    (minusInside : Degeneration.Conic.coordinateBox.Contains point.minus) :
    let original := Degeneration.Conic.Lift.onPatch point parameterInside plusInside minusInside
    let exchanged := Degeneration.Conic.Lift.onPatch point.exchange parameterInside minusInside plusInside
    NamedEquivalent exchanged.value.name original.value.neg.name := by
  intro original exchanged
  exact Degeneration.Conic.Lift.exchange_patch_agrees original exchanged

/-- A rational waist quarter derives actual cubic channels and exact forward readback from intrinsic parameter data. -/
example (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) (time : Data.Rat.Fraction.Rational)
    (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational)) :
    let actual := Waist.lift site parameter (Waist.direction quarter time) regular bound
    NamedEquivalent (actual.value.mul actual.value).name
      (Named.exact ((Paths.polynomial parameter).eval (Waist.point site parameter
        (Waist.direction quarter time) regular bound).base)) ×
      NamedEquivalent actual.coordinates.plus.name
        (Named.exact (Waist.coordinate site parameter (Waist.direction quarter time))) := by
  intro actual
  exact ⟨actual.square, NamedEquivalent.transport rfl
    (congrArg Named.exact (Waist.point_plus _ _ _ regular bound)) actual.plus_agrees⟩

/-- The zero collision's computed annulus has the displayed positive inner and outer squared radii. -/
example : Degeneration.Conic.Annulus.innerRadiusSq 0 (1 / 8) = 1 / 1024 ∧
    Degeneration.Conic.Annulus.outerRadiusSq = 1 / 64 := by
  decide +kernel

/-- The same labelled displacement at the one collision has the same original computed annulus radii. -/
example : Degeneration.Conic.Annulus.innerRadiusSq 1 (9 / 8) = 1 / 1024 ∧
    Degeneration.Conic.Annulus.outerRadiusSq = 1 / 64 := by
  decide +kernel

/-- Whole-quarter cofactor preparation constructs actual cubic channels and independent endpoint agreement. -/
example (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational)) :
    let actual := Waist.Transport.Quarter.build site parameter quarter regular bound
    NamedEquivalent (actual.finishLift.value.mul actual.finishLift.value).name
      (Named.exact ((Paths.polynomial parameter).eval
        (Waist.point site parameter (Waist.direction quarter 1) regular bound).base)) ×
      NamedEquivalent actual.finishLift.value.name
        (Waist.lift site parameter (Waist.direction quarter 1) regular bound).value.name := by
  intro actual
  exact ⟨actual.finishLift.square, actual.finishLift_agrees⟩

/-- Actual transported quarter lifts give both original value-row pullbacks with independent endpoint agreement. -/
example (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) (coordinate : Fin 2)
    (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational)) :
    let actual := Waist.Transport.Quarter.build site parameter quarter regular bound
    let transported := actual.finishLift
    let independent := Waist.lift site parameter (Waist.direction quarter 1) regular bound
    let differential := valueSpecification parameter coordinate
    let simple := valueSpecification_denominatorPairs parameter coordinate
    NamedEquivalent (Waist.Differential.value differential simple transported).name
      (Waist.Differential.value differential simple independent).name ×
      NamedEquivalent (transported.value.mul
        (Waist.Differential.value differential simple transported)).name
        (Named.exact (differential.scale * differential.numerator.eval
          (Waist.point site parameter (Waist.direction quarter 1) regular bound).base *
            Waist.Tangent.baseVelocity site parameter quarter 1)) := by
  intro actual transported independent differential simple
  have cofactor : NamedEquivalent transported.unitRoot.value.name independent.unitRoot.value.name :=
    NamedEquivalent.transport transported.unitRoot_name.symm independent.unitRoot_name.symm
      actual.finishUnit_agrees
  exact ⟨Waist.Differential.value_respects differential simple transported independent cofactor,
    Waist.Differential.value_cleared differential simple transported⟩

/-- Each original value-row evaluator on an apart cubic sheet agrees with the same waist pullback and tangent. -/
example (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) (coordinate : Fin 2)
    (time : Data.Rat.Fraction.Rational) (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational))
    (apart : Named.Apart (Waist.lift site parameter (Waist.direction quarter time) regular bound).value.name) :
    let actual := Waist.lift site parameter (Waist.direction quarter time) regular bound
    NamedEquivalent (((valueSpecification parameter coordinate).value
      (Waist.point site parameter (Waist.direction quarter time) regular bound).base actual.value apart).mul
        (Coherence.exact (Waist.Tangent.baseVelocity site parameter quarter time))).name
      (Waist.Differential.value (valueSpecification parameter coordinate)
        (valueSpecification_denominatorPairs parameter coordinate) actual).name := by
  intro actual
  exact Waist.Differential.value_agrees _ _ actual apart

/-- Both original value rows construct an actual pullback at the original moving branch without ordinate apartness. -/
example (site : Fin 2) (parameter : Canonical) (coordinate : Fin 2)
    (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational)) :
    let actual := Waist.lift site parameter (Waist.direction .first 0) regular bound
    PProd ((Waist.point site parameter (Waist.direction .first 0) regular bound).base = Paths.branchPoint parameter 1)
      (NamedEquivalent (actual.value.mul (Waist.Differential.value (valueSpecification parameter coordinate)
        (valueSpecification_denominatorPairs parameter coordinate) actual)).name (Named.exact 0)) := by
  intro actual
  have branch := Waist.point_first_start site parameter regular bound
  have velocity : Waist.Tangent.baseVelocity site parameter .first 0 = 0 := by
    rewrite [Waist.Tangent.baseVelocity_eq_ordinate_mul site parameter .first regular bound 0, branch.2,
      Basic.zero_mul]
    rfl
  have cleared := Waist.Differential.value_cleared (valueSpecification parameter coordinate)
    (valueSpecification_denominatorPairs parameter coordinate) actual
  rewrite [velocity, Basic.mul_zero] at cleared
  exact ⟨branch.1, cleared⟩

/-- Both original differential rows construct a sampled integration cell starting at the actual moving branch. -/
example (site : Fin 2) (parameter : Canonical) (coordinate : Fin 2)
    (regular : parameter ≠ Degeneration.criticalValue site)
    (bound : Norm.Basic.normSq (parameter - Degeneration.criticalValue site) ≤ (1 / 16 : Data.Rat.Fraction.Rational)) :
    let differential := valueSpecification parameter coordinate
    let budget := Waist.Differential.Bounds.Data.build site parameter differential
    let span : Data.Rat.Interval.Bounds := ⟨0, 1, by decide +kernel⟩
    let lift := Waist.lift site parameter (Waist.direction .first span.lower) regular bound
    let actual := Waist.Differential.Cells.Model.build budget
      (valueSpecification_denominatorPairs parameter coordinate) lift 0
    (Waist.point site parameter (Waist.direction .first span.lower) regular bound).base =
      Paths.branchPoint parameter 1 ∧
      actual.cell.integralSample = (⟨span.upper - span.lower, 0⟩ : Canonical) * actual.center ∧
      (1 / 16 : Data.Rat.Fraction.Rational) ≤ Norm.Basic.normSq actual.centerRoot := by
  intro differential budget span lift actual
  exact ⟨(Waist.point_first_start site parameter regular bound).1, actual.integralSample,
    Degeneration.UnitRoot.root_normSq_lower site
      (Waist.point_inside site parameter (Waist.direction .first span.lower) regular bound) actual.centerResidual⟩

end TestPurelib.Curves.Legendre.Degeneration
