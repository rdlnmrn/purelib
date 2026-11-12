module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Factorization
public import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original odd-power differential pullbacks on the regular parallel circle

The original radial tangent cancels one normalized-ordinate reciprocal factor.
Every original odd-power differential therefore has a pullback constructed
from the actual cached cofactor channel and exact remaining ordinate powers.
The independently retained ordinary full-ordinate preparation gives an
operational comparison to this construction. Value, cubic and quintic forms
retain their original numerator, scale, quarter, parameter and lift owners.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter} {time : Fraction.Rational}
variable {positive : (0 : Fraction.Rational) < 2}
variable {unit : Owner ((unitPolynomial site).eval
  (point site parameter 2 (Waist.direction quarter time) positive).base)}

/-- Construct the original parallel pullback using the identical supplied cofactor channel and exact ordinate powers. -/
@[expose] def value (differential : OddPowerDifferential radicand)
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit) : CoherentNamed :=
  differential.factorizedValue
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
    actual.unitRoot.value actual.unitRoot.apart
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate
    (Stereographic.Tangent.logarithmicVelocity time)

/-- The ordinary original differential on the same prepared cubic lift and its actual tangent agrees with the pullback.

Intrinsic regularity derives the original normalized-ordinate nonzero
certificate. Existing preparation keeps its original full cubic product,
and the general exact-factor law compares the two actual process trees.
-/
def value_agrees (differential : OddPowerDifferential radicand) (regular : parameter ≠ criticalValue site)
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit)
    (prepared : Approximation.Gaussian.Division.Prepared actual.value) :
    NamedEquivalent ((differential.value
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
      prepared.denominator prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))).name
      (value differential actual).name := by
  rewrite [Tangent.baseVelocity_eq_ordinate_mul site parameter 2 quarter (by decide +kernel) time]
  exact differential.value_factorized
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
    actual.value actual.unitRoot.value prepared
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) actual.value_eq
    (parallel_ordinate_ne_zero site parameter (Waist.direction quarter time) regular) actual.unitRoot.apart

/-- The exact coefficient formula on one displayed cofactor reading at the same original parallel point.

This is a scalar coefficient, distinct from any independently refined
arithmetic-process witness. An observation attachment must pay the difference
between its original witnesses and this displayed reading.
-/
@[expose] def reading (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) (differential : OddPowerDifferential radicand) (root : Canonical) : Canonical :=
  differential.scale * differential.numerator.eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base *
      Stereographic.Tangent.logarithmicVelocity time *
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate⁻¹ ^
        (2 * differential.denominatorPairs) * root⁻¹ ^ differential.denominatorExponent

/-- The exact numerator and remaining ordinate factor of one original parallel differential channel. -/
@[expose] def coefficient (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) (differential : OddPowerDifferential radicand) : Canonical :=
  differential.scale * differential.numerator.eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base *
      Stereographic.Tangent.logarithmicVelocity time *
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate⁻¹ ^
        (2 * differential.denominatorPairs)

set_option genInjectivity false in
/-- A materialized differential bank on one original parallel lift, sharing its actual cofactor reciprocal.

The original finite specification table and complete lift remain indices.
The reciprocal is constructed once. The finite power and channel vectors
store their actual names, and entry readbacks consume these same caches.
-/
structure Bank {count : Nat} (forms : Data.Vector (OddPowerDifferential radicand) count)
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit) where
  /-- The retained reciprocal of the identical original cofactor channel. -/
  reciprocal : CoherentNamed
  /-- The reciprocal cache is the complete original source construction. -/
  reciprocal_eq : reciprocal = (Coherence.exact 1).div actual.unitRoot.value actual.unitRoot.apart
  /-- The actual finite power names computed from that same cached reciprocal. -/
  powers : Data.Vector CoherentNamed count
  /-- Every cached power uses its original specification's odd denominator exponent. -/
  powers_eq : ∀ coordinate, powers coordinate =
    Approximation.Gaussian.Name.Coherent.Power.namedPower reciprocal (forms coordinate).denominatorExponent
  /-- The materialized original differential channels, retaining the same cached powers. -/
  channels : Data.Vector CoherentNamed count
  /-- Each channel reads the original exact coefficient and its identical cached power. -/
  channels_eq : ∀ coordinate, channels coordinate =
    (Coherence.exact (coefficient site parameter quarter time (forms coordinate))).mul (powers coordinate)

constructive_injectivity Bank

namespace Bank

variable {count : Nat} {forms : Data.Vector (OddPowerDifferential radicand) count}
variable {actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit}

/-- Construct the original reciprocal once and materialize its finite power and differential-channel caches. -/
@[expose] def build (forms : Data.Vector (OddPowerDifferential radicand) count)
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit) : Bank forms actual :=
  let reciprocal := (Coherence.exact 1).div actual.unitRoot.value actual.unitRoot.apart
  let powers := Data.Vector.Basic.vectorOfFn (fun coordinate =>
    Approximation.Gaussian.Name.Coherent.Power.namedPower reciprocal (forms coordinate).denominatorExponent)
  let channels := Data.Vector.Basic.vectorOfFn (fun coordinate =>
    (Coherence.exact (coefficient site parameter quarter time (forms coordinate))).mul (powers coordinate))
  { reciprocal := reciprocal
    reciprocal_eq := rfl
    powers := powers
    powers_eq := fun coordinate => Data.Vector.Basic.vectorOfFn_apply _ coordinate
    channels := channels
    channels_eq := fun coordinate => Data.Vector.Basic.vectorOfFn_apply _ coordinate }

/-- Each actual bank entry is the complete original parallel pullback construction for its retained specification. -/
theorem channel_eq_value (bank : Bank forms actual) (coordinate : Fin count) :
    bank.channels coordinate = value (forms coordinate) actual := by
  rewrite [bank.channels_eq coordinate, bank.powers_eq coordinate, bank.reciprocal_eq]
  rfl

/-- The retained denominator preparation compares its ordinary differential and tangent to the cached bank entry. -/
def agrees (bank : Bank forms actual) (coordinate : Fin count) (regular : parameter ≠ criticalValue site)
    (prepared : Approximation.Gaussian.Division.Prepared actual.value) :
    NamedEquivalent (((forms coordinate).value
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
      prepared.denominator prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))).name
      (bank.channels coordinate).name :=
  NamedEquivalent.transport rfl
    (congrArg (fun channel : CoherentNamed => channel.name) (bank.channel_eq_value coordinate).symm)
    (value_agrees (forms coordinate) regular actual prepared)

end Bank

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
