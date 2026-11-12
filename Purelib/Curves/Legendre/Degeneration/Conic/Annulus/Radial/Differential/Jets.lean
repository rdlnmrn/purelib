module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Six original differential pullbacks on one retained parallel lift

One materialized bank shares the actual original cofactor reciprocal across
both value rows and all four derivative rows. Each projection consumes that
same cache and compares to its original ordinary evaluator with the supplied
full cubic preparation and the actual oriented tangent. These are pointwise
channels; productive period derivatives require integral remainder evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Jets

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter} {time : Fraction.Rational}
variable {positive : (0 : Fraction.Rational) < 2}
variable {unit : Owner ((unitPolynomial site).eval
  (point site parameter 2 (Waist.direction quarter time) positive).base)}

/-- The original six-specification bank indexed by the identical complete original parallel lift. -/
abbrev Bank
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit) :=
  Differential.Bank (Specification.Table.forms parameter) actual

/-- Construct all six original channels with one retained cofactor reciprocal and materialized power caches. -/
@[expose] def build
    (actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit) : Bank actual :=
  Differential.Bank.build (Specification.Table.forms parameter) actual

variable {actual : Lift (point site parameter 2 (Waist.direction quarter time) positive) unit}

/-- Read the actual cached original value channel at its retained differential coordinate. -/
@[expose] def value (bank : Bank actual) (coordinate : Fin 2) : CoherentNamed :=
  bank.channels (Specification.Table.valueIndex coordinate)

/-- Read the actual cached original first derivative channel at its retained differential coordinate. -/
@[expose] def first (bank : Bank actual) (coordinate : Fin 2) : CoherentNamed :=
  bank.channels (Specification.Table.firstIndex coordinate)

/-- Read the actual cached original second derivative channel at its retained differential coordinate. -/
@[expose] def second (bank : Bank actual) (coordinate : Fin 2) : CoherentNamed :=
  bank.channels (Specification.Table.secondIndex coordinate)

/-- The retained ordinary value differential and actual tangent agree with the same bank's value channel. -/
def value_agrees (bank : Bank actual) (coordinate : Fin 2) (regular : parameter ≠ criticalValue site)
    (prepared : Approximation.Gaussian.Division.Prepared actual.value) :
    NamedEquivalent (((Specification.valueSpecification parameter coordinate).value
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
      prepared.denominator prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))).name
      (value bank coordinate).name := by
  have result := bank.agrees (Specification.Table.valueIndex coordinate) regular prepared
  rewrite [Specification.Table.forms_value parameter coordinate] at result
  exact result

/-- The original ordinary first derivative and actual tangent agree with the identical bank's first channel. -/
def first_agrees (bank : Bank actual) (coordinate : Fin 2) (regular : parameter ≠ criticalValue site)
    (prepared : Approximation.Gaussian.Division.Prepared actual.value) :
    NamedEquivalent (((Specification.firstDerivativeSpecification parameter coordinate).value
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
      prepared.denominator prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))).name
      (first bank coordinate).name := by
  have result := bank.agrees (Specification.Table.firstIndex coordinate) regular prepared
  rewrite [Specification.Table.forms_first parameter coordinate] at result
  exact result

/-- The original ordinary second derivative and actual tangent agree with the identical bank's second channel. -/
def second_agrees (bank : Bank actual) (coordinate : Fin 2) (regular : parameter ≠ criticalValue site)
    (prepared : Approximation.Gaussian.Division.Prepared actual.value) :
    NamedEquivalent (((Specification.secondDerivativeSpecification parameter coordinate).value
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base
      prepared.denominator prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))).name
      (second bank coordinate).name := by
  have result := bank.agrees (Specification.Table.secondIndex coordinate) regular prepared
  rewrite [Specification.Table.forms_second parameter coordinate] at result
  exact result

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Jets
