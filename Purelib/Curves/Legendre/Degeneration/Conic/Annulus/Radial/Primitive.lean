module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Factorization
public import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Original primitive coefficient caches on a retained radial reading

The original full-sheet preparation supports both the primitive's productive
reciprocal-power evaluator and its cached reduced coefficient interpretation.
An uncancelled exact-factor specialization retains the original cofactor
channel and complete odd ordinate power. Both comparisons concern actual
arithmetic process trees on the same original lift.

The displayed scalar endpoint formula is independently prescribed at an
actual cofactor reading. It is not an arithmetic-process witness; attaching
such a witness requires a separately paid finite observation comparison.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

/-- Transport the original cubic square identity to the identical retained prepared denominator.

The original lift and its actual preparation remain independent owners.
The original finite-power transport consumes their retained operational
comparison without changing the polynomial, selected sheet or sampler starts.
-/
def squareIdentity (reading : Transport.Reading actual time inside) (prepared : Division.Prepared reading.lift.value) :
    PowerIdentity prepared.denominator 2
      ((Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter time) positive).base) :=
  PowerIdentity.transport (PowerIdentity.ofSquare reading.lift.square) prepared.equivalent.symm

/-- Retain original numerical, reduced-coefficient and uncancelled factored primitive evaluators at one identical lift.

The original primitive's polynomial index and cached coefficient expression
remain indices. Each value is its complete original factory, and every factory
consumes the same retained preparation or original cofactor certificate once.
-/
@[expose] def Values (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (prepared : Division.Prepared reading.lift.value) :=
  Σ identity : { retained : PowerIdentity prepared.denominator 2
        ((Paths.polynomial parameter).eval
          (point site parameter 2 (Waist.direction quarter time) positive).base) //
      retained = squareIdentity reading prepared },
    { interpretation : Expression.Denotation primitive.coefficient
          (point site parameter 2 (Waist.direction quarter time) positive).base prepared.denominator //
        interpretation = primitive.interpret
          (point site parameter 2 (Waist.direction quarter time) positive).base
          prepared.denominator identity.val prepared.apart } ×
      { value : CoherentNamed // value = primitive.value
          (point site parameter 2 (Waist.direction quarter time) positive).base prepared.denominator prepared.apart } ×
        { factored : CoherentNamed // factored = primitive.factorizedValue
          (point site parameter 2 (Waist.direction quarter time) positive).base
          reading.lift.unitRoot.value reading.lift.unitRoot.apart
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ }

namespace Values

/-- Construct each actual original primitive evaluator once from the same retained cubic and cofactor caches. -/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (prepared : Division.Prepared reading.lift.value) :
    Values primitive reading prepared :=
  let identity := squareIdentity reading prepared
  let interpretation := primitive.interpret (point site parameter 2 (Waist.direction quarter time) positive).base
    prepared.denominator identity prepared.apart
  let value := primitive.value (point site parameter 2 (Waist.direction quarter time) positive).base
    prepared.denominator prepared.apart
  let factored := primitive.factorizedValue (point site parameter 2 (Waist.direction quarter time) positive).base
    reading.lift.unitRoot.value reading.lift.unitRoot.apart
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹
  ⟨⟨identity, rfl⟩, ⟨⟨interpretation, rfl⟩, ⟨⟨value, rfl⟩, ⟨factored, rfl⟩⟩⟩⟩

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {prepared : Division.Prepared reading.lift.value}

/-- Read the original finite-power identity retained on the exact prepared full-sheet channel. -/
@[expose] def identity (values : Values primitive reading prepared) : PowerIdentity prepared.denominator 2
    ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter time) positive).base) := values.1.val

/-- Read the actual interpretation of the original unchanged reduced coefficient-expression cache. -/
@[expose] def interpretation (values : Values primitive reading prepared) : Expression.Denotation primitive.coefficient
    (point site parameter 2 (Waist.direction quarter time) positive).base prepared.denominator := values.2.1.val

/-- Read the independently retained original productive primitive coefficient evaluator. -/
@[expose] def value (values : Values primitive reading prepared) : CoherentNamed := values.2.2.1.val

/-- Read the actual uncancelled coefficient specialization on the identical original cofactor channel. -/
@[expose] def factored (values : Values primitive reading prepared) : CoherentNamed := values.2.2.2.val

/-- The retained prepared-sheet identity is the original square transport factory. -/
theorem identity_eq (values : Values primitive reading prepared) :
    values.identity = squareIdentity reading prepared := values.1.property

/-- The retained interpretation is its exact original factory at the same cached coefficient and sheet identity. -/
theorem interpretation_eq (values : Values primitive reading prepared) : values.interpretation =
    primitive.interpret (point site parameter 2 (Waist.direction quarter time) positive).base
      prepared.denominator values.identity prepared.apart := values.2.1.property

/-- The actual primitive evaluator is the original numerical factory on the same prepared sheet. -/
theorem value_eq (values : Values primitive reading prepared) : values.value =
    primitive.value (point site parameter 2 (Waist.direction quarter time) positive).base
      prepared.denominator prepared.apart := values.2.2.1.property

/-- The factored cache is the same original evaluator specialization with its complete odd reciprocal power. -/
theorem factored_eq (values : Values primitive reading prepared) : values.factored =
    primitive.factorizedValue (point site parameter 2 (Waist.direction quarter time) positive).base
      reading.lift.unitRoot.value reading.lift.unitRoot.apart
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ := values.2.2.2.property

/-- Both retained primitive evaluators agree through the original coefficient interpretation machinery. -/
def agrees_interpretation (values : Values primitive reading prepared) :
    NamedEquivalent values.value.name values.interpretation.channel.name := by
  have compared : NamedEquivalent
      (primitive.value (point site parameter 2 (Waist.direction quarter time) positive).base
        prepared.denominator prepared.apart).name
      (primitive.interpret (point site parameter 2 (Waist.direction quarter time) positive).base
        prepared.denominator values.identity prepared.apart).channel.name :=
    primitive.reciprocal_power_equivalent _ prepared.denominator values.identity prepared.apart
  exact NamedEquivalent.transport (congrArg (fun retained : CoherentNamed => retained.name) values.value_eq.symm)
    (congrArg (fun retained : Expression.Denotation primitive.coefficient
      (point site parameter 2 (Waist.direction quarter time) positive).base prepared.denominator =>
        retained.channel.name) values.interpretation_eq.symm) compared

/-- The retained actual full-sheet primitive agrees with its original uncancelled cofactor evaluator.

Intrinsic regularity supplies the exact ordinate's nonzero evidence. The
original lift product and preparation derive the comparison without another
root query, coefficient copy, arithmetic witness or desired endpoint equation.
-/
def agrees_factored (values : Values primitive reading prepared) (regular : parameter ≠ criticalValue site) :
    NamedEquivalent values.value.name values.factored.name :=
  NamedEquivalent.transport (congrArg (fun retained : CoherentNamed => retained.name) values.value_eq.symm)
    (congrArg (fun retained : CoherentNamed => retained.name) values.factored_eq.symm)
    (primitive.value_factorized_inverse
      (point site parameter 2 (Waist.direction quarter time) positive).base
      reading.lift.value reading.lift.unitRoot.value prepared
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate reading.lift.value_eq
      (parallel_ordinate_ne_zero site parameter (Waist.direction quarter time) regular) reading.lift.unitRoot.apart)

end Values

/-- Retain one original cubic preparation and its complete primitive evaluator caches on the supplied Reading. -/
@[expose] def Endpoint (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site) :=
  Σ prepared : { retained : Division.Prepared reading.lift.value // retained = reading.parallelPrepared regular },
    Values primitive reading prepared.val

namespace Endpoint

/-- Prepare the same original supplied cubic lift once and retain each original primitive coefficient cache once. -/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site) :
    Endpoint primitive reading regular :=
  let prepared := reading.parallelPrepared regular
  let values := Values.build primitive reading prepared
  ⟨⟨prepared, rfl⟩, values⟩

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}

/-- Read the identical retained full-cubic denominator preparation without rebuilding its original lift. -/
@[expose] def prepared (endpoint : Endpoint primitive reading regular) : Division.Prepared reading.lift.value :=
  endpoint.1.val

/-- Read all actual original primitive coefficient caches consuming that exact original preparation. -/
@[expose] def values (endpoint : Endpoint primitive reading regular) : Values primitive reading endpoint.prepared :=
  endpoint.2

/-- The retained primitive endpoint preparation is the original factory on the same supplied complete Reading. -/
theorem prepared_eq (endpoint : Endpoint primitive reading regular) :
    endpoint.prepared = reading.parallelPrepared regular := endpoint.1.property

end Endpoint

/-- Prescribe the original primitive coefficient on the actual displayed cofactor reading and exact radial ordinate.

The original numerator, scale, odd exponent, curve parameter and oriented
quarter remain unchanged. This scalar expression is not chosen from any
integral, derivative output or arithmetic-process witness.
-/
@[expose] def reading (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (quarter : UnitCircuitQuarter) (time : Fraction.Rational) (cofactorReading : Canonical) : Canonical :=
  primitive.scale * primitive.numerator.eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base *
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).ordinate⁻¹ ^
        primitive.denominatorExponent * cofactorReading⁻¹ ^ primitive.denominatorExponent

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive

end
