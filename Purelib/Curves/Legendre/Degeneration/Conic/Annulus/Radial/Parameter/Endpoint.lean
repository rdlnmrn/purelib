module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

/-!
# Original normalized parameter caches at a retained radial reading

One complete original requested-time Reading supplies its identical cubic
lift and cofactor cache. Its known normalized ordinate constructs one Anchor;
the admitted increment constructs one Step on that same Anchor. The retained
factory equations identify these exact caches without re-querying a source.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}

/-- Cache one original radial Reading, its exact known-root Anchor and one admitted parameter Step.

The dependent cache retains the complete input Reading and its original lift.
Both later stages carry their own exact factory equations and consume the
previous retained value once; no root process or cofactor owner is substituted.
-/
@[expose] def Endpoint (actual : Transport.Quarter site parameter 2 quarter positive)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (regular : parameter ≠ criticalValue site) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :=
  Σ reading : Transport.Reading actual time inside,
    Σ anchor : { retained : Anchor reading.lift //
      retained = Anchor.build reading.lift regular actual.data.bound },
      { step : Step anchor.val increment // step = Step.build anchor.val increment admitted }

namespace Endpoint

variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {regular : parameter ≠ criticalValue site} {increment : Canonical}
variable {admitted : IncrementBound site parameter increment}

/-- Construct one normalized Anchor and admitted Step while reusing the identical supplied original Reading. -/
def ofReading (reading : Transport.Reading actual time inside)
    (regular : parameter ≠ criticalValue site) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : Endpoint actual time inside regular increment admitted :=
  let anchor := Anchor.build reading.lift regular actual.data.bound
  let step := Step.build anchor increment admitted
  ⟨reading, ⟨anchor, rfl⟩, ⟨step, rfl⟩⟩

/-- Query the original retained quarter once, then retain its same normalized Anchor and admitted Step. -/
def build (actual : Transport.Quarter site parameter 2 quarter positive)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (regular : parameter ≠ criticalValue site) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : Endpoint actual time inside regular increment admitted :=
  let reading := Transport.Reading.build actual time inside
  ofReading reading regular increment admitted

/-- Read the identical complete original requested-time Reading retained in the normalized endpoint cache. -/
@[expose] def reading (endpoint : Endpoint actual time inside regular increment admitted) :
    Transport.Reading actual time inside := endpoint.1

/-- Read the original Anchor on that same retained Reading's complete cubic lift. -/
@[expose] def anchor (endpoint : Endpoint actual time inside regular increment admitted) :
    Anchor endpoint.reading.lift := endpoint.2.1.val

/-- Read the identical admitted Step on the endpoint's actual cached Anchor. -/
@[expose] def step (endpoint : Endpoint actual time inside regular increment admitted) :
    Step endpoint.anchor increment := endpoint.2.2.val

/-- The endpoint's normalized Anchor is its exact original factory on the same retained Reading. -/
theorem anchor_eq (endpoint : Endpoint actual time inside regular increment admitted) :
    endpoint.anchor = Anchor.build endpoint.reading.lift regular actual.data.bound := endpoint.2.1.property

/-- The cached normalized Step is its exact admitted factory on the identical retained Anchor. -/
theorem step_eq (endpoint : Endpoint actual time inside regular increment admitted) :
    endpoint.step = Step.build endpoint.anchor increment admitted := endpoint.2.2.property

/-- Reusing an original Reading retains that entire input cache without a second original quarter query. -/
theorem ofReading_reading (reading : Transport.Reading actual time inside)
    (regular : parameter ≠ criticalValue site) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :
    (ofReading reading regular increment admitted).reading = reading := by
  unfold ofReading Endpoint.reading
  rfl

/-- The endpoint constructor retains exactly its single original requested-time Reading factory. -/
theorem build_reading (actual : Transport.Quarter site parameter 2 quarter positive)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (regular : parameter ≠ criticalValue site) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :
    (build actual time inside regular increment admitted).reading = Transport.Reading.build actual time inside := by
  unfold build
  exact ofReading_reading _ regular increment admitted

end Endpoint

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

end
