module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Values
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Rational.Box.Refinement

/-! # Queried physical factor channels from the same preparation caches

Each original factor preparation is queried once at the exact requested
physical segment parameter. Parameter transports retain the complete queried
Owners; their original certificates construct one full product and coordinate
cache. The actual source/target curve readings remain independent inputs to
later operational comparison.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

open Purelib.RootIsolation.SquareRoot

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.RootIsolation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient}

/-- The exact original normalized trace-query cache type on this same retained physical factor preparation. -/
@[expose] def NormalQuery (completed : Segment budgets segment within) (time : Fraction.Rational) :=
  FixedRootBoxPath.Preparation.Reading completed.normal time

/-- The exact original cofactor trace-query cache type on the same retained physical segment parameter. -/
@[expose] def UnitQuery (completed : Segment budgets segment within) (time : Fraction.Rational) :=
  FixedRootBoxPath.Preparation.Reading completed.unit time

/-- The original normalized query is the completed preparation's exact requested-time operation. -/
@[irreducible, expose] def NormalQueryCache (completed : Segment budgets segment within)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) (query : NormalQuery completed time) : Prop :=
  query = completed.preparedNormal.read time inside

/-- The original cofactor query is that same completed preparation's exact requested-time operation. -/
@[irreducible, expose] def UnitQueryCache (completed : Segment budgets segment within)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) (query : UnitQuery completed time) : Prop :=
  query = completed.preparedUnit.read time inside

/-- Actual original factor queries, reindexed complete Owners and one stored full product at a physical segment point.

Whole query-factory identities preserve both completed preparation caches.
The Owner equations are the original parameter transports of those exact
queries; Values retains their complete original certificate/product/coordinate
caches. The underlying physical segment is never replaced by a chart witness.
-/
@[expose] def Reading (completed : Segment budgets segment within) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) :=
  Σ normalQuery : { query : NormalQuery completed time // NormalQueryCache completed time inside query },
    Σ unitQuery : { query : UnitQuery completed time // UnitQueryCache completed time inside query },
      Σ normal : { owner : SquareRootContinuationChain.Owner
          (Clearance.normalizedRadicand site parameter (segment.pointAt time)) // owner =
          Owner.Transport.castOwnerParameter (completed.normal_point time) normalQuery.val.owner },
        Σ unit : { owner : SquareRootContinuationChain.Owner ((unitPolynomial site).eval (segment.pointAt time)) //
            owner = Owner.Transport.castOwnerParameter (completed.unit_point time) unitQuery.val.owner },
          { values : Values site parameter (segment.pointAt time) unit.val normal.val //
              values = Values.build unit.val normal.val }

namespace Reading

/-- Query both retained original factors once and cache their actual Owners and full product. -/
def build (completed : Segment budgets segment within) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) : Reading completed time inside :=
  let normalQuery := completed.preparedNormal.read time inside
  let unitQuery := completed.preparedUnit.read time inside
  let normal := Owner.Transport.castOwnerParameter (completed.normal_point time) normalQuery.owner
  let unit := Owner.Transport.castOwnerParameter (completed.unit_point time) unitQuery.owner
  let values := Values.build unit normal
  ⟨⟨normalQuery, by unfold NormalQueryCache; rfl⟩,
    ⟨⟨unitQuery, by unfold UnitQueryCache; rfl⟩, ⟨⟨normal, rfl⟩, ⟨⟨unit, rfl⟩, ⟨values, rfl⟩⟩⟩⟩⟩

variable {completed : Segment budgets segment within} {time : Fraction.Rational}
variable {inside : FixedRootBoxPath.Inside time}

/-- Read the identical entire original normalized trace query on the unchanged cached preparation. -/
@[expose] def normalQuery (reading : Reading completed time inside) : NormalQuery completed time := reading.1.val

/-- Read the identical entire original cofactor trace query on its separate unchanged cached preparation. -/
@[expose] def unitQuery (reading : Reading completed time inside) : UnitQuery completed time := reading.2.1.val

/-- Read the reindexed complete original normalized Owner at the actual physical segment coordinate. -/
@[expose] def normal (reading : Reading completed time inside) := reading.2.2.1.val

/-- Read the reindexed complete original cofactor Owner at that same physical coordinate. -/
@[expose] def unit (reading : Reading completed time inside) := reading.2.2.2.1.val

/-- Read the complete original certificate/product/coordinate cache constructed from those identical queried Owners. -/
@[expose] def values (reading : Reading completed time inside) :
    Values site parameter (segment.pointAt time) reading.unit reading.normal := reading.2.2.2.2.val

/-- The actual normalized query keeps the completed original preparation and exact requested-time identity. -/
theorem normalQuery_eq (reading : Reading completed time inside) :
    reading.normalQuery = completed.preparedNormal.read time inside := by
  have retained := reading.1.property
  unfold NormalQueryCache at retained
  exact retained

/-- The actual cofactor query keeps its completed original preparation and that same requested-time identity. -/
theorem unitQuery_eq (reading : Reading completed time inside) :
    reading.unitQuery = completed.preparedUnit.read time inside := by
  have retained := reading.2.1.property
  unfold UnitQueryCache at retained
  exact retained

/-- The normalized Owner is only the original exact-parameter transport of the identical actual query Owner. -/
theorem normal_eq (reading : Reading completed time inside) : reading.normal =
    Owner.Transport.castOwnerParameter (completed.normal_point time) reading.normalQuery.owner :=
  reading.2.2.1.property

/-- The cofactor Owner is only the original exact-parameter transport of its identical actual query Owner. -/
theorem unit_eq (reading : Reading completed time inside) : reading.unit =
    Owner.Transport.castOwnerParameter (completed.unit_point time) reading.unitQuery.owner :=
  reading.2.2.2.1.property

/-- The full product/cache is the original complete factory on those actual separately retained query Owners. -/
theorem values_eq (reading : Reading completed time inside) :
    reading.values = Values.build reading.unit reading.normal := reading.2.2.2.2.property

/-- The actual normalized query Owner preserves refinement to the identical original source seed box. -/
theorem normal_refines (reading : Reading completed time inside) :
    reading.normal.track.initial.box.Refines anchor.seed.owner.track.initial.box := by
  rewrite [reading.normal_eq, Owner.Transport.castOwnerParameter_initial_box]
  exact reading.normalQuery.refines

/-- The actual cofactor query Owner preserves refinement to the unchanged original quarter reference box. -/
theorem unit_refines (reading : Reading completed time inside) :
    reading.unit.track.initial.box.Refines actual.data.source.track.initial.box := by
  rewrite [reading.unit_eq, Owner.Transport.castOwnerParameter_initial_box]
  exact reading.unitQuery.refines

end Reading

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
