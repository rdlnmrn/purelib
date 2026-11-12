module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Path
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

/-! # Factor caches on the identical original sharp spatial route

The supplied original Geometry already retains its complete source/target
Reading pair, sharp clearance and paid ClearBoxPaths.Route factory. The
factor path consumes precisely that route's stored physical edges and ambient
witness. No route, reading, source attachment or cofactor allowance is rebuilt.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The existing factor-path cache type on exactly the supplied original geometry's stored route and ambient witness. -/
@[expose] def RoutePath (budgets : Budgets anchor)
    (geometry : Parallel.Geometry source targetReading anchor.regular payment) :=
  Path budgets geometry.route.path geometry.route.within

/-- The complete factor-path factory retains the same geometry and every actual physical route edge. -/
@[irreducible, expose] def RouteCache (budgets : Budgets anchor)
    (geometry : Parallel.Geometry source targetReading anchor.regular payment)
    (completed : RoutePath budgets geometry) : Prop :=
  completed = Path.build budgets geometry.route.path geometry.route.within

/-- The retained factor-path caches belong to the identical original sharp spatial route.

The existing subtype binds the whole factor-path factory to the original
stored route and ambient witness. The entire original Geometry and budget
caches remain indices, including both independent original Reading owners.
-/
@[expose] def Route (budgets : Budgets anchor)
    (geometry : Parallel.Geometry source targetReading anchor.regular payment) :=
  { completed : RoutePath budgets geometry // RouteCache budgets geometry completed }

namespace Route

variable {budgets : Budgets anchor}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}

/-- Retain a completed original route factor-path cache without rebuilding its edges, budgets or preparations. -/
@[expose] def ofCompleted (completed : RoutePath budgets geometry)
    (completed_eq : RouteCache budgets geometry completed) : Route budgets geometry := ⟨completed, completed_eq⟩

/-- Prepare each physical edge once on the identical original supplied sharp Route and factor budgets. -/
def build (budgets : Budgets anchor)
    (geometry : Parallel.Geometry source targetReading anchor.regular payment) : Route budgets geometry :=
  let completed := Path.build budgets geometry.route.path geometry.route.within
  ofCompleted completed (by unfold RouteCache; rfl)

/-- Read the entire unchanged original factor-path cache on the exact stored spatial Route. -/
@[expose] def path (completed : Route budgets geometry) : RoutePath budgets geometry := completed.val

/-- The retained factor-path is the whole original factory on the same stored route and ambient-containment cache. -/
theorem path_eq (completed : Route budgets geometry) :
    completed.path = Path.build budgets geometry.route.path geometry.route.within := by
  have retained := completed.property
  unfold RouteCache at retained
  exact retained

/-- Retaining completed route evidence returns the same entire original factor-path cache. -/
theorem ofCompleted_path (completed : RoutePath budgets geometry)
    (completed_eq : RouteCache budgets geometry completed) :
    (ofCompleted completed completed_eq).path = completed := rfl

end Route

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
