module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Comparison
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Endpoint
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Basic

/-! # A particular paid route and its independent original endpoint Lift

The actual path-shape comparison keeps its original terminal source. The
empty route compares the two original quarter Readings at the same base;
one- and two-edge routes consume their original factor Readings and exact
complete endpoint equations. The existing geometry payment pays normalized
sheet agreement internally. Both endpoint comparisons are constructed once
and retained with their exact factories.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

namespace Route.Acquisition.Comparison

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {prepared : Division.Prepared source.lift.value}
variable (attachment : Spatial.Source source prepared)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Cache

/-- The unchanged actual paid output agrees with the independently retained original target Lift.

Original complete endpoint equations identify the physical point. The same
quarter depth-seven payment places its exact target ordinate in the original
source Seed square. The two-edge stopped alternative consumes the preceding
Reading at its retained original preparation; no target process is retagged.
-/
def agrees_target (target : Transport.Reading actual last lastInside) : {finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor)
      (Spatial.coordinate site parameter 2 quarter positive first) finish) →
    (within : path.WithinAmbient) → (factors : Path budgets path within) →
    (paid : CoveredTracedPath.Acquisition.Spine (fun {_start _finish} segment => widthRequest anchor segment)
      path within attachment.attached.owner) →
    (cache : Cache attachment path within factors paid) →
    (_point_eq : finish = (Parameter.sourcePoint site parameter (Waist.direction quarter last)).base) →
    (_payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) →
    NamedEquivalent (channel attachment path within factors paid cache).name target.lift.value.name := by
  intro finish path
  cases path with
  | nil _point =>
      intro _within _factors _paid _cache point_eq _payment
      exact Transport.Reading.agrees_of_base_eq source target anchor.regular point_eq
  | cons _head tail =>
      cases tail with
      | nil _finish =>
          intro _within _factors paid cache point_eq payment
          exact (First.terminal attachment cache).1.agrees_target target
            (paid.1.prepared.acquired.prepared.finish_eq.trans point_eq) payment
      | cons _second remaining =>
          cases remaining with
          | nil _finish =>
              intro _within _factors paid cache point_eq payment
              let output := Second.output attachment cache.2
              change NamedEquivalent output.channel.name target.lift.value.name
              cases output with
              | inl retained =>
                  exact (Second.terminal attachment cache.2).1.agrees_target target
                    (retained.property.1.trans
                      (paid.2.1.prepared.acquired.prepared.finish_eq.trans point_eq)) payment
              | inr terminal =>
                  exact terminal.1.agrees_target target
                    (paid.2.1.prepared.acquired.prepared.finish_eq.trans point_eq) payment
          | cons _third _rest =>
              intro _within _factors _paid cache _point_eq _payment
              exact nomatch cache

end Cache

variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}
variable {factors : Route budgets geometry}
variable {retained : Route.Acquisition factors attachment.attached.owner}

namespace Result

/-- Derive actual paid-output agreement with the exact original independent target already retained by the Geometry. -/
def agrees_target (result : Result attachment retained) :
    NamedEquivalent result.channel.name targetReading.lift.value.name :=
  Cache.agrees_target attachment targetReading geometry.route.path geometry.route.within
    retained.factors.path retained.spine result.val rfl payment

/-- Both derived endpoint relations retain their exact completed factories and the original paid Result as index.

The original physical output and independent target remain separate inputs.
Their complete operational comparison is stored once, followed by its actual
composition with this particular covered finishing-Owner comparison.
-/
@[expose] def Endpoint (result : Result attachment retained) :=
  Σ compared : { relation : NamedEquivalent result.channel.name targetReading.lift.value.name //
      relation = agrees_target attachment result },
    { finished : NamedEquivalent
        (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner) targetReading.lift.value.name //
      finished = result.equivalent.trans compared.val }

namespace Endpoint

/-- Construct and retain both independent-target comparisons once from the same complete original paid Result. -/
def build (result : Result attachment retained) : Endpoint attachment result :=
  let compared := Result.agrees_target attachment result
  let finished := result.equivalent.trans compared
  ⟨⟨compared, rfl⟩, ⟨finished, rfl⟩⟩

variable {attachment : Spatial.Source source prepared}
variable {retained : Route.Acquisition factors attachment.attached.owner}
variable {result : Result attachment retained}
variable (endpoint : Endpoint attachment result)

/-- Read the same completed comparison between the actual retained output channel and independent target Lift. -/
@[expose] def comparison : NamedEquivalent result.channel.name targetReading.lift.value.name := endpoint.1.val

/-- The stored actual-output comparison is the exact internally derived factory on the same original Result. -/
theorem comparison_eq : endpoint.comparison = Result.agrees_target attachment result := endpoint.1.property

/-- Read the stored covered finish Owner's derived agreement with the original independent endpoint Lift. -/
@[expose] def finish : NamedEquivalent
    (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner) targetReading.lift.value.name :=
  endpoint.2.val

/-- The finishing comparison composes the exact retained original route and independent-target comparisons. -/
theorem finish_eq : endpoint.finish = result.equivalent.trans endpoint.comparison := endpoint.2.property

end Endpoint
end Result

end Route.Acquisition.Comparison

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
