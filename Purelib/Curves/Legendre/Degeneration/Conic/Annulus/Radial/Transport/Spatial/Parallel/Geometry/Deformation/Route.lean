module

public import Purelib.Riemann.Paths.ClearBoxPaths.Parameter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Continuation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry.Deformation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Actual horizontal factor preparations on the retained L-route fan

The original Route supplies its literal zero, one or two oriented edge
occurrences. Every moving edge is prepared once on its corresponding chord
interval, using the SAME source Seed and cofactor budgets. Two edges retain
the shared half-time corner exactly. The empty route performs no artificial
edge preparation. No OwnerPath, paid acquisition or old reading is replaced.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Deformation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Factors (Budgets)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The original spatial Route chord is the SAME actual radial endpoint chord at its unchanged fraction. -/
theorem route_chord (geometry : Geometry source targetReading anchor.regular payment)
    (fraction : Fraction.Rational) :
    geometry.route.chord fraction =
      Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction := by
  unfold ClearBoxPaths.Route.chord Tangent.baseChord
  rewrite [show first + (last - first) = last by ring1]
  rfl

/-- The two actual ruled strips share their exact original chord boundary at the SAME fraction and orientation. -/
theorem chord_boundary (geometry : Geometry source targetReading anchor.regular payment)
    (fraction : Fraction.Rational) : geometry.deformation fraction 1 = geometry.route.deformation fraction 0 :=
  (geometry.deformation_chord fraction).trans
    ((route_chord (anchor := anchor) geometry fraction).symm.trans (geometry.route.deformation_chord fraction).symm)

/-- The SAME retained original RegionClearance pays every point of the literal chord-to-L-route deformation. -/
theorem route_deformation_lower (geometry : Geometry source targetReading anchor.regular payment)
    {fraction blend : Fraction.Rational} (fractionInside : FixedRootBoxPath.Inside fraction)
    (blendInside : FixedRootBoxPath.Inside blend) :
    geometry.clearance.bound ≤ Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (geometry.route.deformation fraction blend)) :=
  geometry.route.deformation_lower geometry.clearance
    (source_inside (positive := positive) anchor.regular)
    (target_inside (positive := positive) anchor.regular payment) fractionInside blendInside

/-- The actual ruled edge remains in the SAME original factor-clear source box at every original unit parameter. -/
theorem route_edge_inside (geometry : Geometry source targetReading anchor.regular payment)
    {start finish : Canonical}
    (edge : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish)
    (within : edge.WithinAmbient) (left right : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside left) (rightInside : FixedRootBoxPath.Inside right)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    (Factors.sourceBox anchor).Contains (geometry.route.edgeDeformation edge left right time blend) :=
  geometry.route.edgeDeformation_contains edge within
    (source_inside (positive := positive) anchor.regular)
    (target_inside (positive := positive) anchor.regular payment) leftInside rightInside inside blendInside

/-- Both original factor preparations on one actual ruled edge and its unchanged source budgets. -/
@[expose] def EdgePreparation (budgets : Budgets anchor)
    (geometry : Geometry source targetReading anchor.regular payment)
    {start finish : Canonical}
    (edge : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish)
    (within : edge.WithinAmbient) (left right : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside left) (rightInside : FixedRootBoxPath.Inside right)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :=
  Factors.Continuation budgets (fun time => geometry.route.edgeDeformation edge left right time blend)
    (route_edge_inside geometry edge within left right leftInside rightInside blend blendInside)
    (geometry.route.edgeScale edge left right blend)
    (geometry.route.edgeScale_nonnegative edge left right blendInside)
    (fun first last _ _ => geometry.route.edgeDeformation_distance edge left right blendInside first last)

namespace EdgePreparation

/-- Prepare each factor once along the actual ruled edge, retaining its original depth, advance and endpoint caches. -/
def build (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    {start finish : Canonical}
    (edge : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish)
    (within : edge.WithinAmbient) (left right : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside left) (rightInside : FixedRootBoxPath.Inside right)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :
    EdgePreparation budgets geometry edge within left right leftInside rightInside blend blendInside :=
  Factors.Continuation.build budgets (fun time => geometry.route.edgeDeformation edge left right time blend)
    (route_edge_inside geometry edge within left right leftInside rightInside blend blendInside)
    (geometry.route.edgeScale edge left right blend)
    (geometry.route.edgeScale_nonnegative edge left right blendInside)
    (fun first last _ _ => geometry.route.edgeDeformation_distance edge left right blendInside first last)

variable {budgets : Budgets anchor} {geometry : Geometry source targetReading anchor.regular payment}
variable {start middle finish : Canonical}
variable {firstEdge : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) start middle}
variable {secondEdge : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) middle finish}
variable {firstWithin : firstEdge.WithinAmbient} {secondWithin : secondEdge.WithinAmbient}
variable {blend : Fraction.Rational} {blendInside : FixedRootBoxPath.Inside blend}

/-- Derive the literal first preparation's normalized finish agreement with the second's actual cached source.

The common-point law is the original shared Route corner of the two local
fans, valid for every blend. Both original preparation Owners and full
caches remain unchanged; the original source Budget derives the sign.
-/
def normal_join
    (first : EdgePreparation budgets geometry firstEdge firstWithin 0 (1 / 2)
      (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside)
    (second : EdgePreparation budgets geometry secondEdge secondWithin (1 / 2) 1
      (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside) :
    NamedEquivalent (ownerRootName first.preparedNormal.finishOwner.parameterNonzero first.preparedNormal.finishOwner)
      (ownerRootName second.preparedNormal.source.parameterNonzero second.preparedNormal.source) :=
  Factors.Continuation.normal_join first second (geometry.route.edgeDeformation_join firstEdge secondEdge blend)

/-- Derive the two actual cofactor preparation Owners' signed agreement at the SAME retained corner. -/
def unit_join
    (first : EdgePreparation budgets geometry firstEdge firstWithin 0 (1 / 2)
      (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside)
    (second : EdgePreparation budgets geometry secondEdge secondWithin (1 / 2) 1
      (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside) :
    NamedEquivalent (ownerRootName first.preparedUnit.finishOwner.parameterNonzero first.preparedUnit.finishOwner)
      (ownerRootName second.preparedUnit.source.parameterNonzero second.preparedUnit.source) :=
  Factors.Continuation.unit_join first second (geometry.route.edgeDeformation_join firstEdge secondEdge blend)

end EdgePreparation

/-- Original preparations indexed by the literal retained ordered path shape and its at-most-two-edge certificate.

A one-edge shape retains one whole completed preparation with its exact
factory equation. A two-edge shape retains its two distinct preparations on
[0,1/2] and [1/2,1] in original order. This is only a cache family over the
original path; it introduces no replacement path, trace or root Owner.
-/
@[expose] def RoutePreparations (budgets : Budgets anchor)
    (geometry : Geometry source targetReading anchor.regular payment)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :
    {start finish : Canonical} →
      (path : ClearPath (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish) →
      path.WithinAmbient → path.segmentCount ≤ 2 → Type
  | _, _, .nil _, _, _ => PUnit
  | _, _, .cons head tail, within, short =>
      match tail with
      | .nil _ =>
          { completed : EdgePreparation budgets geometry head within.head 0 1
              (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside // completed =
            EdgePreparation.build budgets geometry head within.head 0 1
              (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside }
      | .cons second remaining =>
          match remaining with
          | .nil _ =>
              { completed : EdgePreparation budgets geometry head within.head 0 (1 / 2)
                  (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside // completed =
                EdgePreparation.build budgets geometry head within.head 0 (1 / 2)
                  (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside } ×
              { completed : EdgePreparation budgets geometry second within.tail.head (1 / 2) 1
                  (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside // completed =
                EdgePreparation.build budgets geometry second within.tail.head (1 / 2) 1
                  (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside }
          | .cons _ rest => False.elim (by
              change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
              omega0)

namespace RoutePreparations

/-- Construct actual preparations on each SAME retained edge exactly once in its original orientation and order. -/
def build (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :
    {start finish : Canonical} →
      (path : ClearPath (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish) →
      (within : path.WithinAmbient) → (short : path.segmentCount ≤ 2) →
      RoutePreparations budgets geometry blend blendInside path within short
  | _, _, .nil _, _, _ => PUnit.unit
  | _, _, .cons head tail, within, short => by
      cases tail with
      | nil endpoint =>
          let completed := EdgePreparation.build budgets geometry head within.head 0 1
            (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside
          exact ⟨completed, rfl⟩
      | cons second remaining =>
          cases remaining with
          | nil endpoint =>
              let first := EdgePreparation.build budgets geometry head within.head 0 (1 / 2)
                (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside
              let last := EdgePreparation.build budgets geometry second within.tail.head (1 / 2) 1
                (of_decide_eq_true rfl) (of_decide_eq_true rfl) blend blendInside
              exact ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩
          | cons third rest =>
              change Nat.succ (Nat.succ (Nat.succ rest.segmentCount)) ≤ 2 at short
              omega0

end RoutePreparations

/-- The actual preparation-cache family on precisely the SAME Geometry's stored original L-route and containment. -/
@[expose] def RouteHorizontal (budgets : Budgets anchor)
    (geometry : Geometry source targetReading anchor.regular payment)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :=
  RoutePreparations budgets geometry blend blendInside geometry.route.path geometry.route.within geometry.route.short

namespace RouteHorizontal

/-- Prepare the SAME literal zero/one/two-edge Route without changing or replaying its original paid acquisition. -/
def build (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (blend : Fraction.Rational) (blendInside : FixedRootBoxPath.Inside blend) :
    RouteHorizontal budgets geometry blend blendInside :=
  RoutePreparations.build budgets geometry blend blendInside
    geometry.route.path geometry.route.within geometry.route.short

end RouteHorizontal
end Deformation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry
