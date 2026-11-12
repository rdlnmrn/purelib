module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope.Numerators.Schedule
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership

/-! # Genuine fine quarter observations after a sufficient fixed-coarse request schedule

One original depth-seven six-row envelope cache computes a sufficient depth
before layerAt creates any finer source Reading or cofactor observation.
The actual new depth is also at least ten, paying the independent repeated-
visit seed-window certificate. The resulting original Numerical input
retains that SAME layer and one decomposition; it is not an old Steps
quarter or a transport of an unpaid execution.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Input.Numerical

open Purelib.Data
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Block → LayerBlock
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}
variable (data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Specification.Table.forms parameter index))
variable (coarse : Numerators.Cache (quarter := unitQuarter) leg.regular 7
  UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)
variable {row : Fin 6} {initialAccuracy : AccuracyRequest}
variable (initialPiece : Piece (data row) leg.actual initialAccuracy) (target : AccuracyRequest)
variable (sourceQueried : initialPiece.Queried) (atSource : initialPiece.span.lower = 0)
variable (atFinish : initialPiece.span.upper = 1)
variable (finishQuery : { reading : ReadingAt leg.actual initialPiece.upperEndpoint //
  QueryCache leg.actual initialPiece.upperEndpoint reading })

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] SquareRootTrackEquivalence.ownerRootName

/-- Compute a sufficient depth first, create the original fine Layer once, then cache its original decomposition.

The SAME coarse six-row cache pays physical Route widths and every actual
fine cofactor cost. The maximum with ten additionally pays repeated-visit
window nearness. The complete supplied initial Piece and final query stay
unchanged; no finer Reading is obtained by relabelling an old observation.
-/
def scheduled : Numerical (data := data row) leg :=
  let depth := max (Numerators.minimum data coarse initialAccuracy target) 10
  let layer := initialPiece.layerAt depth
  ofLayer initialPiece depth layer rfl
    ((Numerators.seven_le data coarse initialAccuracy target).trans (Nat.Order.le_max_left _ _))
    sourceQueried atSource atFinish finishQuery

/-- The new numerical input retains exactly the computed sufficient fine depth. -/
theorem scheduled_depth :
    (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).depth =
      max (Numerators.minimum data coarse initialAccuracy target) 10 := by
  unfold scheduled
  exact ofLayer_depth _ _ _ _ _ _ _ _ _

/-- The genuine fine producer preserves the identical original initial request. -/
theorem scheduled_accuracy :
    (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).accuracy =
      initialAccuracy := by
  unfold scheduled
  exact ofLayer_accuracy _ _ _ _ _ _ _ _ _

/-- The genuine fine producer retains the SAME complete initial Piece and its complete original source cache. -/
theorem scheduled_initial_heq :
    HEq (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).initial
      initialPiece := by
  unfold scheduled
  exact ofLayer_initial_heq _ _ _ _ _ _ _ _ _

/-- The actual created Layer, not an equality to an old execution, is retained whole by the numerical input. -/
theorem scheduled_layer_heq :
    HEq (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).layer
      (initialPiece.layerAt (max (Numerators.minimum data coarse initialAccuracy target) 10)) := by
  unfold scheduled
  exact ofLayer_layer_heq _ _ _ _ _ _ _ _ _

/-- The same actual chosen depth pays the fixed coarse schedule at the retained input's own original request index. -/
theorem scheduled_minimum_le :
    Numerators.minimum data coarse
        (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).accuracy target ≤
      (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).depth := by
  rewrite [scheduled_accuracy, scheduled_depth]
  exact Nat.Order.le_max_left _ _

/-- The actual new numerical Layer pays the depth-ten repeated-visit geometry before any finer observations. -/
theorem scheduled_ten_le :
    10 ≤ (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).depth := by
  rewrite [scheduled_depth]
  exact Nat.Order.le_max_right _ _

variable (piece : Piece (data row) leg.actual
  (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).layer.accuracy)
variable (member : piece ∈
  (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).layer.pieces)

include member

/-- Every actual newly created member span has the intrinsic depth-ten width needed by the repeat-window bound. -/
theorem scheduled_piece_width : piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 10 :=
  (scheduled data coarse initialPiece target sourceQueried atSource atFinish finishQuery).layer.width_le 10
    (scheduled_ten_le data coarse initialPiece target sourceQueried atSource atFinish finishQuery) piece member

variable {targetEndpoint : Endpoint}
variable {queried : { reading : ReadingAt leg.actual targetEndpoint //
  QueryCache leg.actual targetEndpoint reading }}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) piece.lowerEndpoint}
variable {agreement : InitialAgreement piece.lowerEndpoint piece.source sourceOwner}

/-- The SAME actual paid Block's original source/target times satisfy the repeat-window depth-ten payment.

Only the retained original span/target incidence is used. The actual Block,
Geometry, factor preparations, source Reading and paid Owner handoffs are
unchanged, including its second L-edge's preceding source origin.
-/
theorem scheduled_route_width
    (retained : LayerBlock (regular := leg.regular) piece queried sourceOwner agreement) :
    (piece.span.lower - targetEndpoint.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10 :=
  retained.width_eq.trans_le
    (scheduled_piece_width data coarse initialPiece target sourceQueried atSource atFinish finishQuery piece member)

end Steps.Acquisition.Quarter.Input.Numerical

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
