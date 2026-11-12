module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Requested roots on the actual retained spatial-parent Point banks

The supplied completed move, primitive and covered-parent caches remain
original owners. The consumer constructs one ordered bank of actual signed
Points, then subsequent original root requests use its stored entries.
-/

namespace TestPurelib.Curves.Legendre.ParallelParentPoints

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Integration.Path.Dyadic
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
open Transport
open Transport.Spatial
open Parallel
open OwnerMoves
open Purelib.Curves.Legendre
open Periods
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {budget : OwnerBudget leg coarse (some bounds.timeRequest)}
variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : Gaussian.Equivalence.NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

variable {bank : Entries moves} {count : Nat}

/-- Retain actual shared-reference parent Points once and request their original signed roots at later paid accuracies.

The same stored cache row determines every bounded parent occurrence. One
returned original procedure performs an actual root request on that Point;
no cover, source preparation, Reference or parent-Point factory is invoked
inside this later request function.
-/
def requestedParentRoots (retained : Entries.Primitives bounds bank count) (factory : bank = entries moves)
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) :
    Σ points : {actual : Entries.Primitives.ParentPoints bounds retained factory frame differential sheet caches //
        actual = Entries.Primitives.parentPoints bounds retained factory frame differential sheet caches},
      (edge : Fin times.length) →
      (parent : Fin (DependentProduct.get times points.val.1.val edge).parents.length) →
      (stage : Nat) → (accuracy : AccuracyRequest) →
        Point.PrimitiveRoot
          (DependentProduct.get (DependentProduct.get times points.val.1.val edge).parents
            (DependentProduct.get times points.val.2 edge).2.val parent).1 stage accuracy.tolerance :=
  let points := Entries.Primitives.parentPoints bounds retained factory frame differential sheet caches
  ⟨⟨points, rfl⟩, fun edge parent stage accuracy =>
    let sample := (DependentProduct.get (DependentProduct.get times points.1.val edge).parents
      (DependentProduct.get times points.2 edge).2.val parent).1
    Point.selectPrimitiveRoot sample stage accuracy.tolerance accuracy.positive⟩

end TestPurelib.Curves.Legendre.ParallelParentPoints
