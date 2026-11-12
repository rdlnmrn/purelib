module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine
public import Purelib.Polynomial.Geometry.ClearPath.Distance
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Distance
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Data.List.Membership

/-! # Actual source-query distance payments through the retained acquisition spine

The proof follows the SAME original ClearPath, paid Segment and source-family
spines. Every head uses its stored canonical centers, covered parents and
actual PreparedParents coordinate cache. The original head finish Owner
indexes the unchanged tail. No preparation or observation is executed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

namespace Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Every literal source-model query point of every actual retained paid edge obeys one whole-source distance bound. -/
@[expose] def DistanceBound (center : Canonical) (bound : Rational)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained → Prop
  | _, _, .nil _, _, _, _, _ => True
  | _, _, .cons _head tail, within, _owner, retained, sources =>
      (∀ index : Fin sources.1.covered.parents.length, ∀ fraction : Rational,
        0 ≤ fraction ∧ fraction ≤ 1 →
          Norm.Basic.normSq (center -
            (sources.2.1.entry index).preparation.cell.models.coordinate.point fraction) ≤ bound) ∧
        DistanceBound center bound width tail within.tail retained.1.traced.finishOwner retained.2 sources.2.2
termination_by structural _ _ path _ _ _ _ => path

/-- Carry the actual original path payment through the SAME stored parent/source and finish-owner handoff spines. -/
theorem distanceBound (center : Canonical) (bound : Rational)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :
    ∀ {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
      (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
      (retained : Acquisition.Spine width path within owner)
      (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (targets := targets) width path within owner retained),
      ClearPath.PointBound center bound path → DistanceBound center bound width path within owner retained sources
  | _, _, .nil _, _, _, _, _, _ => True.intro
  | _, _, .cons _head tail, within, _owner, retained, sources, paid => by
      constructor
      · intro index fraction inside
        rewrite [(sources.2.1.entry index).queryPoint_eq fraction]
        exact sources.1.point_distance_le paid.1 _ (List.getElem_mem index.isLt) fraction inside
      · exact distanceBound center bound width tail within.tail retained.1.traced.finishOwner retained.2
          sources.2.2 paid.2
termination_by structural _ _ path _ _ _ _ _ => path

variable {center : Canonical} {bound : Rational}
variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start middle finish : Canonical}
variable {firstEdge : ClearSegment (Paths.polynomial parameter) ambient start middle}
variable {restPath : ClearPath (Paths.polynomial parameter) ambient middle finish}
variable {within : (ClearPath.cons firstEdge restPath).WithinAmbient}
variable {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {retained : Acquisition.Spine width (.cons firstEdge restPath) within owner}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width (.cons firstEdge restPath) within owner retained}

/-- Read the physical payment for an actual retained source query on this SAME acquired head and bounded occurrence. -/
theorem DistanceBound.head
    (paid : DistanceBound center bound width (.cons firstEdge restPath) within owner retained sources)
    (index : Fin sources.1.covered.parents.length) (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq (center -
      (sources.2.1.entry index).preparation.cell.models.coordinate.point fraction) ≤ bound :=
  paid.1 index fraction inside

/-- Pass the SAME actual tail sources their derived payment at the literal stored first finish Owner. -/
theorem DistanceBound.tail
    (paid : DistanceBound center bound width (.cons firstEdge restPath) within owner retained sources) :
    DistanceBound center bound width restPath within.tail retained.1.traced.finishOwner retained.2 sources.2.2 := paid.2

end Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

end
