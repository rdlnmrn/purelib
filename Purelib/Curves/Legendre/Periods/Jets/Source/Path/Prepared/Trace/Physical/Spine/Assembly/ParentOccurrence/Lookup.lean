module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence
import Purelib.Data.List.Flatten.Occurrence

/-! # Exact physical-Spine parent lookup retaining the original selected Segment

The same stored Flatten.Occurrence supplies its outer Segment and child
index. Original readonly selectors keep whole actual acquisition/source
tails and their original finish-Owner handoffs; no locator or producer runs.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

namespace PreparedParents.Trace.Physical.Spine.Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

variable {ambient : Geometry.Rational.Box}
variable {width : {start finish : Canonical} →
  ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
variable {start finish : Canonical}
variable (path : ClearPath (Paths.polynomial parameter) ambient start finish)
variable (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
variable (retained : Acquisition.Spine width path within owner)
variable (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width path within owner retained)
variable (index : Fin (assemble width path within owner retained kept).geometry.parents.length)
variable (position : Data.List.Flatten.Occurrence (parentWords width path within owner retained kept)
  (flattenedIndex path within owner retained kept index))

/-- Read the exact original Segment/child occurrence under this SAME physical-Spine source position.

The stored whole original tuple is selected directly. Parent equality
transports only the child interface; the original acquisition's TraceCache
and complete original head/tail factories retain its actual trace identity.
-/
@[expose] def parentOccurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets)
    ((assemble width path within owner retained kept).geometry.parents[index.val]'index.isLt) :=
  ⟨ambient, width, selected path within owner retained kept index position,
    ⟨child path within owner retained kept index position,
      parent_eq path within owner retained kept index position⟩⟩

/-- The entire original selected Segment/Parents/source tuple is the same readonly physical lookup result. -/
theorem parentOccurrence_selected :
    (parentOccurrence path within owner retained kept index position).selected =
      selected path within owner retained kept index position := by
  unfold parentOccurrence
  rfl

/-- The literal original child coordinate is retained without another flatten lookup or index search. -/
theorem parentOccurrence_child :
    (parentOccurrence path within owner retained kept index position).child =
      child path within owner retained kept index position := by
  unfold parentOccurrence
  rfl

/-- Exact parent occurrence keeps the complete original selected PreparedParent under the original assembly law. -/
theorem parentOccurrence_prepared_heq :
    HEq ((assemble width path within owner retained kept).prepared.entry index)
      ((parentOccurrence path within owner retained kept index position).selected.prepared.entry
        (parentOccurrence path within owner retained kept index position).child) :=
  prepared_heq path within owner retained kept index position

end PreparedParents.Trace.Physical.Spine.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
