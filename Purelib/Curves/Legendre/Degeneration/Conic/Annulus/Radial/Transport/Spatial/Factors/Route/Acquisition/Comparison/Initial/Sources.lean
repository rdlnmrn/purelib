module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold.Entry.Sources
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Acquired
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Data.List.Membership
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Actual original factor origins at retained paid physical source occurrences

The First operation reads the original ordinary Fold. The Second operation
reads the same stored cross-segment Entry, preserving its preceding terminal
Reading/Samples on the first child. Actual Parents centers are transported
only by the original whole traced_prepared_eq. No source or factor query,
request, observation or preparation factory is replayed. Existing operational
comparison machinery constructs the required certificates on those same inputs.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Fold

namespace Route.Acquisition.Comparison.Initial

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates centeredEdges centeredEdges_point_zero CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.RootContinuation
open Segment.Reading.Payment

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {entry : Initial source}
variable {middle finish : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive reference) middle}
variable {headWithin : head.WithinAmbient} {headFactors : Segment budgets head headWithin}
variable {headPaid : CoveredTracedPath.Acquisition.Segment (segment := head) (within := headWithin)
  (owner := entry.owner) (widthRequest anchor head)}
variable {second : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) middle finish}
variable {secondWithin : second.WithinAmbient} {secondFactors : Segment budgets second secondWithin}
variable {secondPaid : CoveredTracedPath.Acquisition.Segment (segment := second) (within := secondWithin)
  (owner := headPaid.traced.finishOwner) (widthRequest anchor second)}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2} {count : Nat}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace First

variable (retained : First entry headFactors headPaid)
variable (parents : CoveredTracedPath.Acquisition.Segment.Parents (curve := Fibre.frameCurve frame)
  basis sheet count headPaid)
variable (index : Fin parents.covered.parents.length)

/-- Read the literal old factor source Reading at this SAME retained physical moving-child occurrence. -/
@[expose] def sourceReading :=
  Fold.Cache.sourceReadingAt (frame := frame) (basis := basis) (sheet := sheet) (completed := headFactors)
    headPaid.prepared.budget.trace
    (Acquisition.Initial.Result.fold (completed := headFactors) (suppliedOwner := entry.owner)
      (suppliedAgreement := Acquisition.Initial.ownerAgreement entry.owner entry.equivalent)
      (suppliedPaid := headPaid.prepared.paid) retained)
    parents.acquiredCenters (parents.acquiredIndex index)

/-- Read the complete old Samples at the SAME source Reading, retaining both factor requests and product state. -/
@[expose] def sourceSamples : RequestedSamples (anchor := anchor) (sourceReading retained parents index) :=
  Fold.Cache.sourceSamplesAt (frame := frame) (basis := basis) (sheet := sheet) (completed := headFactors)
    headPaid.prepared.budget.trace
    (Acquisition.Initial.Result.fold (completed := headFactors) (suppliedOwner := entry.owner)
      (suppliedAgreement := Acquisition.Initial.ownerAgreement entry.owner entry.equivalent)
      (suppliedPaid := headPaid.prepared.paid) retained)
    parents.acquiredCenters (parents.acquiredIndex index)

/-- The exact retained source child query agrees with its actual old factor Reading through the SAME ordinary Fold. -/
def sourceEquivalent :
    NamedEquivalent
      ((parents.covered.parents[index.val]'index.isLt).edge.rootName 0
        (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
      (sourceReading retained parents index).values.value.name := by
  have names := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) (parents.acquiredParent_eq index)
  exact NamedEquivalent.transport names.symm rfl
    (Fold.Cache.sourceEquivalentAt (frame := frame) (basis := basis) (sheet := sheet) (completed := headFactors)
      headPaid.prepared.budget.trace
      (Acquisition.Initial.Result.fold (completed := headFactors) (suppliedOwner := entry.owner)
        (suppliedAgreement := Acquisition.Initial.ownerAgreement entry.owner entry.equivalent)
        (suppliedPaid := headPaid.prepared.paid) retained)
      parents.acquiredCenters (parents.acquiredIndex index))

/-- The actual retained first-edge source Reading occurs at the SAME literal original child's physical point. -/
theorem sourcePoint_eq :
    head.pointAt
      ((centeredEdges (Fibre.frameCurve frame) basis sheet headPaid.prepared.acquired.prepared.subdivision
        parents.acquiredCenters)[(parents.acquiredIndex index).val]'
          (parents.acquiredIndex index).isLt).parameterEdge.left.parameter =
      (parents.covered.parents[index.val]'index.isLt).edge.point 0 := by
  have original := centeredEdges_point_zero (Fibre.frameCurve frame) basis sheet
    headPaid.prepared.acquired.prepared.subdivision parents.acquiredCenters _
    (List.getElem_mem (parents.acquiredIndex index).isLt)
  have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point 0)
    (parents.acquiredParent_eq index)
  exact original.symm.trans same.symm

variable {floor : Nat} {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets path stage}
variable {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
  (parents.covered.parents[index.val]'index.isLt)}
variable {inside : (patch.neighborhood count).box.Contains
  ((parents.covered.parents[index.val]'index.isLt).edge.point 1)}

/-- The literal old prepared source sample agrees with its actual first-edge factor origin without observer replay. -/
def sourceSampleEquivalent (prepared : PreparedParent patch count floor inside targets) :
    NamedEquivalent prepared.firstSample.certificate.value.name
      (sourceReading retained parents index).values.value.name :=
  prepared.firstQueryEquivalent.symm.trans (sourceEquivalent retained parents index)

end First

namespace Second

variable {firstResult : First entry headFactors headPaid}
variable (retained : Second entry headFactors headPaid secondFactors secondPaid firstResult)
variable (parents : CoveredTracedPath.Acquisition.Segment.Parents (curve := Fibre.frameCurve frame)
  basis sheet count secondPaid)
variable (index : Fin parents.covered.parents.length)

/-- Read the exact original second-edge source origin, keeping preceding Reading/Samples on its initial child. -/
@[expose] def sourceAt :=
  Fold.Entry.Cache.sourceAt (frame := frame) (basis := basis) (sheet := sheet) (completed := secondFactors)
    (terminal entry retained).1 (terminal entry retained).2.1 secondPaid.prepared.budget.trace
    retained.2.val parents.acquiredCenters (parents.acquiredIndex index)

/-- Read the SAME full-cubic source channel of the actual preceding or current second-edge origin. -/
@[expose] def sourceChannel :=
  Fold.Entry.Cache.SourceAt.channel (terminal entry retained).1 (sourceAt retained parents index)

/-- Read the SAME OLD product observation at that actual origin, retaining its original requests, state and radius. -/
@[expose] def sourceProduct :=
  Fold.Entry.Cache.SourceAt.product (terminal entry retained).1 (sourceAt retained parents index)

/-- The exact original second-edge child query agrees with the retained origin selected by its actual Entry cache. -/
def sourceEquivalent :
    NamedEquivalent
      ((parents.covered.parents[index.val]'index.isLt).edge.rootName 0
        (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
      (sourceChannel retained parents index).name := by
  have names := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) (parents.acquiredParent_eq index)
  exact NamedEquivalent.transport names.symm rfl
    (Fold.Entry.Cache.SourceAt.equivalent (terminal entry retained).1 (sourceAt retained parents index))

/-- The actual second-edge source origin retains the literal moving child's physical point across the original corner.

The initial child consumes the stored previous-terminal point equality;
its full previous Reading/Samples remain the actual origin. Successors use
the unchanged original tail. No new-segment Reading is substituted.
-/
theorem sourcePoint_eq :
    Fold.Entry.Cache.SourceAt.point (terminal entry retained).1 (sourceAt retained parents index) =
      (parents.covered.parents[index.val]'index.isLt).edge.point 0 := by
  have actual := Fold.Entry.Cache.sourceAt_point_eq (frame := frame) (basis := basis) (sheet := sheet)
    (completed := secondFactors) (terminal entry retained).1 (terminal entry retained).2.1
    secondPaid.prepared.budget.trace retained.2.val parents.acquiredCenters (parents.acquiredIndex index)
  have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point 0)
    (parents.acquiredParent_eq index)
  exact actual.trans same.symm

variable {floor : Nat} {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets path stage}
variable {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
  (parents.covered.parents[index.val]'index.isLt)}
variable {inside : (patch.neighborhood count).box.Contains
  ((parents.covered.parents[index.val]'index.isLt).edge.point 1)}

/-- The actual old source sample agrees with its unchanged second-edge origin through the original query certificate. -/
def sourceSampleEquivalent (prepared : PreparedParent patch count floor inside targets) :
    NamedEquivalent prepared.firstSample.certificate.value.name (sourceChannel retained parents index).name :=
  prepared.firstQueryEquivalent.symm.trans (sourceEquivalent retained parents index)

end Second

end Route.Acquisition.Comparison.Initial

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

end
