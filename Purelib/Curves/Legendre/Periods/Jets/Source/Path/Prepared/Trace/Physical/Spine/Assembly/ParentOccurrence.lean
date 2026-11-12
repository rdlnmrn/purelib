module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison.EndpointQueries
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Approximation.Gaussian.Equivalence

/-! # Original physical-segment occurrence and primitive endpoint result

A centered parent may come from different retained ambient/width owners.
Existing Sigma containers retain those indices and the whole original
SegmentSources value with its literal child index. This is a lookup view,
not a new trace, root Owner, observation or source preparation cache.
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
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

namespace ParentOccurrence

/-- The original physical width-request family on one retained sharp ambient. -/
@[expose] def Width (ambient : Geometry.Rational.Box) : Type :=
  {start finish : Canonical} →
    ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest

/-- The whole original physical source tuple under its retained width family. -/
@[expose] def Selected {ambient : Geometry.Rational.Box} (width : Width (parameter := parameter) ambient) : Type _ :=
  SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) width

/-- The original bounded child and exact whole-parent incidence in one retained source tuple. -/
@[expose] def Child {ambient : Geometry.Rational.Box} {width : Width (parameter := parameter) ambient}
    (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (selected : Selected (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width) : Type :=
  { child : Fin selected.parents.covered.parents.length //
    parent = selected.parents.covered.parents[child.val]'child.isLt }

end ParentOccurrence

/-- One literal selected SegmentSources and original child incidence, retaining its actual ambient and width owner.

SegmentSources already owns the whole acquired Segment, Parents and source
product. The outer two Sigma indices expose the original ambient and width
when lookup crosses Blocks with different sharp boxes. No field of a root
Owner, trace or observation is copied into a replacement representation.
-/
@[expose] def ParentOccurrence (parent : CenteredEdge (Fibre.frameCurve frame) basis) :=
  Σ ambient : Geometry.Rational.Box,
    Σ width : ParentOccurrence.Width (parameter := parameter) ambient,
      Σ selected : ParentOccurrence.Selected (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) width,
        ParentOccurrence.Child parent selected

namespace ParentOccurrence

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) parent)

/-- Read the actual original sharp ambient of this selected acquired Segment. -/
@[expose] def ambient : Geometry.Rational.Box := occurrence.1

/-- Read the same original physical width-request family, retaining its complete actual closure. -/
@[expose] def width : Width (parameter := parameter) occurrence.ambient := occurrence.2.1

/-- Read the whole existing acquired Segment/Parents/source tuple without running any producer. -/
@[expose] def selected : Selected (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) occurrence.width := occurrence.2.2.1

/-- Read the exact original selected centered-child position. -/
@[expose] def child : Fin occurrence.selected.parents.covered.parents.length := occurrence.2.2.2.val

/-- The displayed aggregate parent is the entire original selected child, not merely its coordinate or root name. -/
theorem parent_eq : parent = occurrence.selected.parents.covered.parents[
    occurrence.child.val]'occurrence.child.isLt := occurrence.2.2.2.property

/-- Transport only the exact whole-parent index of this same selected occurrence view. -/
@[expose] def castParent {next : CenteredEdge (Fibre.frameCurve frame) basis} (equal : parent = next) :
    ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) next := by
  cases equal
  exact occurrence

/-- Whole-parent transport retains the complete original selected tuple and child occurrence heterogeneously. -/
theorem castParent_heq {next : CenteredEdge (Fibre.frameCurve frame) basis} (equal : parent = next) :
    HEq (occurrence.castParent equal) occurrence := by
  cases equal
  rfl

/-- Retain the actual endpoint comparison result and its derived relation to one SAME original primitive Point. -/
@[expose] def PointResult {localCount : Nat} {target : Rational}
    (request : LocalRequest parent localCount target)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point 1)) :=
  Σ endpoint : Comparison.Cache.EndpointResult parent,
    NamedEquivalent (ownerName endpoint.1) sample.certificate.value.name

end ParentOccurrence

end PreparedParents.Trace.Physical.Spine.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
