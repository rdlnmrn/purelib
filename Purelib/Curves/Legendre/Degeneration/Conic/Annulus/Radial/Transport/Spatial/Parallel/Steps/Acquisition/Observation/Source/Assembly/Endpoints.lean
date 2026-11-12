module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source.Assembly
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence.Lookup
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.Fin
import Purelib.Data.List.Append
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence

/-! # Original physical endpoint occurrence below an old retained Block Entry

The original Entry supplies its same complete Block/source pair and whole
input equality. Structural descent follows the exact old target and paid
source tails. One new readonly physical lookup chooses the local Segment;
no old producer or observation is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes
open Purelib.Data.List
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

namespace Steps.Acquisition.Observation.Blocks.Sources.Entry

/-- Select the original physical Segment/child under a supplied retained old Block Entry.

The head consumes the whole original pair equation to transport only its
parent bound. The original physical locator runs once on that actual
child. A successor follows the exact stored finishOwner/nextAgreement
and source tail, keeping earlier source Reading/Samples unchanged.
-/
def physicalOccurrence : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (outer : Fin
      (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).length) →
    Entry targets current reading originalOwner original sourceOwner agreement paid sources outer →
    (child : Fin ((parentWords targets current reading originalOwner original sourceOwner agreement paid sources)[
      outer.val]'outer.isLt).length) →
    Spine.Sources.ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := sourceTargets)
      (((parentWords targets current reading originalOwner original sourceOwner agreement paid sources)[
        outer.val]'outer.isLt)[child.val]'child.isLt)
  | [] => fun _ _ _ _ _ _ _ _ outer => Fin.elim0 outer
  | target :: targets => fun current reading originalOwner original sourceOwner agreement paid sources outer =>
      Data.Fin.casesDependent
        (motive := fun selectedIndex : Fin (parentWords (target :: targets) current reading originalOwner
            original sourceOwner agreement paid sources).length =>
          Entry (target :: targets) current reading originalOwner original sourceOwner agreement
            paid sources selectedIndex →
          (child : Fin ((parentWords (target :: targets) current reading originalOwner original
            sourceOwner agreement paid sources)[selectedIndex.val]'selectedIndex.isLt).length) →
          Spine.Sources.ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
            (sheet := sheet) (targets := sourceTargets)
            (((parentWords (target :: targets) current reading originalOwner original sourceOwner agreement
              paid sources)[selectedIndex.val]'selectedIndex.isLt)[child.val]'child.isLt))
        (fun picked child => by
          let width : {start finish : Canonical} →
              ClearSegment (Paths.polynomial parameter) (Factors.sourceBox paid.head.anchor) start finish →
                AccuracyRequest :=
            fun {_start _finish} segment => widthRequest paid.head.anchor segment
          let actual := Spine.Sources.assemble width original.headGeometry.route.path
            original.headGeometry.route.within sourceOwner paid.head.paid.spine picked.val.2
          have same := congrArg (fun kept => (Spine.Sources.assemble width original.headGeometry.route.path
            original.headGeometry.route.within sourceOwner paid.head.paid.spine kept).geometry.parents)
            (congrArg Prod.snd picked.property)
          let localIndex : Fin actual.geometry.parents.length :=
            ⟨child.val, Eq.mpr (congrArg (fun word => child.val < word.length) same) child.isLt⟩
          let position := Spine.Sources.locate original.headGeometry.route.path
            original.headGeometry.route.within sourceOwner paid.head.paid.spine picked.val.2 localIndex
          let selected := Spine.Sources.parentOccurrence original.headGeometry.route.path
            original.headGeometry.route.within sourceOwner paid.head.paid.spine picked.val.2 localIndex position
          have parentEq := getElem_congr same (i := localIndex.val) (j := child.val) rfl localIndex.isLt
          exact selected.castParent parentEq)
        (fun next picked child => physicalOccurrence targets target original.nextReading
          original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement
          paid.tail sources.2 next picked child) outer
termination_by structural targets => targets

end Steps.Acquisition.Observation.Blocks.Sources.Entry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
