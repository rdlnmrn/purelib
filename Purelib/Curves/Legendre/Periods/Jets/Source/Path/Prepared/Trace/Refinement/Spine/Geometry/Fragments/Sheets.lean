module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Fragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Original shared-domain sheet assignments on actual retained child fragments

The chosen lifted grid supplies its SAME existing root frames. One shared
face-domain bank assigns every actual fragment of the original child
request through the existing root-based sheet constructor. The full input
fragment/request cache, domain bank and assignment outcome stay retained;
coordinate inclusion and numerical sheet labels supply no root identity.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

namespace Fragments

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment (SplitSheets)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {originalGrid : ClearGrid (Paths.polynomial parameter) (Ambient (Fibre.frameCurve frame))}
variable {point : Canonical} {owner : Owner ((Paths.polynomial parameter).eval point)}
variable {period : PeriodWalk (curve := Fibre.frameCurve frame) originalGrid point owner basis}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) point owner point
  (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
variable {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational}
variable {positive : 0 < diameter}
variable {retained : Materialized.Geometry (count := count)
  diameter positive period.closed.traced.lineage inputCenters materialized factory}
variable {canonical : inputCenters = Centers.build period.closed.traced.lineage}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {member : ContainsVertex originalGrid point}
variable {included : CoordinateInclusion originalGrid framed.bank.grid}
variable {target : Rational} {supplied : ControlledSumRequest retained.parents count target}

/-- The complete original fragment/request cache, SAME shared bank and root-based assignment with whole factories.

This exact product retains both supplied inputs as values before the
original SplitSheets producer runs. Its original parent-to-sample root
proofs, selected face entries, actual domains and ordered analytic splits
stay in their existing constructors, including repeated/stationary slots.
-/
@[expose] def Assigned {frames : RootFrames framed.bank.grid}
    (givenDomains : FaceDomainBank frames framed.faces.regulars)
    (actual : Fragments owner period retained canonical member included supplied) : Type 2 :=
  (kept : {value : Fragments owner period retained canonical member included supplied // value = actual}) ×
  (bank : {value : FaceDomainBank frames framed.faces.regulars // value = givenDomains}) ×
  {value : SplitSheets bank.val kept.val.regular kept.val.request.requests //
    value = SplitSheets.build bank.val kept.val.regular kept.val.request.requests}

/-- Assign every SAME retained child fragment using one GIVEN shared face-domain bank.

Only the existing SplitSheets.build algorithm executes. Both complete
input caches are bound first and forwarded unchanged, so later requests
can reuse their actual sheet entries and domains without replaying this
assignment or replacing a supplied bank by a newly constructed one.
-/
def assign {frames : RootFrames framed.bank.grid}
    (givenDomains : FaceDomainBank frames framed.faces.regulars)
    (actual : Fragments owner period retained canonical member included supplied) : Assigned givenDomains actual :=
  let kept : {value : Fragments owner period retained canonical member included supplied // value = actual} :=
    ⟨actual, rfl⟩
  let bank : {value : FaceDomainBank frames framed.faces.regulars // value = givenDomains} := ⟨givenDomains, rfl⟩
  let sheets : {value : SplitSheets bank.val kept.val.regular kept.val.request.requests //
    value = SplitSheets.build bank.val kept.val.regular kept.val.request.requests} :=
    ⟨SplitSheets.build bank.val kept.val.regular kept.val.request.requests, rfl⟩
  ⟨kept, bank, sheets⟩

/-- Build one actual domain bank from the GIVEN lifted grid's retained frames, then share it with the same assignment.

Original FaceDomainBank.build delays each regular face and sheet until
needed. Its clearance-driven model/domain constructors are total on the
supplied certified regular faces. No vertex/root frame, edge bank, geometry
or source request is reacquired. Consumers with an existing bank use assign.
-/
def withDomains (lifted : LiftedPuncturedGrid framed)
    (actual : Fragments owner period retained canonical member included supplied)
    {Result : Type u}
    (consume : (domains : FaceDomainBank lifted.frames framed.faces.regulars) →
      domains = FaceDomainBank.build lifted.frames framed.faces.regulars → Assigned domains actual → Result) : Result :=
  let domains : {value : FaceDomainBank lifted.frames framed.faces.regulars //
    value = FaceDomainBank.build lifted.frames framed.faces.regulars} :=
    ⟨FaceDomainBank.build lifted.frames framed.faces.regulars, rfl⟩
  let assigned := assign domains.val actual
  consume domains.val domains.property assigned

namespace Assigned

variable {frames : RootFrames framed.bank.grid} {givenDomains : FaceDomainBank frames framed.faces.regulars}
variable {actual : Fragments owner period retained canonical member included supplied}
variable (assigned : Assigned givenDomains actual)

/-- Read the SAME retained original fragment/request caches. -/
@[expose] def fragments : Fragments owner period retained canonical member included supplied := assigned.1.val

/-- The full fragment/request cache is exactly the given original value. -/
theorem fragments_eq : assigned.fragments = actual := assigned.1.property

/-- Read the SAME complete shared face-domain bank. -/
@[expose] def domains : FaceDomainBank frames framed.faces.regulars := assigned.2.1.val

/-- The whole shared bank remains exactly the given original bank. -/
theorem domains_eq : assigned.domains = givenDomains := assigned.2.1.property

/-- Read every actual assigned sample/entry/domain/split in its original fragment order. -/
@[expose] def sheets : SplitSheets assigned.domains assigned.fragments.regular assigned.fragments.request.requests :=
  assigned.2.2.val

/-- The assignment is the whole original constructor on the SAME retained bank, fragments and requests. -/
theorem sheets_eq : assigned.sheets =
    SplitSheets.build assigned.domains assigned.fragments.regular assigned.fragments.request.requests :=
  assigned.2.2.property

end Assigned

end Fragments

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
