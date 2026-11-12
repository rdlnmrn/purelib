module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-!
# Grid fragments of the retained corrected A/B periods

The actual canonical parents inherit the original grid-line support through
accepted preparation and root-subedge refinement. Covered requests split
those same parents into regular-face fragments. Sheet assignment compares
their retained roots with the supplied original face-domain bank.

The B construction consumes the whole corrected walk, including its preceding
A prefix. These operations do not identify an independently transported
physical cycle with either canonical cycle.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment (SplitSheets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments (IncludedFragments)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Periods.StandardPeriodGridLines

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}

/-- Every actual scheduled A parent lies on an original retained grid line. -/
theorem a_stage_onLines (prepared : Prepared paired) (index : Fin genus) (stage : Nat) :
    Grid.ParentsOnLines base.bank.grid ((prepared.aWalk index).state stage).state.parents :=
  PeriodFragments.stage_lines (base := base) (source := standardDifferential index) (prepared.aWalk index)
    (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet))
    (CoordinateInclusion.refl base.bank.grid) stage

/-- Every actual corrected B parent retains its original grid-line support.

The schedule refines the complete corrected B walk, so all preceding A
occurrences remain present in their original order and orientation.
-/
theorem b_stage_onLines (prepared : Prepared paired) (index : Fin genus) (stage : Nat) :
    Grid.ParentsOnLines base.bank.grid ((prepared.bWalk index).state stage).state.parents :=
  PeriodFragments.stage_lines (base := base) (source := standardDifferential index) (prepared.bWalk index)
    (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet))
    (CoordinateInclusion.refl base.bank.grid) stage

/-- Acquire and split a controlled request on the actual retained A schedule.

The covered ancestor, primitive request, splitting axes and regular-face
placements are retained in the original IncludedFragments cache. The
minimum stage and numerical request floor are independent inputs.
-/
def aFragments (prepared : Prepared paired) (differential index : Fin genus)
    (minimum : Nat) (target : Rational) (positive : 0 < target) (minimumIndex : Nat := 0) :
    IncludedFragments (base := base) (prepared.aWalk index) differential minimum target :=
  let comparison := CoveredPeriodRequest.acquire (prepared.aWalk index).initial
    (standardDifferentials genus) (standardDifferential differential) genus minimum target positive minimumIndex
  IncludedFragments.ofRequest (prepared.aWalk index)
    (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet))
    (CoordinateInclusion.refl base.bank.grid) comparison

/-- Acquire and split a controlled request on the complete corrected B schedule.

The actual B programme's covered parents, ordered repeated occurrences,
root requests and preceding A prefix are retained without preparing a new
reference tour or replacing its source owner.
-/
def bFragments (prepared : Prepared paired) (differential index : Fin genus)
    (minimum : Nat) (target : Rational) (positive : 0 < target) (minimumIndex : Nat := 0) :
    IncludedFragments (base := base) (prepared.bWalk index) differential minimum target :=
  let comparison := CoveredPeriodRequest.acquire (prepared.bWalk index).initial
    (standardDifferentials genus) (standardDifferential differential) genus minimum target positive minimumIndex
  IncludedFragments.ofRequest (prepared.bWalk index)
    (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet))
    (CoordinateInclusion.refl base.bank.grid) comparison

/-- Retain one actual A fragment cache and its original root-based sheet assignment.

The supplied domain bank is shared by every fragment. Its sheet comparisons
consume the same original controlled request stored in the retained cache;
coordinate inclusion supplies no root-equivalence premise.
-/
def aFragmentSheets (prepared : Prepared paired) (differential index : Fin genus)
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (minimum : Nat) (target : Rational) (positive : 0 < target) (minimumIndex : Nat := 0) :
    (split : IncludedFragments (base := base) (prepared.aWalk index) differential minimum target) ×
      SplitSheets domains split.cells split.comparison.request.requests :=
  let split := prepared.aFragments differential index minimum target positive minimumIndex
  ⟨split, split.assign domains⟩

/-- Retain one corrected B fragment cache and its original root-based sheet assignment.

Both components retain the complete corrected B occurrences and their
actual local primitive requests, including the preceding A prefix.
-/
def bFragmentSheets (prepared : Prepared paired) (differential index : Fin genus)
    (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (minimum : Nat) (target : Rational) (positive : 0 < target) (minimumIndex : Nat := 0) :
    (split : IncludedFragments (base := base) (prepared.bWalk index) differential minimum target) ×
      SplitSheets domains split.cells split.comparison.request.requests :=
  let split := prepared.bFragments differential index minimum target positive minimumIndex
  ⟨split, split.assign domains⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
