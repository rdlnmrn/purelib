module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
public import Purelib.Riemann.Periods.StandardPeriodAmbient
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison

open Purelib.Riemann.Periods.StandardPeriodAmbient

open Purelib.Riemann.Periods.StandardPeriodGridLines

open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid

open Purelib.RootIsolation.SquareRoot.Grid

public section

/-!
# Original period primitives on a coordinate-enlarged grid

Split the retained program's actual covered parents, not a newly prepared
walk. Root ownership stays in the original request and its sheet assignments.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes SplitPrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {original : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)} {point : Purelib.Data.Gaussian.Basic.Canonical}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval point)} {source :
    Differential genus}
  {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
    curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve branches higher}

/-- Every actual original period-stage parent lies on the coordinate-enlarged grid lines. -/
public theorem stage_lines (period : PreparedGridPeriodPrograms.PeriodWalk original point owner source)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex original point)
    (included : Extension.CoordinateInclusion original base.bank.grid) (stage : Nat) :
    Grid.ParentsOnLines base.bank.grid (period.state stage).state.parents := by
  apply ParentsOnLines.refinement (period.initial.statesSubedges (PreparedRefinementProgramCore.standardDifferentials
    genus) stage)
  rw [period.initial_eq, RootClosedWalk.initial_parents]
  exact Grid.prepared_onLines base.bank.grid source 0 period.closed.traced.prepared
    (included.path _ (period.closed.walk.vertices member))

/-- Every actual original period-stage parent retains endpoints inside the original curve ambient box. -/
public theorem stage_inside (period : PreparedGridPeriodPrograms.PeriodWalk original point owner source) (stage : Nat)
  :
    PreparedPolynomialSheetPropagation.EndpointsIn (Cuts.Ambient curve) (period.state stage).state.parents := by
  apply EndpointsIn.refinement (period.initial.statesSubedges (PreparedRefinementProgramCore.standardDifferentials
    genus) stage)
  rw [period.initial_eq, RootClosedWalk.initial_parents]
  exact PreparedPolynomialSheetPropagation.prepared_endpoints curve source 0 period.closed.traced.prepared

set_option genInjectivity false in
/-- The request is retained verbatim; only its finite geometric split uses the new grid. In particular the result
estimates the original period name. -/
structure IncludedFragments (period : PreparedGridPeriodPrograms.PeriodWalk original point owner source)
    (differential : Fin genus) (minimum : Nat) (target : Fraction.Rational) where
  /-- The exact original covered period request retained unchanged by this enlarged-grid split. -/ comparison :
    PreparedPrimitiveChargeBounds.CoveredPeriodRequest period.initial
    (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) genus minimum target
  /-- The cached finite splitting axes of the actual enlarged grid. -/ axes : PreparedPrimitiveSplits.PrimitiveAxes
    base.bank.grid
  /-- The actual finite splitting spine on the retained original covered request. -/ fragments :
    PreparedPrimitiveSplits.SplitPrimitiveRequest axes comparison.request
  /-- The retained regular-face placements of those exact original fragments. -/ cells :
    RegularFaces.RegularPrimitiveSplits (base := base) axes fragments.splits

constructive_injectivity IncludedFragments

namespace IncludedFragments

variable {period : PeriodWalk original point owner source}
  {differential : Fin genus} {minimum : Nat} {target : Rational}

/-- Split the supplied original period request using the enlarged grid's actual axes and retain all original request and
root ownership. -/
@[expose] def ofRequest (period : PreparedGridPeriodPrograms.PeriodWalk original point owner source)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex original point) (included :
      Extension.CoordinateInclusion original base.bank.grid)
    (comparison : PreparedPrimitiveChargeBounds.CoveredPeriodRequest period.initial
      (PreparedRefinementProgramCore.standardDifferentials genus)
      (PeriodMatrix.standardDifferential differential) genus minimum target) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments (base := base) period
      differential minimum target := by
  let axes := PrimitiveAxes.build base.bank.grid
  let fragments := SplitPrimitiveRequest.build axes comparison.request
  have inside : PreparedPolynomialSheetPropagation.EndpointsIn (Cuts.Ambient curve)
    (comparison.cover.retained.current.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply EndpointsIn.recast
    rw [comparison.cover.retained.current_eq]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.stage_inside period
      comparison.cover.stage
  have lines : Grid.ParentsOnLines base.bank.grid (comparison.cover.retained.current.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply ParentsOnLines.recast
    rw [comparison.cover.retained.current_eq]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.stage_lines period member included
      comparison.cover.stage
  let located := LocatedPrimitiveSplits.build base.bank axes fragments.splits (fun _ present => EndpointsIn.member
    inside present)
  exact ⟨comparison, axes, fragments, RegularPrimitiveSplits.build located lines⟩

/-- The retained fragment sum estimates the exact original period program at every stage meeting the original request.
-/
theorem accurate (split : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments (base :=
  base) period differential minimum target)
    (stage : Nat) (later : split.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (split.fragments.sum - ((period.program differential).integral.model
      stage).integralSample) < target := by
  rw [split.fragments.original_sum, period.program_model]
  exact split.comparison.accurate (PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials
    differential) stage later

/-- Existing sheet selection compares the actual parent roots with the new face frames; coordinate inclusion is not used
as a root-equality proof. -/
@[expose] def assign (split : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments
  (base := base) period differential minimum target)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) :
    Fragment.SplitSheets domains split.cells split.comparison.request.requests :=
  Fragment.SplitSheets.build domains split.cells split.comparison.request.requests

end IncludedFragments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
