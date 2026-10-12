module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.StandardPeriodAmbient
import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.StandardPeriodAmbient

open Purelib.Riemann.Periods.StandardPeriodGridLines

open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

public section

/-!
# Actual cut-grid fragments of the retained standard period primitives

The A/B primitive bank is split using this intersection row's existing grid.
Both sums retain their exact standard-period estimates, at the same common
tail. Identifying these fragments with shared face-word values still requires
sheet-aware local comparison; splitting alone does not assert that identity.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow (PrimitiveComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes SplitPrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation (EndpointsIn)
open Purelib.Riemann.Periods.StandardPeriodAmbient.EndpointsIn (recast member)
open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid (ParentsOnLines)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
/-- One shared axis cache and the two actual original-parent splitting spines. No alternative grid, tour pair, or period
program enters. -/
structure GridFragments (comparison : IntersectionRow.PrimitiveComparison row differential minimum target) where
  /-- The cached splitting axes on the exact original retained grid. -/ axes : PreparedPrimitiveSplits.PrimitiveAxes
    base.bank.grid
  /-- The retained splitting spine for the exact original A primitive request. -/ a :
    PreparedPrimitiveSplits.SplitPrimitiveRequest axes comparison.a.request
  /-- The retained splitting spine for the exact original B primitive request. -/ b :
    PreparedPrimitiveSplits.SplitPrimitiveRequest axes comparison.b.request
  /-- The retained regular-face locations of every actual A primitive fragment. -/ aCells :
    RegularFaces.RegularPrimitiveSplits (base := base) axes a.splits
  /-- The retained regular-face locations of every actual B primitive fragment. -/ bCells :
    RegularFaces.RegularPrimitiveSplits (base := base) axes b.splits

constructive_injectivity GridFragments

namespace GridFragments

variable {comparison :
  PrimitiveComparison row
  differential minimum target}

/-- Split both original period requests with one shared grid-axis cache and retain their actual regular-face placements.
-/
@[expose] def build (comparison : IntersectionRow.PrimitiveComparison row differential minimum target) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments comparison := by
  let axes := PrimitiveAxes.build base.bank.grid
  let a := SplitPrimitiveRequest.build axes comparison.a.request
  let b := SplitPrimitiveRequest.build axes comparison.b.request
  have aInside : PreparedPolynomialSheetPropagation.EndpointsIn (Cuts.Ambient curve)
      (comparison.a.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply EndpointsIn.recast
    rw [comparison.a.cover.retained.current_eq]
    exact IntersectionRow.a_stage_ambient row comparison.a.cover.stage
  have bInside : PreparedPolynomialSheetPropagation.EndpointsIn (Cuts.Ambient curve)
      (comparison.b.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply EndpointsIn.recast
    rw [comparison.b.cover.retained.current_eq]
    exact IntersectionRow.b_stage_ambient row comparison.b.cover.stage
  have aLines : Grid.ParentsOnLines base.bank.grid
      (comparison.a.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply ParentsOnLines.recast
    rw [comparison.a.cover.retained.current_eq]
    exact IntersectionRow.a_stage_onLines row comparison.a.cover.stage
  have bLines : Grid.ParentsOnLines base.bank.grid
      (comparison.b.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) := by
    apply ParentsOnLines.recast
    rw [comparison.b.cover.retained.current_eq]
    exact IntersectionRow.b_stage_onLines row comparison.b.cover.stage
  let aLocated := LocatedPrimitiveSplits.build base.bank axes a.splits (fun _ member => EndpointsIn.member aInside
    member)
  let bLocated := LocatedPrimitiveSplits.build base.bank axes b.splits (fun _ member => EndpointsIn.member bInside
    member)
  exact ⟨axes, a, b, RegularPrimitiveSplits.build aLocated aLines, RegularPrimitiveSplits.build bLocated bLines⟩

/-- The actual A fragment sum satisfies the original period estimate at every stage above the retained common tail. -/
theorem a_accurate (fragments : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments
  comparison) (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (fragments.a.sum -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target := by
  rw [fragments.a.original_sum]
  exact comparison.a_accurate stage later

/-- The actual B fragment sum satisfies the original period estimate at every stage above that same common tail. -/
theorem b_accurate (fragments : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments
  comparison) (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (fragments.b.sum -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target := by
  rw [fragments.b.original_sum]
  exact comparison.b_accurate stage later

set_option genInjectivity false in
/-- Both unchanged standard requests use the same retained face-domain bank, with a certified operational sheet and
complete analytic-cell split for every original fragment. -/
structure SheetAssignments (fragments : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments
  comparison)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) : Type 2 where
  /-- The actual A fragments' retained sheet entries on the original shared domain bank. -/ a :
    Fragment.SplitSheets domains fragments.aCells comparison.a.request.requests
  /-- The actual B fragments' retained sheet entries on that same original domain bank. -/ b :
    Fragment.SplitSheets domains fragments.bCells comparison.b.request.requests

constructive_injectivity SheetAssignments

/-- Assign every actual A/B fragment its operational sheet and analytic-cell split on the supplied retained face
domains. -/
@[expose] def assign (fragments : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments
  comparison)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) :
      SheetAssignments fragments
      domains :=
  ⟨Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.build domains fragments.aCells
    comparison.a.request.requests,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.build domains fragments.bCells
      comparison.b.request.requests⟩

end GridFragments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
