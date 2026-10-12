module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveSide
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedPrimitiveRequest
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public section

/-! Full paired primitive samples on the retained all-hole excision paths.
These are the actual parent caches of the sewn annuli; no independent tour
is prepared. Density charges remain explicit until the geometric budget and
transport to the shared face traces have been paid. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedPrimitiveRequest.Lifted.OuterPreparation
open Purelib.Data.Rat
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
  (PairedAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedAnnulus

/-- Retain both complete summaries and their endpoint discrepancy certificate, alongside the full primitive area bound
on this very annulus. -/
@[expose] def PrimitiveSample (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains) (error :
  Fraction.Rational) :=
  { sample : RequestedNewtonPrimitiveSide.FullAreaRequest
      (entry.source.outer.band first) (PeriodMatrix.standardDifferential second) genus
      entry.sewn.comparison.left.parents.parents error //
    Data.Gaussian.Norm.Basic.normSq sample.2.2.2.val.areaValue ≤
      2 * (error + Comparison.pairedDensityCharge entry.sewn.comparison.left second) }

/-- Acquire the full paired primitive summaries on the exact original annular parent cache, retaining the explicit
density-charge area bound. -/
@[expose] def samplePrimitives (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains)
    (error : Fraction.Rational) (positive : 0 < error) :
      PrimitiveSample entry error :=
  let sample := Comparison.pairedPrimitiveRequest entry.sewn.comparison.left second error positive
  ⟨sample, Comparison.paired_primitive_area_bound entry.sewn.comparison.left second sample⟩

end PairedAnnulus

namespace PairedComparison

variable {excision : AllHoleExcision request.single.grid
  lifted}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision}

/-- Every retained annulus is sampled once, preserving its position and source payload. The result cannot silently omit
a hole or substitute another path. -/
@[expose] def samplePrimitives (comparison : PairedComparison prepared first second domains)
    (error : Fraction.Rational) (positive : 0 < error) :
    { samples : List ((entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains) ×
        Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples.PairedAnnulus.PrimitiveSample entry error) //
          samples.map Sigma.fst = comparison.entries } := by
  let samples := comparison.entries.map fun entry =>
    (⟨entry, Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples.PairedAnnulus.samplePrimitives entry error
      positive⟩ :
      (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains) ×
        Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples.PairedAnnulus.PrimitiveSample entry error)
  refine ⟨samples, ?_⟩
  dsimp only [samples, -eq_self, -iff_self]
  induction comparison.entries with
  | nil => rfl
  | cons entry tail ih => exact congrArg (List.cons entry) ih

end PairedComparison
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveSamples
