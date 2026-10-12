module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Riemann.Branches.NewtonCutAreaRequests
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision.SewnAnnulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing

public section

/-!
# Requested annular contributions on the sewn surface

The sample retains the actual selected annular area, original inner-hole
area, paired cut jumps and defects, and Newton occurrence offsets. Its
computed correction accounts for all of them. The remaining error is paid
by the same Newton and contact budgets used by the prepared outer tour.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation (CutComparison)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (CutBalance)
open Purelib.Riemann.Branches.NewtonCutAreaRequests (SewnRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error
    radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {lifted : LiftedPuncturedGrid request.grid.punctured}
  {differential : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.grid.faces.regulars} {stage floor : Nat}
  {shared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {surface : CachedSample lifted.cutPolygon.patch
    readings.values}

set_option genInjectivity false in
/-- The actual sewn annular area sample with all retained boundary and occurrence corrections.

The original inner-hole area, paired jumps, defects and Newton occurrence offsets remain explicit in the cached
correction. -/
structure AnnularSample (annulus : AllHoleExcision.SewnAnnulus surface) (prepared : Lifted.OuterPreparation
  annulus.source.region)
    (requested : NewtonCutAreaRequests.SewnRequest request prepared differential domains floor) where
  /-- The actual outer-tour comparison on the retained triangle readings and sewn sample. -/ outer :
    CutComparison.Sample requested.comparison readings surface
  /-- The retained exact area balance of the original selected annulus. -/ balance : CutBalance annulus
    prepared requested.comparison.word
  /-- The cached primitive sample on the actual retained projected edge pairing. -/ paired :
    ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues
  /-- The cached original inner-hole boundary area. -/ innerArea : Data.Gaussian.Basic.Canonical
  /-- The cache is exactly the retained inner word's area under the original sewn energy values. -/ innerArea_eq :
    innerArea = Stokes.edgeListArea surface.energyValues balance.inner.word.edges
  /-- The complete cached inner-boundary, jump, defect and occurrence-offset correction. -/ correction :
    Data.Gaussian.Basic.Canonical
  /-- The cached correction is exactly the sum of the retained original inner area, paired jumps, paired defects and
    outer occurrence correction. -/ correction_eq : correction = innerArea + paired.jumpSum + paired.defectSum +
    outer.occurrences.correction

constructive_injectivity AnnularSample

namespace AnnularSample

variable {annulus : SewnAnnulus surface} {prepared :
  OuterPreparation annulus.source.region}
  {requested : SewnRequest request prepared differential domains floor}

/-- Cache the actual outer sample, retained annular balance and complete correction using the original sewn values. -/
@[expose] def build (annulus : AllHoleExcision.SewnAnnulus surface) (prepared : Lifted.OuterPreparation
  annulus.source.region)
    (requested : NewtonCutAreaRequests.SewnRequest request prepared differential domains floor) :
      Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests.AnnularSample annulus prepared requested :=
  let outer := CutComparison.Sample.build requested.comparison readings surface
  let balance := CutBalance.build annulus prepared requested.comparison.word
  let paired := PrimitiveSample.build balance.complete.pairing surface.energyValues
  let innerArea := Stokes.edgeListArea surface.energyValues balance.inner.word.edges
  ⟨outer, balance, paired, innerArea, rfl,
    innerArea + paired.jumpSum + paired.defectSum + outer.occurrences.correction, rfl⟩

/-- This is the area already retained by the sewn annular selection. The identity does not substitute a new triangle
list or a projected primitive. -/
theorem corrected_eq (sample : Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests.AnnularSample annulus prepared
  requested) :
    annulus.selected.area - sample.correction = sample.outer.occurrences.raw - sample.outer.occurrences.correction := by
  rw [sample.balance.area_balance sample.paired, sample.correction_eq, sample.innerArea_eq, ← sample.outer.raw_area]
  ring1

/-- The actual selected annular area after its retained complete correction satisfies the original Newton/contact error
target. -/
theorem accurate (sample : Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests.AnnularSample annulus prepared
  requested) (later : requested.sewing.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (annulus.selected.area - sample.correction) < error := by
  rw [sample.corrected_eq]
  exact requested.corrected_area_small later sample.outer

end AnnularSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests
