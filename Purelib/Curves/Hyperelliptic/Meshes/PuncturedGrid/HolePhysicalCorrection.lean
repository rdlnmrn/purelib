module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.GeneratorValuations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation
public import Purelib.Riemann.Periods.WeightedPeriods
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathRequests

open Purelib.Topology.Surface.Word.GeneratorValuations

public section

/-!
# All weighted branch-hole corrections on one retained period surface

One cached integer coefficient mass pays all hole multiplicities. Every hole
retains its actual one-sided cut word. Contact budgets are computed once and
shared by all rows; one maximum controls every later triangle/surface sample.
Exterior components are outside this bound and remain in the area formula.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Surface.Sewing.SewnPathRequests (PathRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutCancellation (BranchHoleCutRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison (hole_sources_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (holeCutWord)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Periods.WeightedPeriods (Coefficients)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Differential genus} {weights :
    Data.Vector Int base.faces.holes.length}

set_option genInjectivity false in
/-- One shared positive request for all weighted physical branch-hole corrections.

The original coefficient mass allocates one per-hole allowance; every retained one-sided cut word uses the same path and
contact budget caches above a common stage. -/
structure HolePhysicalRequest
    (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch lifted.cutBoundaryPairs
      differential domains)
    (coefficients : WeightedPeriods.Coefficients weights) (target : SewnPrimitiveFaces.Coordinate) (floor : Nat) where
  /-- The complete weighted hole-correction target is strictly positive. -/ positive : 0 < target
  /-- The cached common allowance for each original physical branch hole. -/ perHole : SewnPrimitiveFaces.Coordinate
  /-- The per-hole allowance is the target divided by the original coefficient mass plus one. -/ perHole_eq : perHole =
    target / (coefficients.mass + 1)
  /-- The shared retained sewing-path request for the original per-hole allowance. -/ path :
    SewnPathRequests.PathRequest lifted.cutPolygon.patch.assembly 8 (perHole / 4)
  /-- The single cached original contact request used by every retained hole row. -/ contacts :
    ContactPreparations.Request prepared.prepared path.tolerance 0
  /-- The actual original hole requests indexed by their retained physical face positions. -/ rows :
    Data.Vector.DependentVector (fun index : Fin base.faces.holes.length =>
    BranchHoleCutCancellation.BranchHoleCutRequest base.faces.holes[index.val] prepared.prepared perHole floor)
  /-- Every original hole row reuses the exact same cached sewing-path request. -/ rows_path : ∀ index, (rows.get
    index).path = path
  /-- Every original hole row reuses the exact same cached contact budgets. -/ rows_budgets : ∀ index, HEq (rows.get
    index).contactRequest.budgets contacts.budgets
  /-- The cached maximum contact stage of the retained hole rows. -/ maximum : Nat
  /-- The cached maximum is computed from the original dependent vector of hole requests. -/ maximum_eq : maximum =
    rows.maximum (fun _ row => row.contactRequest.index)
  /-- The common cached stage paying every original hole request and the supplied floor. -/ index : Nat
  /-- The common stage is the maximum of the supplied floor and retained row maximum. -/ index_eq : index = max floor
    maximum

constructive_injectivity HolePhysicalRequest

namespace HolePhysicalRequest

variable {prepared : BoundaryContactPreparations
  lifted.cutPolygon.patch lifted.cutBoundaryPairs differential domains}
  {coefficients : Coefficients weights} {target :
    Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Cache one sewing path and contact budget, then build all original physical hole rows with the same per-hole
allowance. -/
@[expose] def build (prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
  lifted.cutBoundaryPairs differential domains)
    (coefficients : WeightedPeriods.Coefficients weights) (target : SewnPrimitiveFaces.Coordinate) (positive : 0 <
      target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest prepared coefficients target
      floor :=
  let perHole := target / (coefficients.mass + 1)
  have perHolePositive : 0 < perHole := Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficients.mass_nonnegative (by decide))
  have quarterPositive : 0 < perHole / 4 := Fraction.Order.Field.div_pos_direct perHolePositive (by decide)
  let path := PathRequest.ofProfile prepared.profile prepared.profile_eq 8 (perHole / 4) quarterPositive
  let contacts := ContactPreparations.Request.build prepared.prepared path.tolerance path.tolerance_positive 0
  let rows := DependentVector.ofFn (fun index : Fin base.faces.holes.length =>
    let hole := base.faces.holes[index.val]
    let paired := BranchHoleCancellation.cancellationRequest hole lifted.mesh domains differential (perHole / 4)
      quarterPositive
    let cut := BranchHoleCutWords.holeCutWord lifted hole (List.getElem_mem _)
    BranchHoleCutRequest.ofCachedContacts paired cut
      (BranchHoleSourceComparison.hole_sources_eq hole (List.getElem_mem _) paired cut.sources.sources
        cut.sources_project)
      path prepared.sewing_mem contacts floor)
  let maximum := rows.maximum (fun _ row => row.contactRequest.index)
  ⟨positive, perHole, rfl, path, contacts, rows,
    (fun index => by dsimp only [rows]; rw [DependentVector.ofFn_get]; rfl),
    (fun index => by dsimp only [rows]; rw [DependentVector.ofFn_get]; rfl),
    maximum, rfl, max floor maximum, rfl⟩

/-- The common hole-request stage retains the original supplied minimum floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest
  prepared coefficients target floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- Every original hole row is ready above the common cached request stage. -/
theorem row_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest
  prepared coefficients target floor) (row : Fin base.faces.holes.length)
    {index : Nat} (later : request.index ≤ index) : (request.rows.get row).contactRequest.index ≤ index := by
  have bounded := request.rows.get_le_maximum (fun _ row => row.contactRequest.index) row
  rw [← request.maximum_eq] at bounded
  exact bounded.trans ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later))

/-- The retained per-hole allowance is strictly positive. -/
theorem perHole_positive (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest
  prepared coefficients target floor) : 0 < request.perHole := by
  rw [request.perHole_eq]
  exact Fraction.Order.Field.div_pos_direct request.positive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficients.mass_nonnegative (by decide))

/-- The original coefficient mass times the common hole allowance is strictly below the complete target. -/
theorem paid (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest prepared
  coefficients target floor) : coefficients.mass * request.perHole < target := by
  have strict : coefficients.mass < coefficients.mass + 1 := by
    have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide : (0 : SewnPrimitiveFaces.Coordinate) < 1) coefficients.mass
    exact ((Fraction.Field.add_comm coefficients.mass 0).trans
      (Fraction.Field.zero_add coefficients.mass)).symm.trans_lt translated
  have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    strict request.perHole_positive
  apply bound.trans_eq
  rw [request.perHole_eq, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficients.mass_nonnegative (by decide)).ne'

/-- Every original branch-hole loop is evaluated through the same cut generator bank. The cached coefficient mass
includes the complete finite count and squared integer multiplicities. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest
  prepared coefficients target floor) {index : Nat}
    (later : request.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank differential index domains} (triangles :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    Data.Gaussian.Norm.Basic.normSq (coefficients.combine (fun row : Fin base.faces.holes.length =>
      SewingRetraction.wordValue (ProjectedEdgePairing.generatorValue lifted.cutBoundaryPairs (fun column =>
        surface.sewn.values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators
          column).finish -
          surface.sewn.values ((ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.generators
            column).start))
            (base.faces.holes[row.val].liftedBoundary lifted.vertices lifted.edges))) < target := by
  have bound := coefficients.normSq_combine_le _ (fun _ => request.perHole) (fun row => by
    have scalar := ((request.rows.get row).generator_accurate (request.row_later row later) triangles surface).le
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
  rw [coefficients.charge_constant] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bound.trans_lt request.paid

end HolePhysicalRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
