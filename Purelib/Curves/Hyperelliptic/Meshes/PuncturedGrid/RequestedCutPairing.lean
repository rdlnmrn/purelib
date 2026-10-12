module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCutPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring

public section

/-! Automatic allocation and acquisition of the corrected cut-word comparison.
The common numerical bank is selected after all geometric requests. Physical
hole and exterior terms remain explicit; this is not yet their cancellation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces
open Purelib.Riemann.Periods
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.WordArea
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.Bilinear
open Purelib.Topology.Surface.Sewing.Bilinear.Samples
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
open Purelib.Topology.Surface.Word

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest (ExteriorBoundaryRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests (TotalRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget (CornerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- No scalar accuracy, sewing compatibility, or successful stage search is supplied by the caller. The request retains
every prepared input. -/
structure CutPairingRequest (lifted : Meshes.LiftedPuncturedGrid base)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (i j : Fin genus) (target : Fraction.Rational) (floor : Nat) where
  /-- The requested cut-pairing target is strictly positive. -/ positive : 0 < target
  /-- The shared retained cut refinements on the original face domains. -/ cuts : RegularMeshes.CommonCuts domains
  /-- The original numerical preflights on each sheet. -/ fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains
    sheet
  /-- The prepared exterior boundary request with its allocated fraction of the target. -/ exterior :
    RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet => RegularMeshes.build domains cuts sheet 0) fixed
    ((((target / 4) / 4) / 4) / 4)
  /-- The actual crossing bank of the retained exterior request and lifted mesh. -/ crossings :
    Matched.CrossingBank exterior.prepared.energy lifted.mesh
  /-- The complete crossing replacement request on the actual retained crossing bank. -/ total :
    CrossingRequests.TotalRequest crossings i j 0 0 (((((target / 4) / 4) / 4) / 4) / 4) floor
  /-- The retained common corner replacement budget. -/ corner : CrossingCornerBudget.CornerRequest fixed i j (((target
    / 4) / 4) / 4)
  /-- The original bilinear sewing preparations for the two basis differentials. -/ preparation :
    SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains i j
  /-- The paid sewing request on those exact retained preparations. -/ sewing : BilinearPreparation.Request preparation
    ((target / 4) / 4) floor
  /-- The common stage paying every ownership, crossing, corner and sewing threshold. -/ index : Nat
  /-- The original requested floor is at most the retained common stage. -/ floor_le : floor ≤ index
  /-- The exterior ownership threshold is at most the retained common stage. -/ ownership_le :
    exterior.prepared.ownership.index ≤ index
  /-- The crossing replacement threshold is at most the retained common stage. -/ crossing_le : total.allocated.index ≤
    index
  /-- The corner replacement threshold is at most the retained common stage. -/ corner_le : corner.index ≤ index
  /-- The sewing threshold is at most the retained common stage. -/ sewing_le : sewing.index ≤ index

constructive_injectivity CutPairingRequest

namespace CutPairingRequest

variable {i j : Fin genus} {target : Rational} {floor : Nat}

/-- Prepare all original cut-pairing requests and cache a common paid stage for the supplied positive target. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (cuts : RegularMeshes.CommonCuts domains)
    (i j : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains i j target floor :=
      by
  have quarter {value : Fraction.Rational} (h : 0 < value) : 0 < value / 4 :=
    Fraction.Order.Field.div_pos_direct h (by decide)
  have localPositive := quarter positive
  let fixed := fun sheet => RegularMeshes.preflights domains sheet
  let exterior := ExteriorBoundaryRequest.build (fun sheet => RegularMeshes.build domains cuts sheet 0)
    fixed ((((target / 4) / 4) / 4) / 4) (quarter (quarter (quarter localPositive)))
  let crossings := CrossingBank.build exterior.prepared.energy lifted.mesh
  let total := TotalRequest.build crossings i j 0 0 (((((target / 4) / 4) / 4) / 4) / 4)
    (quarter (quarter (quarter (quarter localPositive)))) floor
  let corner := CornerRequest.build fixed i j (((target / 4) / 4) / 4) (quarter (quarter localPositive))
  let preparation := BilinearPreparation.build lifted.cutPolygon domains i j
  let sewing := BilinearPreparation.Request.build preparation ((target / 4) / 4) (quarter localPositive) floor
  let index := max (max exterior.prepared.ownership.index total.allocated.index) (max corner.index sewing.index)
  have sewingLe : sewing.index ≤ index := (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  exact ⟨positive, cuts, fixed, exterior, crossings, total, corner, preparation, sewing, index,
    sewing.floor_le.trans sewingLe,
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _),
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _),
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _), sewingLe⟩

set_option genInjectivity false in
/-- The caller may supply a later shared bank without repeating its numerical preparation. All comparison samples retain
that same bank. -/
structure Readings (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains i j target floor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) where
  /-- The actual first differential's triangle readings from the shared numerical cache. -/ left :
    TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh
  /-- The actual second differential's triangle readings from that same cache. -/ right :
    TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh
  /-- The acquired crossing samples on the normalization of the same numerical cache. -/ crossings :
    CrossingRequests.Samples request.total.allocated cache.normalize
  /-- The retained original face perimeters on the supplied cache. -/ original : Matched.FacePerimeters (request
    := request.exterior.prepared.energy) cache i j
  /-- The retained face perimeters on the normalization of that same cache. -/ normalized :
    Matched.FacePerimeters (request := request.exterior.prepared.energy) cache.normalize i j
  /-- The sewn surface built from the exact first triangle readings. -/ leftSurface : SewnPrimitiveSamples.CachedSample
    lifted.cutPolygon.patch left.values
  /-- The sewn surface built from the exact second triangle readings. -/ rightSurface :
    SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values
  /-- The bilinear surface sample retaining both original sewn owners. -/ surface :
    Topology.Surface.Sewing.Bilinear.Samples leftSurface
    rightSurface
  /-- The actual canonical cut-boundary word sample on the retained surface values. -/ word : CutBoundaryWord.AreaSample
    lifted.cutBoundaryWord surface.values
    (surface.values lifted.cutPolygon.patch.cut.anchor)
  /-- The original integral pairing of the canonical cut-boundary word. -/ integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
    lifted.cutBoundaryWord
  /-- The retained regular-face neighbor bank for the original framed grid. -/ neighbors : PuncturedFaces.NeighborBank
    base.faces

constructive_injectivity Readings

namespace Readings

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains i j target floor}
  {stage : Nat} {cache : Numerics
    domains stage}

/-- Retain supplied triangle readings when the standard-period comparison has already acquired them on this numerical
bank. -/
@[expose] def buildWith (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest
  lifted domains i j target floor) (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache :=
  let leftSurface := CachedSample.build lifted.cutPolygon.patch left.values
  let rightSurface := CachedSample.build lifted.cutPolygon.patch right.values
  let surface := Bilinear.build leftSurface rightSurface
  ⟨left, right, Samples.build request.total.allocated cache.normalize,
    FacePerimeters.build cache i j, FacePerimeters.build cache.normalize i j,
    leftSurface, rightSurface, surface, surface.wordSample lifted.cutBoundaryWord,
    lifted.cutIntegralPairing, NeighborBank.build base.faces base.bank.frame⟩

/-- Acquire both original triangle readings once and build the complete comparison on the same numerical cache. -/
@[expose] def build (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains i j target floor) (cache : RegularMeshes.Numerics domains stage) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache :=
  buildWith request cache
    (TriangleReadings.build (cache.get i) lifted.mesh) (TriangleReadings.build (cache.get j) lifted.mesh)

/-- The complete retained cut pairing, including paired and remaining matrices and the closed correction. -/
@[expose] def paired (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache) :
  Data.Gaussian.Basic.Canonical :=
  2 * Pairing.contract (fun row column => readings.integral.paired row column) readings.word.values +
    Pairing.contract (fun row column => readings.integral.remaining row column) readings.word.values +
    readings.word.closedCorrection

/-- The actual physical perimeter minus its original source-triangle correction. -/
@[expose] def physical (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache) :
  Data.Gaussian.Basic.Canonical :=
  FacePerimeters.physicalPerimeter readings.normalized readings.neighbors -
    CrossingTriangleAreas.physicalTriangleArea readings.neighbors readings.left readings.right

/-- All geometric and numerical thresholds are discharged by the request's single index; the bound concerns the actual
retained cut-word pairing. -/
theorem comparison (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
  request cache) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.original.localTotalSum - readings.paired - readings.physical) ≤
      target / 4 :=
  LocalCutPairing.local_cut_pairing_bound request.exterior request.total request.corner readings.left readings.right
    readings.crossings readings.original readings.normalized request.sewing readings.surface readings.word
      readings.integral
    (request.sewing_le.trans later) readings.neighbors (Fraction.Order.Field.div_pos_direct request.positive (by
      decide))
    (request.crossing_le.trans later) (request.corner_le.trans later)

/-- The actual corrected cut-pairing value fits the requested target at every paid stage. -/
theorem corrected_bound (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache) (later :
  request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.paired + readings.physical) ≤ target := by
  have quarterPositive {value : Fraction.Rational} (h : 0 < value) : 0 < value / 4 :=
    Fraction.Order.Field.div_pos_direct h (by decide)
  have positive := quarterPositive request.positive
  have bound := LocalCutPairing.corrected_cut_pairing_bound request.exterior request.total request.corner readings.left
    readings.right
    readings.crossings readings.original readings.normalized request.sewing readings.surface readings.word
      readings.integral
    (request.sewing_le.trans later) (request.ownership_le.trans later) readings.neighbors positive
    (request.crossing_le.trans later) (request.corner_le.trans later)
  have exteriorLe : request.exterior.localTarget ≤ target / 4 := by
    rw [request.exterior.localTarget_eq]
    exact (Fraction.Order.Field.divide_le_self (quarterPositive (quarterPositive (quarterPositive positive))).le (by
      decide)).trans
      ((Fraction.Order.Field.divide_le_self (quarterPositive (quarterPositive positive)).le (by decide)).trans
        ((Fraction.Order.Field.divide_le_self (quarterPositive positive).le (by decide)).trans
          (Fraction.Order.Field.divide_le_self positive.le (by decide))))
  apply bound.trans
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (le_refl (target / 4)) exteriorLe) (show (0 : Fraction.Rational) ≤ 2 by decide)
  exact paid.trans_eq ((show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Keep the ambient term and every individual hole correction available to subsequent patch/excision comparisons; none
is inferred to vanish. -/
theorem physical_components (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings request cache) :
    readings.physical = PhysicalComponentCorrection.physicalComponentCorrection readings.normalized readings.neighbors
      readings.left readings.right .exterior +
      FiniteSum.Fin.sumFin (fun hole =>
        PhysicalComponentCorrection.physicalComponentCorrection readings.normalized readings.neighbors readings.left
          readings.right (.hole hole)) :=
  PhysicalComponentCorrection.physicalCorrection_components readings.normalized readings.neighbors readings.left
    readings.right

end Readings

set_option genInjectivity false in
/-- Cached corrected values and the bound for this exact finite acquisition. -/
structure CertifiedReadings (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest
  lifted domains i j target floor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) where
  /-- The complete comparison readings on the supplied numerical cache. -/ readings :
    Readings request cache
  /-- The cached complete corrected cut-pairing value. -/ pairedValue : Data.Gaussian.Basic.Canonical
  /-- The cached physical boundary correction. -/ physicalValue : Data.Gaussian.Basic.Canonical
  /-- The paired cache equals the retained comparison's actual cut pairing. -/ paired_eq : pairedValue = readings.paired
  /-- The physical cache equals the retained comparison's actual boundary correction. -/ physical_eq : physicalValue =
    readings.physical
  /-- The sum of the two exact retained scalar caches satisfies the requested bound. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (pairedValue + physicalValue) ≤ target

constructive_injectivity CertifiedReadings

/-- Consume an existing later bank and retain the expensive scalar results. -/
@[expose] def readAt (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains i j target floor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) (later : request.index ≤ stage) :
    CertifiedReadings request cache :=
  let readings := Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings.build request
    cache
  ⟨readings, readings.paired, readings.physical, rfl, rfl, readings.corrected_bound later⟩

/-- Execute the prepared comparison at its certified index, retaining the expensive all-differential numerical bank
alongside its certified readings. -/
@[expose] def acquire (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted
  domains i j target floor) :
    (cache : RegularMeshes.Numerics domains request.index) ×
      CertifiedReadings request cache :=
  let cache := DependentVector.ofFn fun row =>
    FacePrimitiveBank.build (PeriodMatrix.standardDifferential row) request.index domains
  ⟨cache, request.readAt cache le_rfl⟩

end CutPairingRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
