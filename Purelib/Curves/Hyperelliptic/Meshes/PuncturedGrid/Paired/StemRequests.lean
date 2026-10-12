module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemCancellation
import Purelib.Data.Nat.Order

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-!
# Requested removal of the actual corrected branch stems

Both independent defects are paid on the same later face bank. The endpoint
defect is weighted by a fixed bound for the entire stem-plus-hole increment.
The resulting branch-area comparison retains the full single-lap hole area.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append wordValue_reverse)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAreaRequests (StemAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse
  orderedRoute orderedRoute_value)
open Purelib.Topology.Mesh.RetracingWords (wordArea sum_map_eq_wordValue)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The actual indexed walk value obeys the squared edge-count bound from the paid face magnitude bank. -/
theorem Paired.StemRequests.walk_magnitude (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : fixed.index ≤ stage) {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start
      finish) (sheet : Fin 2) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices walk sheet)) ≤
      (walk.edgeCount : Fraction.Rational) ^ 2 * (4 * fixed.bound) := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh lifted.mesh) fixed later readings
  let observation := WordObservations.realize retainedMagnitude (lifted.edges.indexedEdges lifted.vertices walk sheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback, WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
    lifted.mesh readings.values) (lifted.edges.indexedEdges lifted.vertices walk sheet)) ≤
    ((lifted.edges.indexedEdges lifted.vertices walk sheet).length : Fraction.Rational) ^ 2 *
      (4 * fixed.bound) at cached
  rw [lifted.edges.indexedEdges_length] at cached
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using cached
/-- The fixed squared-norm ceiling for the concatenated stem and hole walk. -/
def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemHoleMagnitude
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) : Fraction.Rational :=
  (((bank.rows.get branch).stem.append (bank.rows.get branch).boundary).edgeCount : Fraction.Rational) ^ 2 * (4 *
    fixed.bound)

/-- The retained stem-plus-hole magnitude ceiling is nonnegative. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemHoleMagnitude_nonnegative
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) : 0 ≤ bank.stemHoleMagnitude fixed branch :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

/-- At a paid stage, the sum of the actual stem and hole increments obeys its fixed magnitude ceiling. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemHoleMagnitude_bound
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : fixed.index ≤ stage) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
      branch sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.holeWord branch
        sheet)) ≤ bank.stemHoleMagnitude fixed branch := by
  have bound := Paired.StemRequests.walk_magnitude fixed readings later
    ((bank.rows.get branch).stem.append (bank.rows.get branch).boundary)
    sheet
  rw [lifted.edges.indexedEdges_append, SewingRetraction.wordValue_append] at bound
  exact bound

set_option genInjectivity false in
/-- A paid removal of a corrected branch stem retaining the complete single-lap hole area.

The area and endpoint defects use the same later face bank, with the latter weighted by the stem-plus-hole magnitude. -/
structure Paired.StemRequests.StemRequest (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed :
  MagnitudeBank.FaceMagnitudeBank
  domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The requested squared-area error is strictly positive. -/ positive : 0 < target
  /-- The cached stem-plus-hole squared-norm ceiling. -/ magnitude : Fraction.Rational
  /-- The magnitude cache reads the actual retained stem and hole walks. -/ magnitude_eq : magnitude =
    bank.stemHoleMagnitude fixed branch
  /-- The retained weighted allowance for the endpoint defect. -/ incrementTarget : Fraction.Rational
  /-- The endpoint allowance is the weighted share of one quarter of the target. -/ incrementTarget_eq : incrementTarget
    = Weighted.allowance (target / 4) (4 * magnitude)
  /-- The actual opposite-sheet stem area request at one quarter of the target. -/ area : StemAreaRequest bank fixed
    branch sheet (target / 4)
  /-- The paired increment request on the same retained stem placement. -/ increment : PairedWalk.IncrementRequest
    area.paired domains differential sheet incrementTarget
  /-- The cached common stage paying the area and increment requests. -/ index : Nat
  /-- The common stage is exactly the maximum of the two retained request stages. -/ index_eq : index = max area.index
    increment.index

constructive_injectivity Paired.StemRequests.StemRequest

namespace Paired.StemRequests.StemRequest

variable {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential} {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {sheet : Fin 2} {target : Purelib.Data.Rat.Fraction.Rational}

/-- Prepare the stem area and increment requests with their shared magnitude budget and cache the common paid stage. -/
def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains
  differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 < target)
      :
    StemRequest bank fixed branch sheet target :=
  let magnitude := bank.stemHoleMagnitude fixed branch
  let incrementTarget := Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let area := StemAreaRequest.build bank fixed branch sheet (target / 4) quarterPositive
  let increment := IncrementRequest.build area.paired domains differential sheet incrementTarget
    (Weighted.allowance_positive quarterPositive
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (bank.stemHoleMagnitude_nonnegative fixed branch)))
  ⟨positive, magnitude, rfl, incrementTarget, rfl, area, increment, max area.index increment.index, rfl⟩

/-- At the common paid stage, the actual corrected stem error obeys the requested squared-norm target. -/
theorem accurate (request : StemRequest bank fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) : normSq (bank.stemError (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.values) branch sheet) ≤ target := by
  have areaLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have incrementLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have oppositeLater := (Data.Nat.Order.le_max_left _ _).trans (request.area.index_eq ▸ areaLater)
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans (request.area.opposite.index_eq ▸ oppositeLater)
  have magnitude := bank.stemHoleMagnitude_bound fixed branch sheet readings fixedLater
  rw [← request.magnitude_eq] at magnitude
  have magnitudeNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸ bank.stemHoleMagnitude_nonnegative fixed
    branch
  have increment : Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.returnWord branch sheet) -
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord branch
        sheet)) ≤ request.incrementTarget := by
    rw [bank.returnWord_reverse, SewingRetraction.wordValue_reverse _ (CanonicalEdgeValues.edgeValuation_reverse
      lifted.mesh readings.values)]
    rw [show -SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
      branch (BranchCutLifts.otherSheet sheet)) -
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord branch
          sheet) =
        -(SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
          branch sheet) +
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
            branch (BranchCutLifts.otherSheet sheet))) by ring1,
      ]
    rw [Data.Gaussian.Norm.Basic.normSq_neg]
    exact request.increment.accurate readings incrementLater
  have oldBound {value : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Data.Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct (oldBound magnitude) increment
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) magnitudeNonnegative
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have weightedBound : 4 * request.magnitude * request.incrementTarget ≤ target / 4 := by
    rw [request.incrementTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have paid := (weighted.trans_eq (by ring1)).trans weightedBound
  let areaSample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh lifted.mesh) readings
  let areaComparison := request.area.realize areaSample areaLater
  have areaPaid := oldBound areaComparison.pay
  rw [areaComparison.return_readback] at areaPaid
  have estimate := (bank.stemError_bound (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch
    sheet).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct areaPaid
      ((show 4 * Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
        lifted.mesh readings.values) (bank.stemWord branch sheet) +
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.holeWord branch
          sheet)) *
          Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
            lifted.mesh readings.values) (bank.returnWord branch sheet) -
            SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
              branch sheet)) =
        4 * (Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
          lifted.mesh readings.values) (bank.stemWord branch sheet) +
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.holeWord
            branch sheet)) *
            Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
              lifted.mesh readings.values) (bank.returnWord branch sheet) -
              SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
                branch sheet))) by ring1).trans_le paid)) (by decide))
  apply canonicalBound
  exact estimate.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Stem removal preserves the entire physical hole polygon. It is not replaced by its endpoint displacement or by a
zero-area assertion. -/
theorem loop_area_accurate (request : StemRequest bank fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) :
    normSq (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.liftedLoop
      branch sheet).indexed -
      bank.holeArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch sheet) ≤ target := by
  rw [bank.loop_area]
  rw [show bank.holeArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch sheet +
      bank.stemError (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch sheet -
        bank.holeArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch sheet =
      bank.stemError (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) branch sheet by ring1]
  exact request.accurate readings later

end Paired.StemRequests.StemRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
