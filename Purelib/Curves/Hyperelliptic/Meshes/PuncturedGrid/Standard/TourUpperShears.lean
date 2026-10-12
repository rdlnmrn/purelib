module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutIntersection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourShearCoordinates
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

@[expose] public section

/-!
# Actual upper-triangular corrections from the retained B-B table

Construct the weights and root-closed corrected tours directly from cached
intersection data. The exact correction theorem requires the original A-A
and A-B blocks to be zero and identity respectively. This requirement is
explicit: arbitrary branch layouts have not yet been proved to satisfy it.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank (BShear)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_ite_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

set_option genInjectivity false in
/-- The actual upper-triangular B-tour correction determined by the retained original intersection table. -/
structure UpperBShear (bank : TourIntersection.IntersectionBank lifted integral) (target : Fin genus) where
  /-- The cached integer correction weights on the original ordered A rows. -/ weights : Data.Vector Int
    genus
  /-- Each weight is the original B/B table entry below the target index and zero elsewhere. -/ weights_eq : ∀ index,
    weights index = if index.val < target.val then bank.bb index target else 0
  /-- The retained actual root-closed B-tour shear using these exact cached weights. -/ shear : IntersectionBank.BShear
    bank target weights
  /-- The exact cut-coordinate certificate on that same retained corrected tour. -/ coordinates : shear.CutCoordinates

constructive_injectivity UpperBShear

namespace UpperBShear

variable {bank : IntersectionBank lifted
  integral} {target : Fin genus}

/-- The existing table determines every coefficient. Geometry, root return, and cut-coordinate witnesses are all
constructed internally. -/
def build (bank : TourIntersection.IntersectionBank lifted integral) (target : Fin genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears.UpperBShear bank target :=
  let weights := Data.Vector.Basic.vectorOfFn fun index => if index.val < target.val then bank.bb index target else 0
  let shear := BShear.build bank target weights
  ⟨weights, Data.Vector.Basic.vectorOfFn_apply _, shear, shear.cutCoordinates⟩

/-- A finite weighted Kronecker-delta sum reads the actual selected weight. -/
private theorem sum_delta (weights : Fin genus → Int) (target : Fin genus) :
    FiniteSum.Fin.sumFin (fun index => weights index * (if index = target then 1 else 0)) = weights target := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => if index = target then weights index else 0) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      by_cases same : index = target
      · rw [if_pos same, if_pos same, mul_one]
      · rw [if_neg same, if_neg same, mul_zero]
    _ = _ := FiniteSum.Fin.sumFin_ite_eq target weights

/-- The actual upper B correction retains A/B duality when the original A/A block vanishes and the A/B block is
identity. -/
theorem a_b (corrected : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears.UpperBShear bank target)
    (aa : ∀ first last, bank.aa first last = 0)
    (ab : ∀ first last, bank.ab first last = if first = last then 1 else 0) (index : Fin genus) :
    SpanningCoordinates.intersection
      (bank.rows.get index).span.a corrected.coordinates.span = if index = target then 1 else 0 := by
  rw [corrected.coordinates.a_intersection, ab]
  have zero : FiniteSum.Fin.sumFin (fun source => corrected.weights source * bank.aa index source) = 0 :=
    (FiniteSum.Fin.sumFin_congr (fun source => by rw [aa index source, mul_zero])).trans FiniteSum.Fin.sumFin_zero
  rw [zero, add_zero]

/-- Once the original A rows are isotropic and dual to B, the constructed literal corrections have zero pairwise B
intersection in every genus. -/
theorem b_b (first : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears.UpperBShear bank target)
  {otherTarget : Fin genus} (last : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears.UpperBShear bank
  otherTarget)
    (aa : ∀ first last, bank.aa first last = 0)
    (ab : ∀ first last, bank.ab first last = if first = last then 1 else 0) :
    SpanningCoordinates.intersection
      first.coordinates.span last.coordinates.span = 0 := by
  have paired := first.coordinates.intersection last.coordinates
  have zero (index : Fin genus) : FiniteSum.Fin.sumFin (fun source => last.weights source * bank.aa index source) = 0 :=
    (FiniteSum.Fin.sumFin_congr (fun source => by rw [aa index source, mul_zero])).trans FiniteSum.Fin.sumFin_zero
  have lastTerms : FiniteSum.Fin.sumFin (fun index => last.weights index * bank.ab index target) = last.weights target
    :=
    (FiniteSum.Fin.sumFin_congr (fun index => congrArg (last.weights index * ·) (ab index target))).trans
      (sum_delta _ _)
  have firstTerms : FiniteSum.Fin.sumFin (fun index => first.weights index *
      (bank.ab index otherTarget + FiniteSum.Fin.sumFin (fun source => last.weights source * bank.aa index source))) =
      first.weights otherTarget :=
    (FiniteSum.Fin.sumFin_congr (fun index => by rw [zero, add_zero, ab])).trans
      (sum_delta _ _)
  rw [lastTerms, firstTerms] at paired
  rw [paired, first.weights_eq, last.weights_eq]
  rcases lt_trichotomy target.val otherTarget.val with before | equal | after
  · rw [if_pos before, if_neg (Nat.not_lt.mpr (Nat.le_of_lt before))]
    ring1
  · have same : target = otherTarget := Fin.ext equal
    subst otherTarget
    rw [bank.bb_diagonal, if_neg (Nat.lt_irrefl _)]
    ring1
  · rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt after)), if_pos after, bank.bb_skew target otherTarget]
    ring1

end UpperBShear
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourUpperShears
