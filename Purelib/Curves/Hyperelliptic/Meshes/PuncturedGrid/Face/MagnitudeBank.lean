module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# One geometry-first magnitude budget for every retained lifted triangle

The references are made before the requested numerical bank. The materialized
index and bound are shared by every selected region, on both local sheets.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Nat
open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences
open Purelib.Data.Rat
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Riemann.Normalization
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)

public section

namespace Face.MagnitudeBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences (CornerReferences)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {differential :
    Differential genus}

set_option genInjectivity false in
/-- The original corner-reference magnitude bounds on both sheets of one retained face.

Both reference banks use the original face domains and differential. Their
maximum sufficient stage and summed magnitude ceiling retain both sheets. -/
structure FaceMagnitudeReferences {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames
  face)
    (differential : Differentials.Basic.Differential genus) where
  /-- The actual corner references on original sheet zero. -/ zero : MagnitudeReferences.CornerReferences
    (domains.domain 0) differential
  /-- The actual corner references on original sheet one. -/ one : MagnitudeReferences.CornerReferences (domains.domain
    1) differential

constructive_injectivity FaceMagnitudeReferences

namespace FaceMagnitudeReferences

/-- Cache the actual original corner references on both retained sheets before selecting numerical primitives. -/
@[expose] def build {face : PuncturedGridFaces.RegularFace bank} (domains : DomainBanks.FaceDomains frames face)
  (differential : Differentials.Basic.Differential genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences domains differential :=
  ⟨CornerReferences.build (domains.domain 0) differential, CornerReferences.build (domains.domain 1) differential⟩

/-- Read the maximum sufficient stage of the two original sheet reference banks. -/
@[expose] def index {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences domains differential)
      : Nat := max fixed.zero.index fixed.one.index

/-- Sum the retained original magnitude bounds of the two sheet reference banks. -/
@[expose] def bound {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences domains differential)
      : Coordinate := fixed.zero.bound + fixed.one.bound

/-- The retained total magnitude bound is nonnegative. -/
theorem nonnegative {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences domains differential)
      : 0 ≤ fixed.bound :=
  add_nonneg fixed.zero.nonnegative fixed.one.nonnegative

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences in
/-- Every actual corner-minus-anchor reading on either original sheet satisfies the fixed paired-sheet bound.

The two original sheet certificates are weakened to the supplied common stage, then bounded by their retained summed
magnitude ceiling. -/
theorem bounded {face : PuncturedGridFaces.RegularFace bank} {domains : DomainBanks.FaceDomains frames face}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeReferences domains differential)
      {index : Nat} (later : fixed.index ≤ index)
    (data : PrimitiveData.FacePrimitives domains differential index) (sheet : Fin 2) (which : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq ((data.atSheet sheet).corners.values which - (data.atSheet
      sheet).corners.values 0) ≤ fixed.bound := by
  rcases sheet with ⟨sheet, inside⟩
  have cases : sheet = 0 ∨ sheet = 1 := by omega
  rcases cases with rfl | rfl
  · exact (fixed.zero.bounded (Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _
      _))) later) data.zero.get which).trans
      (le_add_of_nonneg_right fixed.one.nonnegative)
  · exact (fixed.one.bounded (Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _
      _))) later) data.one.get which).trans
      (le_add_of_nonneg_left fixed.zero.nonnegative)

end FaceMagnitudeReferences

/-- The dependent magnitude-reference bank on every actual original face-domain owner. -/
@[expose] def FaceMagnitudeEntries (differential : Differentials.Basic.Differential genus) :
    {faces : List (PuncturedGridFaces.RegularFace bank)} → DomainBanks.FaceDomainBank frames faces → Type 2
  | _, .nil => PUnit
  | _, .cons first remaining => FaceMagnitudeReferences
    first.get differential × FaceMagnitudeEntries
    differential remaining

namespace FaceMagnitudeEntries

/-- Cache actual paired-sheet references for every retained original face-domain owner. -/
@[expose] def build (differential : Differentials.Basic.Differential genus) : {faces : List
  (PuncturedGridFaces.RegularFace bank)} →
    (domains : DomainBanks.FaceDomainBank frames faces) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries differential domains
  | _, .nil => ⟨⟩
  | _, .cons first remaining => ⟨FaceMagnitudeReferences.build first.get differential,
    build differential
    remaining⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries in
/-- Read the common sufficient stage across the complete actual original face-reference bank. -/
@[expose] def index : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank
  frames faces} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries differential domains → Nat
  | _, .nil, _ => 0
  | _, .cons _ _, fixed => max fixed.1.index (index fixed.2)

/-- Sum all actual retained face-reference magnitude ceilings. -/
@[expose] def bound : {faces : List (PuncturedGridFaces.RegularFace bank)} → {domains : DomainBanks.FaceDomainBank
  frames faces} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries differential domains →
      InverseRootPolynomial.Coordinate
  | _, .nil, _ => 0
  | _, .cons _ _, fixed => fixed.1.bound +
    bound fixed.2

/-- The retained total magnitude bound is nonnegative. -/
theorem nonnegative {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank frames
  faces}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries differential domains) : 0
      ≤ fixed.bound := by
  induction domains with
  | nil => exact le_rfl
  | cons first remaining ih => exact add_nonneg fixed.1.nonnegative (ih fixed.2)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries in
/-- Any actual face, sheet and corner reading above the retained common stage satisfies the fixed complete-bank bound.

The two original sheet certificates are weakened to the supplied common stage, then bounded by their retained summed
magnitude ceiling. -/
theorem bounded {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank frames faces}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries differential domains)
      {index : Nat} (later : fixed.index ≤ index)
    (data : PrimitiveData.FacePrimitiveBank differential index domains) (position : Fin faces.length) (sheet : Fin 2)
      (which : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq (((data.get position).atSheet sheet).corners.values which -
      ((data.get position).atSheet sheet).corners.values 0) ≤ fixed.bound := by
  induction domains with
  | nil => exact Fin.elim0 position
  | cons first remaining ih =>
    rcases position with ⟨position, inside⟩
    cases position with
    | zero =>
      exact (fixed.1.bounded (Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _
        _))) later) data.1.get sheet which).trans
        (le_add_of_nonneg_right fixed.2.nonnegative)
    | succ position =>
      exact (ih fixed.2 (Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _ _)))
        later) data.2
        ⟨position, Nat.lt_of_succ_lt_succ inside⟩).trans (le_add_of_nonneg_left fixed.1.nonnegative)

end FaceMagnitudeEntries

set_option genInjectivity false in
/-- The complete original face-reference bank with cached common stage and magnitude ceiling.

The geometry and unit-target references are fixed before any later shared numerical primitive bank. -/
structure FaceMagnitudeBank {faces : List (PuncturedGridFaces.RegularFace bank)} (domains : DomainBanks.FaceDomainBank
  frames faces)
    (differential : Differentials.Basic.Differential genus) where
  /-- The actual paired-sheet reference entries on the original ordered face-domain bank. -/ entries :
    FaceMagnitudeEntries differential domains
  /-- The cached common sufficient reference stage. -/ index : Nat
  /-- The cached stage is exactly the maximum of the original retained reference entries. -/ index_eq : index =
    entries.index
  /-- The cached sum of original retained corner-reference magnitude bounds. -/ bound : InverseRootPolynomial.Coordinate
  /-- The cached magnitude ceiling is exactly the sum read from the retained original entries. -/ bound_eq : bound =
    entries.bound

constructive_injectivity FaceMagnitudeBank

namespace FaceMagnitudeBank

/-- Cache the original reference entries and materialize their exact common stage and magnitude bound. -/
@[expose] def build {faces : List (PuncturedGridFaces.RegularFace bank)} (domains : DomainBanks.FaceDomainBank frames
  faces) (differential : Differentials.Basic.Differential genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential :=
  let entries := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeEntries.build differential
    domains
  ⟨entries, entries.index, rfl, entries.bound, rfl⟩

/-- The retained total magnitude bound is nonnegative. -/
theorem nonnegative {faces : List (PuncturedGridFaces.RegularFace bank)} {domains : DomainBanks.FaceDomainBank frames
  faces}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) : 0 ≤
      fixed.bound := fixed.bound_eq ▸ fixed.entries.nonnegative

/-- Every actual sufficiently refined lifted triangle corner-minus-anchor value satisfies the retained common magnitude
ceiling.

The finite source position determines the same original face, sheet and triangle half. Its retained corner readings are
bounded by that face bank at the supplied stage. -/
theorem triangle_bounded {vertices : LiftedVertices.VertexBank bank.grid} {edges : RootEdgeBank frames}
    {faces : PuncturedGridFaces.PuncturedFaces bank} {mesh : GridLiftedMesh.LiftedMesh vertices edges faces} {domains :
      DomainBanks.FaceDomainBank frames faces.regulars}
    (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) {index
      : Nat} (later : fixed.index ≤ index)
    {data : PrimitiveData.FacePrimitiveBank differential index domains} (triangles :
      TrianglePrimitiveReadings.TriangleReadings data mesh)
    (source : Fin mesh.triangles.length) (which : Fin 3) :
    Data.Gaussian.Norm.Basic.normSq (triangles.values source which - triangles.values source 0) ≤ fixed.bound
      := by
  let position : Fin faces.regulars.length := ⟨source.val / 4, by have := source.isLt.trans_eq mesh.faceCount; omega⟩
  let sheet : Fin 2 := ⟨source.val % 4 / 2, by omega⟩
  let upper : Bool := decide (source.val % 2 = 1)
  have source_eq : source = mesh.triangleIndex position sheet upper := by
    apply Fin.ext
    simp only [LiftedMesh.triangleIndex]
    dsimp only [position, sheet, upper]
    by_cases odd : source.val % 2 = 1
    · have selected : upper = true := decide_eq_true odd
      rewrite [if_pos selected]
      omega
    · have selected : upper = false := decide_eq_false odd
      have notSelected : upper ≠ true := by
        intro impossible
        have impossible : false = true := selected.symm.trans impossible
        nomatch impossible
      rewrite [if_neg notSelected]
      omega
  rw [source_eq, triangles.values_eq]
  unfold TrianglePrimitiveReadings.FaceCorners.triangleValues
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  have first_eq : SewnPrimitiveFaces.corner (FaceCorners.triangle upper) 0 = 0 := by cases upper <;> rfl
  rw [first_eq, fixed.bound_eq]
  exact fixed.entries.bounded (fixed.index_eq ▸ later) data position sheet _

end FaceMagnitudeBank
end Face.MagnitudeBank

/- The paired source increment is the difference of two readings bounded
by the same retained face magnitude bank. -/
namespace Paired.WalkAreaRequests

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic
  (mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- An actual retained triangle source-edge increment has squared norm at most four times the fixed original corner
magnitude ceiling.

Both endpoints are readings on the same original source triangle. Their common magnitude ceiling bounds the retained
difference by direct Gaussian scalar inequalities. -/
theorem source_increment_bounded (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains differential)
    {index : Nat} (later : fixed.index ≤ index) {numerics : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings numerics mesh) (source : SewnPrimitiveContacts.SourceEdge
      mesh.triangles.length) :
    normSq (source.increment readings.values) ≤ 4 * fixed.bound := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (readings.values source.source source.last - readings.values source.source 0)
    (readings.values source.source source.first - readings.values source.source 0)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (fixed.triangle_bounded later readings source.source source.last)
        (fixed.triangle_bounded later readings source.source source.first)) (by decide))
  rw [show (readings.values source.source source.last - readings.values source.source 0) -
      (readings.values source.source source.first - readings.values source.source 0) =
      source.increment readings.values by unfold SewnPrimitiveContacts.SourceEdge.increment; ring1] at estimate
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans_eq (by ring1)

end Paired.WalkAreaRequests

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
