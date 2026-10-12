module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Fixed corner magnitudes for the actual shared face bank

Three retained paths from the lower-left corner fix a bound before the final
polynomial index is chosen. Both sheets use their original domains and entry
owners. The bounds concern increments, so arbitrary primitive translations
do not enter the sewing-area budget.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Data.Nat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {domain : PeriodDomain models sheet}
    {differential : Differential genus}

set_option genInjectivity false in
/-- A fixed primitive reference from the original face anchor to one actual retained corner.

The route, incoming sheet owner and entered domain are retained together, and the unit request fixes a bound before any
later numerical face index. -/
structure CornerReference (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential
  genus) (corner : Fin 4) where
  /-- The original clear route from the face anchor to this exact corner. -/ route : ClearBoxPaths.Route
    curve.polynomial face.cell.box face.cell.box.anchor (FaceCorners.point face.cell.box corner)
  /-- The cached original route preparation on the retained sheet owner. -/ prepared :
    PreparedClearPathModels.CoveredTracedPath route.path (models.frame.owners sheet)
  /-- The actual entered face path consuming this exact route preparation. -/ entered : EnteredPaths.EnteredPath models
    prepared differential sheet
  /-- The entry is exactly the original selected sheet's face-origin entry. -/ entry_eq : entered.entry = Entry.origin
    models sheet
  /-- The entered path retains the supplied original domain up to erased dependent transport. -/ domain_eq : HEq
    entered.domain domain
  /-- The cached unit-target primitive reference on this exact entered path. -/ reference :
    PrimitiveReferences.Reference entered 1

constructive_injectivity CornerReference

namespace CornerReference

/-- Prepare the actual anchor-to-corner route once on the original domain and retain its unit-target primitive
reference. -/
@[expose] def build (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus)
  (corner : Fin 4) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReference domain differential corner :=
  let route := Route.build face.clearance face.cell.box.anchor (FaceCorners.point face.cell.box corner)
    face.cell.box.contains_anchor (FaceCorners.inside face.cell.box corner)
  let prepared := CoveredTracedPath.build route.path route.within (models.frame.owners sheet)
  let entered := EnteredPath.ofEntry (Entry.origin models sheet) domain prepared
    (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within face.cell.box.contains_anchor)
    differential sheet (ParentCache.build prepared differential sheet)
  ⟨route, prepared, entered, rfl, HEq.rfl, Reference.build entered 1 (by decide)⟩

/-- Every sufficiently refined actual corner increment satisfies its original retained reference bound. -/
theorem bounded {corner : Fin 4} (fixed :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReference domain differential corner) {index
  : Nat}
    (later : fixed.reference.budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives domain differential
      index) :
  Data.Gaussian.Norm.Basic.normSq (data.corners.values corner - data.corners.values 0) ≤ fixed.reference.bound
    := by
  rcases fixed with ⟨route, prepared, entered, entryEq, domainEq, reference⟩
  rcases entered with ⟨entry, usedDomain, cache, reached, mesh, bounds, globalBounds, first, last, firstEq, lastEq⟩
  cases entryEq
  cases eq_of_heq domainEq
  exact reference.bounded later data 0 corner rfl rfl

end CornerReference

set_option genInjectivity false in
/-- Retain the three non-anchor corner references and their common stage and bound.

The original three references determine the cached nested maximum stage and the
exact sum of their stage-independent magnitude ceilings. -/
structure CornerReferences (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential
  genus) where
  /-- The retained reference from the face anchor to corner one. -/ second :
    CornerReference domain differential 1
  /-- The retained reference from the face anchor to corner two. -/ third :
    CornerReference domain differential 2
  /-- The retained reference from the face anchor to corner three. -/ fourth :
    CornerReference domain differential 3
  /-- The cached common sufficient face-model index for all three references. -/ index : Nat
  /-- The common index is exactly the maximum of the three retained grid request indices. -/ index_eq : index = max
    second.reference.budget.grid.index (max third.reference.budget.grid.index fourth.reference.budget.grid.index)
  /-- The cached stage-independent squared-norm ceiling for every corner increment. -/ bound :
    InverseRootPolynomial.Coordinate
  /-- The common bound is exactly the sum of the three retained reference bounds. -/ bound_eq : bound =
    second.reference.bound + third.reference.bound + fourth.reference.bound

constructive_injectivity CornerReferences

namespace CornerReferences

/-- Cache the three original non-anchor corner references and their exact common index and bound. -/
@[expose] def build (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus)
  : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReferences domain differential :=
  let second := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReference.build domain
    differential 1
  let third := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReference.build domain
    differential 2
  let fourth := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReference.build domain
    differential 3
  ⟨second, third, fourth,
    max second.reference.budget.grid.index (max third.reference.budget.grid.index fourth.reference.budget.grid.index),
      rfl,
    second.reference.bound + third.reference.bound + fourth.reference.bound, rfl⟩

/-- The cached total corner magnitude bound is nonnegative. -/
theorem nonnegative (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReferences domain
  differential) : 0 ≤ fixed.bound := by
  rw [fixed.bound_eq]
  exact add_nonneg (add_nonneg fixed.second.reference.bound_positive.le fixed.third.reference.bound_positive.le)
    fixed.fourth.reference.bound_positive.le

/-- Every sufficiently refined corner-minus-anchor reading meets the retained ceiling.

The supplied later stage is sufficient for all three original corner references.
Their nonnegative ceilings sum to the same retained common magnitude bound. -/
theorem bounded (fixed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences.CornerReferences domain
  differential) {index : Nat} (later : fixed.index ≤ index)
    (data : PrimitiveData.DomainPrimitives domain differential index) (corner : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq (data.corners.values corner - data.corners.values 0) ≤ fixed.bound := by
  have common : Nat.max fixed.second.reference.budget.grid.index
      (Nat.max fixed.third.reference.budget.grid.index fixed.fourth.reference.budget.grid.index) ≤ index := by
    rw [fixed.index_eq] at later
    rw [Order.max_eq_natMax, Order.max_eq_natMax] at later
    exact later
  have firstLater := (Order.le_max_left _ _).trans common
  have secondLater := (Order.le_max_left _ _).trans ((Order.le_max_right _ _).trans common)
  have thirdLater := (Order.le_max_right _ _).trans ((Order.le_max_right _ _).trans common)
  rcases corner with ⟨corner, inside⟩
  have cases : corner = 0 ∨ corner = 1 ∨ corner = 2 ∨ corner = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · change Data.Gaussian.Norm.Basic.normSq (data.corners.values 0 - data.corners.values 0) ≤ fixed.bound
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact fixed.nonnegative
  · exact (fixed.second.bounded firstLater data).trans (by
      rw [fixed.bound_eq]
      exact (le_add_of_nonneg_right fixed.third.reference.bound_positive.le).trans
        (le_add_of_nonneg_right fixed.fourth.reference.bound_positive.le))
  · exact (fixed.third.bounded secondLater data).trans (by
      rw [fixed.bound_eq]
      exact (le_add_of_nonneg_left fixed.second.reference.bound_positive.le).trans
        (le_add_of_nonneg_right fixed.fourth.reference.bound_positive.le))
  · exact (fixed.fourth.bounded thirdLater data).trans (by
      rw [fixed.bound_eq]
      exact le_add_of_nonneg_left (add_nonneg fixed.second.reference.bound_positive.le
        fixed.third.reference.bound_positive.le))

end CornerReferences

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeReferences
