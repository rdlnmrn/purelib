module
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments

open Purelib.Integration.Polynomial.Rectangle.Accuracy

@[expose] public section

/-!
# Contained-path requests using a supplied shared primitive cache

Scalar accuracy is selected before this constructor runs. The supplied
primitive, anchor and offset data are reused verbatim at the selected common
index; only the actual parent's controlled requests and mesh readings are new.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank} {models :
    FaceModels frames face}
  {base finish : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner (curve.polynomial.eval base)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish} {prepared :
    CoveredTracedPath path owner}
  {differential : Differential genus} {parentSheet : Fin 2}

/-- Both faces of a contact can consume this very same prepared request. The grid index and the parent's minimum index
are independent scalar floors. -/
def requestSharedWith (entered :
  EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
      / 4))
    (index : Nat) (later : budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives entered.domain differential
      index)
    (request : ControlledSumRequest entered.cache.parents genus (target / 4)) (minimum : budget.minimumIndex ≤
      request.minimumIndex) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments entered.mesh entered.bounds entered.globalBounds
        genus target :=
  let budget := budget.atGridIndex index later
  RequestedFragments.ofPrimitives entered.mesh entered.bounds entered.globalBounds budget request minimum
    data.primitives data.anchors data.offsets entered.reached

/-- Acquire only the original parent's controlled request while reusing the supplied primitive, anchor and offset
caches. -/
def requestShared (entered :
  EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
      / 4))
    (index : Nat) (later : budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives entered.domain differential
      index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments entered.mesh entered.bounds entered.globalBounds
        genus target :=
  let request := ControlledSumRequest.acquire entered.cache.covered entered.cache.proper (target / 4)
    budget.target_positive budget.minimumIndex
  have minimumEq : request.minimumIndex = budget.minimumIndex := ControlledSumRequest.acquire_minimumIndex ..
  requestSharedWith entered budget index later
    data request minimumEq.symm.le

/-- Exact readback of all three dependent numerical caches. Equal indices alone would not identify independently
generated primitive or offset banks. -/
def UsesData (entered :
  EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments entered.mesh entered.bounds
        entered.globalBounds genus target)
    {index : Nat} (data : PrimitiveData.DomainPrimitives entered.domain differential index) : Prop :=
  request.budget.grid.index = index ∧ HEq request.primitives data.primitives ∧
    HEq request.anchors data.anchors ∧ HEq request.offsets data.offsets

/-- The request constructed with the supplied parent request retains all three exact numerical caches. -/
theorem
  requestSharedWith_usesData
  (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
      / 4))
    (index : Nat) (later : budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives entered.domain differential
      index)
    (request : ControlledSumRequest entered.cache.parents genus (target / 4)) (minimum : budget.minimumIndex ≤
      request.minimumIndex) :
    entered.UsesData (entered.requestSharedWith budget index later data request minimum) data := ⟨rfl, HEq.rfl, HEq.rfl,
      HEq.rfl⟩

/-- The constructed local request retains the supplied controlled parent request unchanged. -/
theorem requestSharedWith_request
  (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
      / 4))
    (index : Nat) (later : budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives entered.domain differential
      index)
    (request : ControlledSumRequest entered.cache.parents genus (target / 4)) (minimum : budget.minimumIndex ≤
      request.minimumIndex) :
    (entered.requestSharedWith budget index later data request minimum).request = request := rfl

/-- The acquired local request retains the supplied common-stage primitive, anchor and offset caches exactly. -/
theorem requestShared_usesData
  (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) {target : Coordinate}
    (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
      / 4))
    (index : Nat) (later : budget.grid.index ≤ index) (data : PrimitiveData.DomainPrimitives entered.domain differential
      index) :
    UsesData entered
      (requestShared entered budget index later
        data) data := ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath
