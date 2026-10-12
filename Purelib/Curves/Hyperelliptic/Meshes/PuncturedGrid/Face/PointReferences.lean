module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Riemann.Readings

@[expose] public section

/-! The retained finite reference controls arbitrary cached point readings,
including fine boundary vertices. Only the shared face index changes; its
prepared path, owner, parent request and evaluated sum remain fixed. -/
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences (Reference)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {base finish : Purelib.Data.Gaussian.Basic.Canonical} {owner :
    Owner (curve.polynomial.eval base)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish} {prepared :
    CoveredTracedPath path owner}
  {differential : Differential genus} {parentSheet : Fin 2}
  {entered : EnteredPath models prepared
    differential parentSheet} {target : Coordinate}

/-- Endpoint ownership discrepancies are paid by the same fragment budget as corner readback, even when the points use
different local grid owners. -/
theorem point_accurate (reference : PrimitiveReferences.Reference entered target) {index : Nat}
    (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = base) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) - reference.value) < target
      := by
  rw [reference.value_eq]
  exact SharedPointRequests.point_accurate entered
    (entered.requestSharedWith reference.budget index later data reference.request reference.minimum)
    data (entered.requestSharedWith_usesData ..) readings first last firstEq lastEq

/-- Any sufficiently refined pair of actual cached endpoint readings satisfies the original fixed primitive-reference
magnitude bound. -/
theorem point_bounded (reference : PrimitiveReferences.Reference entered target) {index : Nat}
    (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = base) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq (readings.values last - readings.values first) ≤ reference.bound := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((readings.values last - readings.values first) - reference.value) reference.value).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct
        (point_accurate reference later data readings
          first last firstEq lastEq).le le_rfl) (by decide))
  rw [sub_add_cancel, ← reference.bound_eq] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointReferences
