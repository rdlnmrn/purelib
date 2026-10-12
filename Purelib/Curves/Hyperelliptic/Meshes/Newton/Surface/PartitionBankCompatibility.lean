module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
public import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionCompatibility
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Vector

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonObservationSurfacePartition

@[expose] public section

/-! The canonical complete-surface partition bank supplies all transverse
compatibility certificates needed to construct neighboring-face contacts. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original}

/-- Cache the canonical observation partition for every original regular face in its exact retained index order. -/
def build (observations : NewtonProtectedObservations.ProtectedObservations original) (grid : BranchCellBank.NewtonGrid
  preparation target radius) :
    NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid :=
  DependentVector.ofFn (SurfacePartition.build observations grid)

/-- The retained surface partition bank has matching transverse interval lists on every pair of original adjacent
regular faces. -/
structure Compatible (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid) : Prop where
  /-- Vertically adjacent original faces retain identical horizontal partition intervals. -/ horizontal : ∀ first last,
    GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
    (grid.faces.regulars[last.val]'last.isLt).cell.box →
    (partitions.get first).cuts.x.intervals = (partitions.get last).cuts.x.intervals
  /-- Horizontally adjacent original faces retain identical vertical partition intervals. -/ vertical : ∀ first last,
    GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
    (grid.faces.regulars[last.val]'last.isLt).cell.box →
    (partitions.get first).cuts.y.intervals = (partitions.get last).cuts.y.intervals

/-- The canonical complete-surface observation partition bank satisfies both original side compatibility conditions. -/
theorem build_compatible (observations : NewtonProtectedObservations.ProtectedObservations original) (grid :
  BranchCellBank.NewtonGrid preparation target radius) :
    Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.Compatible
      (Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.build observations grid) := by
  constructor
  · intro first last matching
    dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.build]
    rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
    exact PartitionCompatibility.build_x_compatible observations grid first last matching.1 matching.2.1
  · intro first last matching
    dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility.build]
    rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
    exact PartitionCompatibility.build_y_compatible observations grid first last matching.1 matching.2.1

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
