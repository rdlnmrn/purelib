module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Data.Rat.Fraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Roots.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerNegation
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

@[expose] public section

/-!
# Operational root negation after the actual branch-hole lap

The shared grid transports prove that one inward lap reaches the other
retained owner. The cached frame comparison identifies that owner's actual
root name with the negative of the initial name and supplies a finite tail
bound for the sum of the endpoint root readings.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchRootNegation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootOwnerNegation (Negation SumRequest)
open Purelib.Riemann.RootContinuation.SquareRootDifferentialNegation.OwnerFrame
open Purelib.Riemann.RootContinuation.GridRootWalks.BranchCellBank
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Exact rational targets and quantitative root-comparison allowances. -/
abbrev Coordinate := Fraction.Rational

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

/-- The cache refers to the same anchor frame used by every retained grid edge in the hole tour. -/
def rootNegation (hole : PuncturedGridFaces.BranchHole bank) (sheet : Fin 2) :
    RootOwnerNegation.Negation (frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)) sheet :=
  RootOwnerNegation.negation
    (frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)) sheet

variable (hole : Purelib.Riemann.Meshes.PuncturedGridFaces.BranchHole bank) (edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (sheet : Fin 2)
  (data : Purelib.Riemann.RootContinuation.RootOwnerNegation.Negation (frames.frameAt hole.cell.box.anchor
    (hole.cell.anchor_mem hole.member)) sheet)

/-- This endpoint is the endpoint of `edges.trace hole.inwardBoundary`: the actual prepared edge transports, including
their same-root handoffs. -/
def root_after_lap :
    Gaussian.Equivalence.NamedEquivalent
      (Named.neg
        (OwnerTraceReadings.ownerName ((frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)).owners
          sheet)))
      (OwnerTraceReadings.ownerName ((frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)).owners
        (RootEdgeBank.target edges hole.inwardBoundary sheet))) := by
  rw [Riemann.RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap hole
    edges sheet]
  exact data.equivalent

/-- One request bounds both endpoint root readings at all later indices. It consumes the retained negation cache and
does not prepare the lap again. -/
def rootSumRequest (start : Nat) (target : Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchRootNegation.Coordinate)
  (positive : 0 < target) :
    RootOwnerNegation.SumRequest
      (OwnerTraceReadings.ownerName ((frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)).owners
        sheet))
      (OwnerTraceReadings.ownerName ((frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)).owners
        (RootEdgeBank.target edges hole.inwardBoundary sheet))) start target := by
  rw [Riemann.RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap hole
    edges sheet]
  exact data.request start target positive

/-- The ordinary named differential values at the initial and actual one-lap endpoint roots cancel. This is a
coefficient identity; integration and primitive-area comparisons still retain their own error terms. -/
def differential_after_lap (differential : Differentials.Basic.Differential genus) :
    let frame := frames.frameAt hole.cell.box.anchor (hole.cell.anchor_mem hole.member)
    let first := (frame.owners sheet).certificate (frame.owners sheet).parameterNonzero
    let second := (frame.owners (RootEdgeBank.target edges hole.inwardBoundary sheet)).certificate
      (frame.owners (RootEdgeBank.target edges hole.inwardBoundary sheet)).parameterNonzero
    Gaussian.Equivalence.NamedEquivalent
      ((Value.differentialValue differential hole.cell.box.anchor first.value first.apart).add
        (Value.differentialValue differential hole.cell.box.anchor second.value second.apart)).name
      (Named.exact 0) := by
  rw [Riemann.RootContinuation.GridRootWalks.BranchCellBank.BranchHole.sharedTransport_swap hole
    edges sheet]
  exact Negation.differential_sum_zero
    data differential hole.cell.box.anchor

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchRootNegation
