module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Riemann.RootContinuation.RootOwnerFrames

@[expose] public section

/-!
# Original period-request signs in shared face models

The retained fragment entry supplies the operational root agreement. The
comparison reads the original request's polynomial index, including indices
zero and one. The analytic split propagates this initial sign to every cell.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differential genus}
  {axes : PrimitiveAxes base.bank.grid}
    {parent : CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}
  {inner : Purelib.Geometry.Rational.Box}

/-- A local cell's sign agrees with the original parent's operational query, even when the original parent extends
beyond this face. -/
theorem original_aligned (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (cell : TransportedFaceInverseModels.TransportedCell (RegularPrimitiveFragment.domainCache fragment
      domains).models.bounds
      ((RegularPrimitiveFragment.domainCache fragment domains).models.frame.owners assigned.entry.sheet) inner)
    (inside : inner.Contains fragment.located.first) (index : Nat) :
    InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index) fragment.located.first
      (parent.edge.rootName interval.lower assigned.fractionInside) := by
  let models := (RegularPrimitiveFragment.domainCache fragment domains).models
  let face := fragment.face.located.face
  obtain ⟨ownerTrace, winding⟩ := assigned.entry.reached
  let route := Route.build face.clearance face.cell.box.anchor fragment.located.first
    face.cell.box.contains_anchor (cell.geometry.refines.contains inside)
  let traced := TracedPath.build route.path route.within (models.frame.owners assigned.entry.sheet)
  let frame := OwnerFrame.build assigned.sample.owner.parameterNonzero
  have equivalent := TracedPath.equivalentOfOwnerPathSelections
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (face.cell.anchor_mem face.member)).toLoop route.within
      traced ownerTrace frame
    (frame.select traced.finishOwner) (frame.select assigned.sample.owner)
    ((Route.winding face.clearance (BranchIsolation.degreePositive curve) route face.cell.box.contains_anchor).trans
      winding.symm)
  have aligned : InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index) fragment.located.first
      (OwnerTraceReadings.ownerName traced.finishOwner) :=
    ContinuedComparison.trace_aligned cell source traced
      (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within face.cell.box.contains_anchor) frame inside
        index
  obtain ⟨original⟩ := assigned.original
  intro otherCount patch patchInside sample roots otherIndex
  exact aligned patch patchInside sample (equivalent.trans (original.symm.trans roots)) otherIndex

/-- No extra Newton-step floor is imposed on the already retained request. -/
theorem nearest (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (cell : TransportedFaceInverseModels.TransportedCell (RegularPrimitiveFragment.domainCache fragment
      domains).models.bounds
      ((RegularPrimitiveFragment.domainCache fragment domains).models.frame.owners assigned.entry.sheet) inner)
    (inside : inner.Contains fragment.located.first) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval fragment.located.first -
      (request.neighborhood.base.refine rightIndex).value.eval fragment.located.first) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval fragment.located.first +
      (request.neighborhood.base.refine rightIndex).value.eval fragment.located.first) := by
  have patchInside : request.neighborhood.box.Contains fragment.located.first := by
    rw [fragment.located.first_eq]
    exact (PrimitiveSplits.endpoints_inside partition fragment.located.member request).1
  obtain ⟨original⟩ := assigned.original
  exact PreparedPolynomialSheetReadings.nearest_at_index
    (original_aligned assigned cell inside
    leftIndex) inside
    request.neighborhood patchInside assigned.sample original rightIndex

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PrimitiveComparison
