module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Winding

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation.RootPathTransport

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Original period-fragment owners in the shared face bank

The complete clear grid edge supplies a winding reference at an interior
fragment endpoint. The incoming root is continued from the original request's
cached neighborhood, and its face model is read from the retained face bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
    (EdgePoint
    RegularPrimitiveFragment
  RegularPrimitiveFragments RegularPrimitiveSplits)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace SheetEntries.EdgePoint

/-- Transport the retained grid-vertex reference along the same certified line. No ambient enlargement or new polynomial
clearance is required. -/
def reference {start finish point : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge bank.grid start finish}
    (location : RegularFaces.EdgePoint edge point) : WindingOneLoop curve.polynomial point := by
  let raw := edge.segment.restrict edge.withinAmbient location.parameter 0 location.inside (by decide)
  let segment := (raw.castStart location.point_eq).castFinish edge.segment.pointAt_zero
  have within : segment.WithinAmbient :=
    (raw.castStart location.point_eq).castFinish_withinAmbient (raw.castStart_withinAmbient
      (edge.segment.restrict_withinAmbient edge.withinAmbient location.parameter 0 location.inside (by decide))
      location.point_eq) edge.segment.pointAt_zero
  let stem : Polynomial.Geometry.ClearPath curve.polynomial (Cuts.Ambient curve) point start := .cons segment (.nil _)
  have stemWithin : stem.WithinAmbient := .cons within (.nil _)
  let loop := BranchCellBank.referenceAt bank start edge.vertices.1
  exact
    { ambient := Cuts.Ambient curve
      path := (stem.append loop.walk.path).append (ClearPath.reverse stem)
      within := (stemWithin.append loop.walk.withinAmbient).append
        (ClearPath.reverse_withinAmbient stem stemWithin)
      winding := by
        rw [ClearPath.rawWinding_append, ClearPath.rawWinding_append, ClearPath.rawWinding_reverse, loop.winding]
        omega }

/-- The selected face-sheet entry of that exact incoming sample owner. -/
def entry {start finish point : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge bank.grid start finish}
    (location : RegularFaces.EdgePoint edge point) {face : PuncturedGridFaces.RegularFace bank}
    (models : BranchCellBank.FaceModels frames face) (inside : face.cell.box.Contains point)
    (owner : Owner (curve.polynomial.eval point)) : FaceModels.Entry models point owner :=
      by
  let route := Route.build face.clearance point face.cell.box.anchor inside face.cell.box.contains_anchor
  let returned := TracedPath.build route.path route.within owner
  let selected := models.frame.select returned.finishOwner
  refine ⟨selected.index, ?_⟩
  let forward := Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor inside
  let traced := TracedPath.build forward.path forward.within (models.frame.owners selected.index)
  let join := OwnerPath.join curve.polynomial face.cell.box.anchor returned.finishOwner
    (models.frame.owners selected.index) selected.equivalent
  let loop := returned.trace.get.append (join.append traced.trace.get)
  have winding : Polygon.Basic.chainRaw curve.polynomial point loop.vertices = 8 * (0 : Int) := by
    rw [OwnerPath.append_winding, OwnerPath.append_winding, TracedPath.winding_original returned,
      TracedPath.winding_original traced,
      OwnerPath.join_winding, Route.winding face.clearance (BranchIsolation.degreePositive curve) route inside,
      Route.winding face.clearance (BranchIsolation.degreePositive curve) forward face.cell.box.contains_anchor]
    omega
  have equivalent := OwnerPath.rootEquivalent_of_even_with_reference
    (reference location) loop 0 winding
  have reached : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners selected.index) traced.finishOwner
    :=
    ⟨traced.trace.get, (TracedPath.winding_original traced).trans
      (Route.winding face.clearance (BranchIsolation.degreePositive curve) forward face.cell.box.contains_anchor)⟩
  exact reached.append (Reached.ofEquivalent equivalent)

end SheetEntries.EdgePoint

variable {base : FramedPuncturedGrid curve branches higher} {frames :
  RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid} {parent :
    CenteredEdge curve source}
  {count : Nat} {target : Rational}

section Partitions

variable {cuts : List Rational} {partition : Partition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}

namespace SheetEntries.RegularPrimitiveFragment

/-- Retained face-cache lookup with the locator's exact face equality. -/
def domainCache (fragment : RegularFaces.RegularPrimitiveFragment axes parent partition interval)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) :
    DomainBanks.FaceDomains frames fragment.face.located.face :=
  domains.atLocation fragment.face.located

namespace SheetEntry

/-- The actual comparison from an original parent query to its retained fragment-start sample.

Both names keep their original parameter, interval bound and incoming
Point owners. The value supplies their executable finite-tail comparisons.
-/
def OriginalComparison (fragment : RegularFaces.RegularPrimitiveFragment axes parent partition interval)
    (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first)
    (fractionInside : 0 ≤ interval.lower ∧ interval.lower ≤ 1) :=
  Gaussian.Equivalence.NamedEquivalent
    (parent.edge.rootName interval.lower fractionInside) sample.certificate.value.name

end SheetEntry

section

attribute [local irreducible] SheetEntry.OriginalComparison

set_option genInjectivity false in
/-- The selected face occurrence names the original request root at the actual fragment start, including nonvertex and
reversed-edge starts. -/
structure SheetEntry (fragment : RegularFaces.RegularPrimitiveFragment axes parent partition interval)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars)
    (request : LocalRequest parent count target) where
  /-- The cached continuation sample at the actual retained fragment start. -/ sample : ContinuedNeighborhood.Point
    request.neighborhood fragment.located.first
  /-- The selected face-sheet entry of that exact incoming sample owner. -/ entry : FaceModels.Entry
    (bank := base.bank.toBranchCellBank) (frames := frames) (face := fragment.face.located.face)
    (domainCache fragment
      domains).models fragment.located.first sample.owner
  /-- The original fragment-start parameter lies in the unit parent interval. -/ fractionInside : 0 ≤ interval.lower ∧
    interval.lower ≤ 1
  /-- The actual signed comparison from the original parent query to this SAME incoming sample.

  Its executable finite-tail comparison is retained as data. It does not
  identify the parent and sample Owners or their independent requests. -/
  original : SheetEntry.OriginalComparison fragment request sample fractionInside
  /-- The cached local analytic domain for the selected entry sheet. -/ domain : Periods.PeriodDomain
    (domainCache fragment
    domains).models entry.sheet
  /-- The selected domain is exactly the shared face-bank entry, without reacquisition. -/ domain_eq : domain =
    (domainCache fragment
    domains).domain entry.sheet
  /-- The cached rectangular split of the actual retained fragment endpoints. -/ split :
    SegmentSplit domain.cuts fragment.located.first fragment.located.last

constructive_injectivity SheetEntry

end

namespace SheetEntry

/-- Acquire the original fragment-start sample, classify its actual sheet and retain the signed comparison and split.

The existing Point, Entry, selected domain and split operations keep their
original arguments and order. The original patch comparison is now actual
retained runtime work; its earlier proof-only wrapping was not a cache.
-/
def build (fragment : RegularFaces.RegularPrimitiveFragment axes parent partition interval)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars)
    (request : LocalRequest parent count target) :
      SheetEntry fragment
      domains request := by
  have bounds := partition.interval_bounds fragment.located.member
  have fractionInside : 0 ≤ interval.lower ∧ interval.lower ≤ 1 :=
    ⟨bounds.1, interval.ordered.le.trans bounds.2⟩
  have inside : request.neighborhood.box.Contains fragment.located.first := by
    rw [fragment.located.first_eq]
    exact (PrimitiveSplits.endpoints_inside partition fragment.located.member request).1
  let sample := ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.first inside
  have faceInside : fragment.face.located.face.cell.box.Contains fragment.located.first := by
    rw [fragment.face.located.cell_eq]
    exact fragment.first_inside
  let entry := EdgePoint.entry fragment.source.first
    (RegularPrimitiveFragment.domainCache fragment
    domains).models faceInside sample.owner
  let domain := (RegularPrimitiveFragment.domainCache
    fragment domains).domain entry.sheet
  have lastInside : fragment.face.located.face.cell.box.Contains fragment.located.last := by
    rw [fragment.face.located.cell_eq]
    exact fragment.last_inside
  let original : Gaussian.Equivalence.NamedEquivalent
      (parent.edge.rootName interval.lower fractionInside) sample.certificate.value.name := by
    rcases request with ⟨patch, neighborhood, neighborhoodEq, requested, finishInside⟩
    subst neighborhood
    exact patch.point_equivalent_at count interval.lower fractionInside fragment.located.first_eq.symm inside sample
  exact ⟨sample, entry, fractionInside, original, domain, rfl,
    SegmentSplit.build domain.cuts fragment.located.first fragment.located.last
      (domain.covers faceInside) (domain.covers lastInside)⟩

end SheetEntry
end SheetEntries.RegularPrimitiveFragment

end Partitions

variable {partition : Partition 0 1 (axes.parameters parent)}

section RegularPrimitiveFragments

set_option genInjectivity false in
/-- Every interval of this original parent has an assigned cached face occurrence; the dependent spine cannot omit a
difficult fragment. -/
inductive FragmentSheets (domains : DomainBanks.FaceDomainBank frames base.faces.regulars)
    (request : LocalRequest parent count target) :
    {intervals : List PreparedAxisPartitions.Interval} → RegularPrimitiveFragments axes parent partition
      intervals → Type
  /-- The empty sheet-entry bank for an empty retained fragment or parent spine. -/ | nil :
    FragmentSheets
    domains request .nil
  /-- Retain the entry for the actual first fragment or parent and the exact dependent tail. -/ | cons {interval :
    PreparedAxisPartitions.Interval} {intervals : List PreparedAxisPartitions.Interval}
      {head : RegularPrimitiveFragment axes parent partition interval}
      {tail : RegularPrimitiveFragments axes parent partition intervals}
      (first : SheetEntries.RegularPrimitiveFragment.SheetEntry head
        domains request)
      (remaining :
        FragmentSheets
        domains request tail) :
        FragmentSheets
        domains request (.cons head tail)

constructive_injectivity FragmentSheets

namespace FragmentSheets

/-- Read one actual original fragment and its whole stored SheetEntry at a bounded occurrence index.

The structural reader follows only the given sheet-entry spine. It runs
no fragment, sheet assignment, Point, Query, domain or split producer and
retains both the original geometric fragment and its actual cached entry.
-/
def «at» {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {request : LocalRequest parent count target} :
    ∀ {intervals : List PreparedAxisPartitions.Interval}
      {fragments : RegularPrimitiveFragments axes parent partition intervals},
      FragmentSheets domains request fragments → (position : Fin intervals.length) →
        Σ fragment : RegularPrimitiveFragment axes parent partition (intervals[position.val]'position.isLt),
          SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request
  | _, _, .nil, position => Fin.elim0 position
  | _, _, .cons (head := head) first _remaining, ⟨0, _bound⟩ => ⟨head, first⟩
  | _, _, .cons _first remaining, ⟨position + 1, bound⟩ =>
      «at» remaining ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- The zero index reads the complete actual head fragment and its original Entry unchanged. -/
theorem at_zero {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {request : LocalRequest parent count target} {interval : PreparedAxisPartitions.Interval}
    {intervals : List PreparedAxisPartitions.Interval}
    {head : RegularPrimitiveFragment axes parent partition interval}
    {tail : RegularPrimitiveFragments axes parent partition intervals}
    (first : SheetEntries.RegularPrimitiveFragment.SheetEntry head domains request)
    (remaining : FragmentSheets domains request tail) :
    «at» (.cons first remaining) ⟨0, Nat.zero_lt_succ intervals.length⟩ = ⟨head, first⟩ := by rfl

/-- A successor index reads the same bounded original tail, without rebuilding its head or assignment. -/
theorem at_succ {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {request : LocalRequest parent count target} {interval : PreparedAxisPartitions.Interval}
    {intervals : List PreparedAxisPartitions.Interval}
    {head : RegularPrimitiveFragment axes parent partition interval}
    {tail : RegularPrimitiveFragments axes parent partition intervals}
    (first : SheetEntries.RegularPrimitiveFragment.SheetEntry head domains request)
    (remaining : FragmentSheets domains request tail) (position : Fin intervals.length) :
    «at» (.cons first remaining) position.succ = «at» remaining position := by rfl

/-- Prepare complete sheet entries on the exact retained fragment and request spine using the supplied shared domain
bank. -/
def build (domains : DomainBanks.FaceDomainBank frames base.faces.regulars)
    (request : LocalRequest parent count target) :
    ∀ {intervals : List PreparedAxisPartitions.Interval} (fragments : RegularPrimitiveFragments axes parent
      partition intervals),
      FragmentSheets domains
        request fragments
  | _, .nil => .nil
  | _, .cons head tail => .cons
    (SheetEntries.RegularPrimitiveFragment.SheetEntry.build head
    domains request)
    (build
    domains request tail)

end FragmentSheets
end RegularPrimitiveFragments

section RegularPrimitiveSplits

set_option genInjectivity false in
/-- Complete sheet assignments for the exact original request and splitting spines. The shared domain bank is an input,
so no per-fragment bank is rebuilt. -/
inductive SplitSheets (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) :
    {parents : List (CenteredEdge curve source)} → {splits :
      PrimitiveSplits axes parents} →
      (fragments : RegularPrimitiveSplits (base := base) axes splits) →
      RequestedParents count target parents → Type 2
  /-- The empty sheet-entry bank for an empty retained fragment or parent spine. -/ | nil :
    SplitSheets domains
    .nil .nil
  /-- Retain the entry for the actual first fragment or parent and the exact dependent tail. -/ | cons {parent :
    CenteredEdge curve source} {parents : List (CenteredEdge
    curve source)}
      {partition : Partition 0 1 (axes.parameters parent)} {splits :
        PrimitiveSplits axes parents}
      {head : RegularPrimitiveFragments axes parent partition partition.intervals}
      {tail : RegularPrimitiveSplits (base := base) axes splits}
      {request : LocalRequest parent count target}
      {requests : RequestedParents count target parents}
      (first : FragmentSheets
        domains request head)
      (remaining :
        SplitSheets
        domains tail requests) :
        SplitSheets
        domains (.cons head tail) (.cons request requests)

constructive_injectivity SplitSheets

namespace SplitSheets

/-- Prepare complete sheet entries on the exact retained fragment and request spine using the supplied shared domain
bank. -/
def build (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) :
    ∀ {parents : List (CenteredEdge curve source)} {splits :
      PrimitiveSplits axes parents}
      (fragments : RegularPrimitiveSplits (base := base) axes splits)
      (requests : RequestedParents count target parents),
        SplitSheets domains
        fragments requests
  | _, _, .nil, .nil => .nil
  | _, _, .cons head tail, .cons request requests =>
      .cons
        (FragmentSheets.build
        domains request head)
        (build
        domains tail requests)

end SplitSheets
end RegularPrimitiveSplits
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
