module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Branches.NewtonCutAreaRequests
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.NewtonCutAreaRequests

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision

open Purelib.Topology.Surface.Sewing

public section

/-!
# One requested source-area correction for all retained Newton holes

The budget is chosen before the grid. Preparations follow the actual excision
entries, retaining their source occurrences and owner threads. All comparisons
share one domain bank and one late index. Numerical summaries retain each
complete polygon separately: the sum below is not the polygon of block totals.
The same request also pays the inherited cut-primitive sewing error. The
annular consumer retains every inner boundary, cut jump and origin offset.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest outerCount)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

namespace NewtonGrid

variable {grid : NewtonGrid preparation target
  radius} {lifted : LiftedPuncturedGrid grid.punctured}

set_option genInjectivity false in
/-- Geometry is shared by every differential, including the original cover and the cached list of oriented source
occurrences. -/
structure AnnularEntry.Prepared (grid : BranchCellBank.NewtonGrid preparation target radius)
    (lifted : Meshes.LiftedPuncturedGrid grid.punctured) where
  /-- The exact annular excision entry whose source occurrences are prepared. -/ entry : Excision.AnnularEntry grid
    lifted
  /-- The cached complete outer source preparation on this actual annular region. -/ outer : Lifted.OuterPreparation
    entry.region

constructive_injectivity AnnularEntry.Prepared

/-- Cache the complete actual outer source preparation on the supplied original annular excision entry. -/
@[expose] def AnnularEntry.Prepared.build (entry : Excision.AnnularEntry grid lifted) :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared grid lifted :=
  ⟨entry, OuterPreparation.build entry.region⟩

set_option genInjectivity false in
/-- The complete ordered source-preparation bank on the original all-hole excision. -/
structure AllHoleExcision.OuterPreparations (excision : Excision.AllHoleExcision grid lifted) where
  /-- The cached source preparations in the original excision-entry order. -/ entries : List
    (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared grid lifted)
  /-- The prepared bank projects to exactly the original excision entry list. -/ entries_eq : entries.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared.entry =
    excision.entries

constructive_injectivity AllHoleExcision.OuterPreparations

/-- Prepare every original excision entry once, preserving its actual source order. -/
@[expose] def AllHoleExcision.OuterPreparations.build (excision : Excision.AllHoleExcision grid lifted) :
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision) :=
  ⟨excision.entries.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared.build, by
    induction excision.entries with
    | nil => rfl
    | cons entry tail ih => exact congrArg (List.cons entry) ih⟩

end NewtonGrid

namespace NewtonPreparation

set_option genInjectivity false in
/-- Both occurrence and hole caps depend only on the fixed original bank. The per-hole allowance is cached before any
requested geometry is acquired. -/
structure FamilyAreaRequest (preparation : BranchCellBank.NewtonPreparation original) (target radius :
  Fraction.Rational) where
  /-- The requested whole all-hole squared-norm target is strictly positive. -/ positive : 0 < target
  /-- The cached upper bound on the number of actual excision holes. -/ count : Nat
  /-- The count cap is exactly the original outer-occurrence bound squared. -/ count_eq : count =
    (NewtonPreparation.outerCount preparation) ^ 2
  /-- The cached local squared-norm allowance for one actual hole. -/ perHole : Fraction.Rational
  /-- The local allowance is the original whole target allocated over the retained count cap. -/ perHole_eq : perHole =
    Aggregate.perTerm target count
  /-- The retained Newton grid and single-annulus request at one quarter of the local allowance. -/ single :
    NewtonPreparation.AreaRequest preparation (perHole / 4) radius

constructive_injectivity FamilyAreaRequest

namespace FamilyAreaRequest

/-- Allocate the original all-hole target before constructing the shared Newton grid and local annular request. -/
@[expose] def build (preparation : BranchCellBank.NewtonPreparation original) (target radius : Fraction.Rational)
    (positive : 0 < target) (radiusPositive : 0 < radius) :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation
      target radius :=
  let count := (NewtonPreparation.outerCount preparation) ^ 2
  let perHole := Aggregate.perTerm target count
  ⟨positive, count, rfl, perHole, rfl,
    AreaRequest.build preparation (perHole / 4) radius
      (Fraction.Order.Field.div_pos_direct (Aggregate.perTerm_positive positive count) (by decide)) radiusPositive⟩

variable {request :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}

/-- The retained per-hole allowance is strictly positive. -/
theorem perHole_positive (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius) : 0 < request.perHole := by
  rw [request.perHole_eq]
  exact Aggregate.perTerm_positive request.positive request.count

/-- One quarter of the retained local allowance is at most the full local allowance. -/
theorem quarter_le (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius) : request.perHole / 4 ≤ request.perHole := by
  calc
    request.perHole / 4 = 1 * (request.perHole / 4) := by ring1
    _ ≤ 4 * (request.perHole / 4) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Fraction.Rational) ≤ 4) request.single.budget.positive.le
    _ = request.perHole := (mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- The actual original excision entry count is bounded by the retained hole cap. -/
theorem entries_count (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius)
    {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
    (excision : Excision.AllHoleExcision request.single.grid lifted) : excision.entries.length ≤ request.count := by
  have count := congrArg List.length excision.holes_eq
  rw [List.Map.length_map] at count
  rw [request.count_eq]
  exact count.le.trans request.single.holes_count

set_option genInjectivity false in
/-- One actual prepared annular source with its differential-specific sewing request on the shared domains. -/
structure ComparedAnnulus (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius)
    (lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured) (differential : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) where
  /-- The exact prepared original annular source consumed by this comparison. -/ source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared request.single.grid
    lifted
  /-- The cached sewn comparison on this exact annular source, differential and shared domain bank. -/ sewn :
    NewtonCutAreaRequests.SewnRequest request.single source.outer differential domains 0

constructive_injectivity ComparedAnnulus

namespace ComparedAnnulus

variable {differential : Fin genus} {domains :
  FaceDomainBank lifted.frames
  request.single.grid.faces.regulars}

/-- Prepare the supplied annular source's sewing request for one differential on the shared domain bank. -/
@[expose] def build (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius)
    {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured} (differential : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars)
    (source : Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared
      request.single.grid lifted) :
      FamilyAreaRequest.ComparedAnnulus
      request lifted differential domains :=
  ⟨source, SewnRequest.build request.single source.outer differential domains 0⟩

open
  FamilyAreaRequest.ComparedAnnulus
  in
/-- Read the maximum contact stage of the actual compared annuli, retaining zero for an empty list. -/
@[expose] def index : List
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
  request lifted differential domains) → Nat
  | [] => 0
  | entry :: tail => max entry.sewn.sewing.contact.index (index tail)

open
  FamilyAreaRequest.ComparedAnnulus
  in
/-- Every actual annular contact request is paid at the complete retained entry maximum. -/
theorem index_le : ∀ (entries : List
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
  request lifted differential domains)) (entry),
    entry ∈ entries → entry.sewn.sewing.contact.index ≤ index entries
  | [], _, member => (List.not_mem_nil member).elim
  | first :: tail, entry, member => by
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact Nat.Order.le_max_left _ _
      · exact
          (index_le
          tail entry member).trans (Nat.Order.le_max_right _ _)

end ComparedAnnulus

set_option genInjectivity false in
/-- The original prepared entries and all numerical reference stages are cached; adding another differential does not
reprepare their owner paths. -/
structure Comparison (prepared :
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision)) (differential : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) where
  /-- The cached ordered differential-specific comparisons on the original prepared annuli. -/ entries : List
    (ComparedAnnulus
    request lifted differential domains)
  /-- The compared annuli project to exactly the original prepared source list. -/ entries_eq : entries.map
    ComparedAnnulus.source
    = prepared.entries
  /-- The cached common stage paying every actual annular sewing request. -/ index : Nat
  /-- The cached comparison stage is exactly the maximum of all actual annular contact stages. -/ index_eq : index =
    ComparedAnnulus.index
    entries

constructive_injectivity Comparison

namespace Comparison

variable {prepared :
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision)} {differential : Fin genus}
  {domains : FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

/-- Reuse the original prepared annuli and shared domains to cache all differential-specific comparisons and their
common stage. -/
@[expose] def build (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius)
    {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
    {excision : Excision.AllHoleExcision request.single.grid lifted}
    (prepared :
      (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
      excision)) (differential : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
      prepared differential domains :=
  let entries := prepared.entries.map
    (ComparedAnnulus.build
    request differential domains)
  ⟨entries, by
    dsimp only [entries]
    induction prepared.entries with
    | nil => rfl
    | cons source tail ih => exact congrArg (List.cons source) ih,

      ComparedAnnulus.index
      entries, rfl⟩

/-- The number of actual compared annuli is bounded by the original request's hole cap. -/
theorem entries_count (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains) : comparison.entries.length ≤ request.count := by
  have first := congrArg List.length comparison.entries_eq
  have second := congrArg List.length prepared.entries_eq
  rw [List.Map.length_map] at first second
  exact first.le.trans (second.le.trans (request.entries_count excision))

/-- Every member annular contact request is paid at any stage above the retained comparison stage. -/
theorem later (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains)
    (entry :
      ComparedAnnulus
      request lifted differential domains) (member : entry ∈ comparison.entries)
    {stage : Nat} (late : comparison.index ≤ stage) : entry.sewn.sewing.contact.index ≤ stage :=

    (ComparedAnnulus.index_le
    comparison.entries entry member).trans (comparison.index_eq ▸ late)

set_option genInjectivity false in
/-- A summary of the full cumulative source polygon, not merely its final increment. Its semantic equations also admit
externally generated samples. -/
structure Term {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential)
  stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) where
  /-- The exact original compared annulus whose complete source polygon is summarized. -/ source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
    request lifted differential domains
  /-- The cached complete increment and area summary of the actual original source occurrence path. -/ data :
    IncrementArea.Summary (source.source.outer.sources.map (fun edge => edge.increment readings.values))

constructive_injectivity Term

namespace Term

variable {stage : Nat} {shared : FacePrimitiveBank
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh}

/-- Cache the complete polygon summary of this exact original annular source under the supplied shared readings. -/
@[expose] def build (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (source :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
  request lifted differential domains) :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Term
      readings :=
  ⟨source, IncrementArea.Summary.build (source.source.outer.sources.map (fun edge => edge.increment readings.values))⟩

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The actual complete source polygon area satisfies the retained per-hole allowance at a paid stage. -/
theorem area_bound (term :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Term
  readings) (later : term.source.sewn.sewing.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq term.data.area < request.perHole := by
  rw [term.data.area_eq]
  exact (request.single.source_area_accurate term.source.sewn.comparison.original
    (term.source.sewn.sewing.reference_later later) readings).trans_le request.quarter_le

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The actual source polygon total satisfies the retained per-hole allowance at a paid stage. -/
theorem total_bound (term :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Term
  readings) (later : term.source.sewn.sewing.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq term.data.total < request.perHole := by
  rw [term.data.total_eq]
  exact (request.single.source_total_accurate term.source.sewn.comparison.original
    (term.source.sewn.sewing.reference_later later) readings).trans_le request.quarter_le

end Term

set_option genInjectivity false in
/-- The complete actual source polygon summaries and their separate cached area and total sums.

The retained term ordering agrees with the original comparison entries, and every sum is linked to those exact
summaries. -/
structure Sample (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains) {stage : Nat}
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) where
  /-- The cached complete source polygon terms in original comparison order. -/ terms : List
    (Term
    readings)
  /-- The retained polygon terms project to exactly the original comparison entries. -/ terms_eq : terms.map
    Term.source
    = comparison.entries
  /-- The cached ordered list of actual complete source polygon areas. -/ areas : List Data.Gaussian.Basic.Canonical
  /-- The area list is exactly the readback of the retained term summaries. -/ areas_eq : areas = terms.map (fun term =>
    term.data.area)
  /-- The cached ordered list of actual source polygon totals. -/ totals : List Data.Gaussian.Basic.Canonical
  /-- The total list is exactly the readback of the retained term summaries. -/ totals_eq : totals = terms.map (fun term
    => term.data.total)
  /-- The cached sum of all actual complete source polygon areas. -/ area : Data.Gaussian.Basic.Canonical
  /-- The area cache is exactly the Gaussian sum of the retained polygon-area list. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum areas
  /-- The cached sum of all actual source polygon totals. -/ total : Data.Gaussian.Basic.Canonical
  /-- The total cache is exactly the Gaussian sum of the retained total list. -/ total_eq : total =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum totals

constructive_injectivity Sample

namespace Sample

variable {comparison :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains} {stage : Nat}
  {shared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh}

/-- Cache every original source polygon summary and its separate area and total readbacks on the supplied shared
readings. -/
@[expose] def build (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains) (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :

      Comparison.Sample
      comparison readings :=
  let terms := comparison.entries.map
    (Term.build
    readings)
  let areas := terms.map (fun term => term.data.area)
  let totals := terms.map (fun term => term.data.total)
  { terms := terms
    terms_eq := by
      dsimp only [terms]
      induction comparison.entries with
      | nil => rfl
      | cons source tail ih => exact congrArg (List.cons source) ih
    areas := areas, areas_eq := rfl, totals := totals, totals_eq := rfl
    area := Data.Gaussian.Norm.Sum.Basic.gaussianSum areas, area_eq := rfl, total :=
      Data.Gaussian.Norm.Sum.Basic.gaussianSum totals, total_eq := rfl }

/-- The actual retained term count is bounded by the original request's hole cap. -/
theorem terms_count (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) : sample.terms.length ≤ request.count := by
  have count := congrArg List.length sample.terms_eq
  rw [List.Map.length_map] at count
  exact count.le.trans comparison.entries_count

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- Every actual retained term is paid at any stage above the original comparison request. -/
theorem term_later (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) (later : comparison.index ≤ stage)
    (term :
      Term
      readings) (member : term ∈ sample.terms) : term.source.sewn.sewing.contact.index ≤ stage :=
  comparison.later term.source (sample.terms_eq ▸ Map.mem_map_of_mem member) later

/-- A list within the retained hole cap and local allowance has total squared norm below the original target. -/
private theorem sum_paid (request :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
  radius) (values : List Data.Gaussian.Basic.Canonical)
    (count : values.length ≤ request.count) (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value
      ≤ request.perHole) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) < target := by
  have estimate := IncrementArea.sum_bound_of_length request.perHole_positive.le bounded count
  rw [request.perHole_eq] at estimate
  exact estimate.trans_lt ((show (request.count : Fraction.Rational) ^ 2 * Aggregate.perTerm target request.count =
    (request.count : Fraction.Rational) * ((request.count : Fraction.Rational) * Aggregate.perTerm target request.count)
      by ring1).trans_lt
      (Aggregate.count_mul_perTerm_lt request.positive request.count))

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- Every original hole contributes its own complete source polygon. Both the number of holes and the later numerical
indices have been paid. -/
theorem area_accurate (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) (later : comparison.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.area <
  target := by
  rw [sample.area_eq]
  apply
    sum_paid
    request sample.areas
  · rw [sample.areas_eq, List.Map.length_map]
    exact sample.terms_count
  · intro value member
    rw [sample.areas_eq] at member
    obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact (term.area_bound (sample.term_later later term member)).le

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The cached complete source-total sum satisfies the original all-hole target at every paid stage. -/
theorem total_accurate (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) (later : comparison.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.total <
  target := by
  rw [sample.total_eq]
  apply
    sum_paid
    request sample.totals
  · rw [sample.totals_eq, List.Map.length_map]
    exact sample.terms_count
  · intro value member
    rw [sample.totals_eq] at member
    obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact (term.total_bound (sample.term_later later term member)).le

/-- The cached result is the sum of the original prepared source polygons, not the area of their total increments or of
a freshly prepared tour. -/
theorem area_eq_source_polygons (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) :
    sample.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.entries.map (fun entry =>
      IncrementArea.pathArea (entry.outer.sources.map (fun edge => edge.increment readings.values)))) := by
  have first := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
    request lifted differential domains =>
    IncrementArea.pathArea (source.source.outer.sources.map (fun edge => edge.increment readings.values))))
      sample.terms_eq
  have second := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared request.single.grid
    lifted =>
    IncrementArea.pathArea (source.outer.sources.map (fun edge => edge.increment readings.values))))
      comparison.entries_eq
  simp only [-eq_self, -iff_self, List.Map.map_map, Function.comp_def] at first second
  have values : sample.terms.map (fun term => term.data.area) = sample.terms.map (fun term =>
      IncrementArea.pathArea (term.source.source.outer.sources.map (fun edge => edge.increment readings.values))) := by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg₂ List.cons term.data.area_eq ih
  exact sample.area_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.areas_eq.trans
    (values.trans (first.trans second))))

/-- The cached total sum reads exactly the original prepared source occurrence totals. -/
theorem total_eq_source_totals (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) :
    sample.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.entries.map (fun entry =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entry.outer.sources.map (fun edge => edge.increment
        readings.values)))) := by
  have first := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
    request lifted differential domains =>
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (source.source.outer.sources.map (fun edge => edge.increment
      readings.values)))) sample.terms_eq
  have second := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared request.single.grid
    lifted =>
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (source.outer.sources.map (fun edge => edge.increment
      readings.values)))) comparison.entries_eq
  simp only [-eq_self, -iff_self, List.Map.map_map, Function.comp_def] at first second
  have values : sample.terms.map (fun term => term.data.total) = sample.terms.map (fun term =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (term.source.source.outer.sources.map (fun edge => edge.increment
        readings.values))) := by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg₂ List.cons term.data.total_eq ih
  exact sample.total_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.totals_eq.trans
    (values.trans (first.trans second))))

/-- Exact order and coverage of the physical tours used by excision, including each tour's sheet-aware vertex labels. -/
theorem outer_words (sample :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) :
    sample.terms.map (fun term => term.source.source.outer.sources.map
      (fun edge => edge.project lifted.mesh.triangulation.faces)) = excision.entries.map (fun entry =>
        entry.region.outer) := by
  have first := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.ComparedAnnulus
    request lifted differential domains =>
    source.source.entry.region.outer)) sample.terms_eq
  have second := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared request.single.grid
    lifted =>
    source.entry.region.outer)) comparison.entries_eq
  have third := congrArg (List.map (fun entry : Excision.AnnularEntry request.single.grid lifted => entry.region.outer))
    prepared.entries_eq
  simp only [-eq_self, -iff_self, List.Map.map_map, Function.comp_def] at first second third
  have projected : sample.terms.map (fun term => term.source.source.outer.sources.map
      (fun edge => edge.project lifted.mesh.triangulation.faces)) =
      sample.terms.map (fun term => term.source.source.entry.region.outer) := by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg₂ List.cons term.source.source.outer.sources_project ih
  exact projected.trans (first.trans (second.trans third))

end Sample

open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)

set_option genInjectivity false in
/-- Each annulus consumes its already retained source term and request. The selected triangles and all cut contributions
are cached with the sample. -/
structure AnnularTerm {stage : Nat}
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) where
  /-- The actual retained complete source term reused by this annular sample. -/ source :
    Term
    readings
  /-- The cached actual triangle selection for this exact original annular excision entry. -/ selected :
    CachedSample.FaceSelection surface (AllHoleExcision.sourceMask source.source.source.entry)
  /-- The cached annular comparison retaining all actual inner-boundary and cut corrections. -/ data :
    CutRequests.AnnularSample ⟨source.source.source.entry, selected⟩
    source.source.source.outer source.source.sewn

constructive_injectivity AnnularTerm

namespace AnnularTerm

variable {stage : Nat} {shared : FacePrimitiveBank
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {surface : CachedSample lifted.cutPolygon.patch
    readings.values}

/-- Cache the actual annular triangle selection and full correction using the supplied original source term and shared
sewn surface. -/
@[expose] def build (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) (source :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Term
  readings) :
  Comparison.AnnularTerm
  readings surface :=
  let selected := FaceSelection.build surface (AllHoleExcision.sourceMask source.source.source.entry)
  ⟨source, selected, AnnularSample.build ⟨source.source.source.entry, selected⟩
    source.source.source.outer source.source.sewn⟩

/-- Read the original sewn annulus using its retained source entry and already cached triangle selection. -/
@[expose] def annulus (term :
  Comparison.AnnularTerm
  readings surface) : AllHoleExcision.SewnAnnulus surface := ⟨term.source.source.source.entry, term.selected⟩

/-- Read the actual selected annular area minus its complete retained correction. -/
@[expose] def difference (term :
  Comparison.AnnularTerm
  readings surface) : Gaussian := term.selected.area - term.data.correction

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The actual annular area residual satisfies the retained local allowance at a paid stage. -/
theorem accurate (term :
  Comparison.AnnularTerm
  readings surface) (later : term.source.source.sewn.sewing.contact.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq term.difference < request.perHole := term.data.accurate later

end AnnularTerm

variable {comparison :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains}

set_option genInjectivity false in
/-- All physical holes occur in the original order. The same selected triangle caches form the actual excision; they are
not selected again. -/
structure SewnSample {stage : Nat}
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains}
    {readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh}
    (source :
      Sample
      comparison readings) (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) where
  /-- The cached annular samples in the exact original physical-hole order. -/ terms : List
    (AnnularTerm
    readings surface)
  /-- The annular samples reuse exactly the original retained source terms. -/ terms_eq : terms.map
    AnnularTerm.source
    = source.terms
  /-- The actual sewn excision consuming these same cached triangle selections. -/ retained : AllHoleExcision.Sewn
    excision surface
  /-- The retained sewn excision uses exactly the cached annular terms and selections. -/ annuli_eq : retained.annuli =
    terms.map
    AnnularTerm.annulus
  /-- The cached sum of all actual inner-boundary, jump, defect and occurrence corrections. -/ correction :
    Data.Gaussian.Basic.Canonical
  /-- The correction cache is exactly the Gaussian sum of the retained annular corrections. -/ correction_eq :
    correction = Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.correction))
  /-- The cached sum of actual corrected annular-area residuals. -/ difference : Data.Gaussian.Basic.Canonical
  /-- The residual cache is exactly the sum of actual selected-area minus correction discrepancies. -/ difference_eq :
    difference = Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    AnnularTerm.difference)

constructive_injectivity SewnSample

namespace SewnSample

variable {comparison :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  prepared differential domains} {stage : Nat}
  {shared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {source :
    Sample
    comparison readings}
  {surface : CachedSample lifted.cutPolygon.patch readings.values}

/-- Build each actual annular selection once and retain those same selections in the complete excision and correction
sums. -/
@[expose] def build (source :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample
  comparison readings) (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values) :

      Comparison.SewnSample
      source surface := by
  let terms := source.terms.map
    (AnnularTerm.build
    surface)
  have terms_eq : terms.map
    AnnularTerm.source
    = source.terms := by
    dsimp only [terms]
    induction source.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg (List.cons term) ih
  let annuli := terms.map
    AnnularTerm.annulus
  have sources_eq : annuli.map SewnAnnulus.source = excision.entries := by
    dsimp only [annuli]
    rw [List.Map.map_map]
    have first := congrArg (List.map (fun term :
      Term
      readings => term.source.source.entry)) terms_eq
    have second := congrArg (List.map (fun entry :
      ComparedAnnulus
      request lifted differential domains => entry.source.entry)) source.terms_eq
    have third := congrArg (List.map (fun entry :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared
      request.single.grid lifted => entry.entry)) comparison.entries_eq
    simp only [-eq_self, -iff_self, List.Map.map_map, Function.comp_def] at first second third
    exact first.trans (second.trans (third.trans prepared.entries_eq))
  let retained : AllHoleExcision.Sewn excision surface :=
    { annuli := annuli
      sources_eq := sources_eq
      remaining := FaceSelection.build surface
        (fun index => !(excision.entries.any (fun entry => AllHoleExcision.sourceMask entry index)))
      annularArea := CellBoundary.sumValues (fun annulus => annulus.selected.area) annuli
      annularArea_eq := rfl }
  exact ⟨terms, terms_eq, retained, rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.correction)), rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      AnnularTerm.difference),
      rfl⟩

/-- The actual retained term count is bounded by the original request's hole cap. -/
theorem terms_count (sample :
  Comparison.SewnSample
  source surface) : sample.terms.length ≤ request.count := by
  have count := congrArg List.length sample.terms_eq
  rw [List.Map.length_map] at count
  exact count.le.trans source.terms_count

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- Every actual retained term is paid at any stage above the original comparison request. -/
theorem term_later (sample :
  Comparison.SewnSample
  source surface) (later : comparison.index ≤ stage)
    (term :
      AnnularTerm
      readings surface) (member : term ∈ sample.terms) :
    term.source.source.sewn.sewing.contact.index ≤ stage :=
  source.term_later later term.source (sample.terms_eq ▸ Map.mem_map_of_mem member)

/-- The residual uses the actual annular areas and the sum of their full displayed corrections; areas of block totals
are never substituted. -/
theorem corrected_eq (sample :
  Comparison.SewnSample
  source surface) :
    sample.retained.annularArea - sample.correction = sample.difference := by
  rw [sample.retained.annularArea_eq, sample.annuli_eq, sample.correction_eq, sample.difference_eq]
  have area : CellBoundary.sumValues (fun annulus => annulus.selected.area) (sample.terms.map
    AnnularTerm.annulus)
    =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map (fun term => term.selected.area)) := by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg (term.selected.area + ·) ih
  rw [area]
  have equal : ∀ terms : List
    (AnnularTerm
    readings surface),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.selected.area)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.correction)) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
          AnnularTerm.difference)
          := by
    intro terms
    induction terms with
    | nil => change (0 : Data.Gaussian.Basic.Canonical) - 0 = 0; ring1
    | cons term tail ih =>
        change (term.selected.area + Data.Gaussian.Norm.Sum.Basic.gaussianSum _) - (term.data.correction +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum _) =
          term.selected.area - term.data.correction + Data.Gaussian.Norm.Sum.Basic.gaussianSum _
        rw [← ih]
        ring1
  exact equal sample.terms

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The cached complete corrected annular residual satisfies the original all-hole target at every paid stage. -/
theorem accurate (sample :
  Comparison.SewnSample
  source surface) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq sample.difference < target := by
  rw [sample.difference_eq]
  apply
    Sample.sum_paid
    request
  · rw [List.Map.length_map]
    exact sample.terms_count
  · intro value member
    obtain ⟨term, member, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact (term.accurate (sample.term_later later term member)).le

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The full actual annular-area sum minus its retained correction satisfies the original all-hole target. -/
theorem annular_accurate (sample :
  Comparison.SewnSample
  source surface) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.annularArea - sample.correction) < target := by
  rw [sample.corrected_eq]
  exact sample.accurate later

/-- Feed the all-hole correction through the exact retained-triangle partition. This consumes the same shared surface
and every physical hole. -/
theorem remaining_eq (sample :
  Comparison.SewnSample
  source surface) :
    sample.retained.remaining.area - (surface.boundaryArea - sample.correction) = -sample.difference := by
  rw [sample.retained.remaining_area, ← sample.corrected_eq]
  ring1

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- The retained remaining-triangle area agrees with the corrected original surface boundary within the all-hole target.
-/
theorem remaining_accurate (sample :
  Comparison.SewnSample
  source surface) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.remaining.area - (surface.boundaryArea -
      sample.correction)) < target := by
  rw [sample.remaining_eq, Data.Gaussian.Norm.Basic.normSq_neg]
  exact sample.accurate later

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison
  in
/-- A period-area estimate and all Newton holes share one additive error budget. The correction remains explicit until
its global cancellation. -/
theorem period_accurate (sample :
  Comparison.SewnSample
  source surface) (later : comparison.index ≤ stage)
    (periodArea : Data.Gaussian.Basic.Canonical) (periodBound : Data.Gaussian.Norm.Basic.normSq
      (surface.boundaryArea - periodArea) < target) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.remaining.area - (periodArea - sample.correction)) < 4 *
      target := by
  have error : sample.retained.remaining.area - (periodArea - sample.correction) =
      (surface.boundaryArea - periodArea) - sample.difference := by
    rw [sample.retained.remaining_area, ← sample.corrected_eq]
    ring1
  rw [error]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct periodBound (sample.accurate later))).trans_eq (by ring1))

end SewnSample
end Comparison
end FamilyAreaRequest
end NewtonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
