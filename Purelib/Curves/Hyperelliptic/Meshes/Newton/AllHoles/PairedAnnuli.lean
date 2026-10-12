module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! Each corrected annular sample consumes its already retained paired
request and its original excision entry. Selected triangles are cached once. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample
open Purelib.Riemann.Topology.NewtonSewnExcision
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Term Sample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {stage : Nat}
  {firstBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential first) stage domains}
  {secondBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential second) stage domains}
  {left : TriangleReadings firstBank
    lifted.mesh} {right : TriangleReadings
    secondBank lifted.mesh}
  {firstSurface : CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : CachedSample lifted.cutPolygon.patch
    right.values}

set_option genInjectivity false in
/-- The original annular request evaluated on two retained sewn surfaces.

The selected triangles are cached on the actual first surface and used by the corrected paired annular sample. -/
structure AnnularTerm (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh)
    (firstSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (secondSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values) where
  /-- The original paired source term and its retained annular request. -/ source : PairedComparison.Term left right
  /-- The cached actual first-surface triangles selected by the original annular source mask. -/ selected :
    CachedSample.FaceSelection firstSurface (AllHoleExcision.sourceMask source.source.source.entry)
  /-- The corrected annular sample using that exact selection and the original second sewn surface. -/ data :
    PairedCutRequests.AnnularSample ⟨source.source.source.entry, selected⟩
    source.source.source.outer source.source.sewn secondSurface

constructive_injectivity AnnularTerm

namespace AnnularTerm

/-- Cache the actual selected first-surface triangles and evaluate the original annular request on both retained sewn
banks. -/
@[expose] def build (firstSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (secondSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values) (source :
      PairedComparison.Term left right) :

      PairedComparison.AnnularTerm
      left right firstSurface secondSurface :=
  let selected := FaceSelection.build firstSurface
    (AllHoleExcision.sourceMask source.source.source.entry)
  ⟨source, selected, AnnularSample.build
    ⟨source.source.source.entry, selected⟩ source.source.source.outer source.source.sewn secondSurface⟩

/-- The actual selected annular area minus its retained complete correction. -/
@[expose] def difference (term :
  PairedComparison.AnnularTerm
  left right firstSurface secondSurface) : Gaussian :=
  term.data.selectedArea - term.data.correction

/-- At its paid sewing stage, the original corrected annular area satisfies the retained per-hole target. -/
theorem accurate (term :
  PairedComparison.AnnularTerm
  left right firstSurface secondSurface)
    (later : term.source.source.sewn.sewing.stage ≤ stage) : Data.Gaussian.Norm.Basic.normSq term.difference <
      request.perHole :=
  term.data.accurate later

end AnnularTerm
variable {prepared :
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision)} {comparison :
  PairedComparison
  prepared first second domains}

set_option genInjectivity false in
/-- The cached selected areas, corrections and differences for every original annular term.

The ordered term readback binds the exact original source sample and both retained sewn surfaces. -/
structure SewnSample (source : PairedComparison.Sample comparison left right)
    (firstSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (secondSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values) where
  /-- The retained corrected annular terms on the two original sewn surface banks. -/ terms : List
    (AnnularTerm
    left right firstSurface secondSurface)
  /-- The annular terms project to exactly the original source sample's ordered terms. -/ terms_eq : terms.map
    AnnularTerm.source
    = source.terms
  /-- The cached sum of the actual selected annular triangle areas. -/ selectedArea : Data.Gaussian.Basic.Canonical
  /-- The selected-area cache is the sum of the retained actual term selections. -/ selectedArea_eq : selectedArea =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.selectedArea))
  /-- The cached complete sum of original annular correction terms. -/ correction : Data.Gaussian.Basic.Canonical
  /-- The correction cache is exactly the sum of the retained annular corrections. -/ correction_eq : correction =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.correction))
  /-- The cached sum of the original actual corrected annular differences. -/ difference : Data.Gaussian.Basic.Canonical
  /-- The cached difference is the sum of the actual retained corrected term differences. -/ difference_eq : difference
    = Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    AnnularTerm.difference)

constructive_injectivity SewnSample

namespace SewnSample

variable {source :
  PairedComparison.Sample
  comparison left right}

/-- Evaluate the exact original term list on the supplied sewn surfaces and cache all three complete area sums. -/
@[expose] def build (source : PairedComparison.Sample comparison left right)
    (firstSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (secondSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values) :

      PairedComparison.SewnSample
      source firstSurface secondSurface :=
  let terms := source.terms.map
    (AnnularTerm.build
    firstSurface secondSurface)
  ⟨terms, by
    dsimp only [terms, -eq_self, -iff_self]
    induction source.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg (List.cons term) ih,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.selectedArea)), rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => term.data.correction)), rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      AnnularTerm.difference),
      rfl⟩

/-- The actual corrected annular term count is bounded by the original all-hole request count. -/
theorem terms_count (sample :
  PairedComparison.SewnSample
  source firstSurface secondSurface) :
    sample.terms.length ≤ request.count := by
  have first := congrArg List.length sample.terms_eq
  have second := congrArg List.length source.terms_eq
  rw [Data.List.Map.length_map] at first second
  exact first.le.trans (second.le.trans comparison.entries_count)

/-- Every actual annular term is ready above the original common comparison stage. -/
theorem term_later (sample :
  PairedComparison.SewnSample
  source firstSurface secondSurface) (later : comparison.index ≤ stage)
    (term :
      AnnularTerm
      left right firstSurface secondSurface) (member : term ∈ sample.terms) :
    term.source.source.sewn.sewing.stage ≤ stage :=
  comparison.later later term.source.source (source.terms_eq ▸ Map.mem_map_of_mem
    (sample.terms_eq ▸ Map.mem_map_of_mem member))

/-- The retained selected-area sum minus its complete correction equals the cached actual difference. -/
theorem corrected_eq (sample :
  PairedComparison.SewnSample
  source firstSurface secondSurface) :
    sample.selectedArea - sample.correction = sample.difference := by
  rw [sample.selectedArea_eq, sample.correction_eq, sample.difference_eq]
  induction sample.terms with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) - 0 = 0; ring1
  | cons term tail ih =>
    change (term.data.selectedArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum _) - (term.data.correction +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum _) =
      term.data.selectedArea - term.data.correction + Data.Gaussian.Norm.Sum.Basic.gaussianSum _
    rw [← ih]
    ring1

/-- At the common paid stage, the complete retained corrected annular difference satisfies the original whole target. -/
theorem accurate (sample :
  PairedComparison.SewnSample
  source firstSurface secondSurface) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq sample.difference < target := by
  have bounded : ∀ value ∈ sample.terms.map
    AnnularTerm.difference,
    Data.Gaussian.Norm.Basic.normSq value ≤ request.perHole := by
    intro value member
    obtain ⟨term, inTerms, rfl⟩ := Map.mem_map.mp member
    exact (term.accurate (sample.term_later later term inTerms)).le
  have count : (sample.terms.map
    AnnularTerm.difference).length
    ≤ request.count := by
    rw [Data.List.Map.length_map]
    exact sample.terms_count
  have estimate := IncrementArea.sum_bound_of_length request.perHole_positive.le bounded count
  rw [request.perHole_eq] at estimate
  rw [sample.difference_eq]
  exact estimate.trans_lt ((show (request.count : Fraction.Rational)^2 * Aggregate.perTerm target request.count =
    (request.count : Fraction.Rational) * ((request.count : Fraction.Rational) * Aggregate.perTerm target request.count)
      by ring1).trans_lt
      (Aggregate.count_mul_perTerm_lt request.positive request.count))

/-- The actual total selected annular area minus all retained corrections satisfies the original whole target. -/
theorem annular_accurate (sample :
  PairedComparison.SewnSample
  source firstSurface secondSurface) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.selectedArea - sample.correction) < target := by
  rw [sample.corrected_eq]
  exact sample.accurate later

end SewnSample

end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
