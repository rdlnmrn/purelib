module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.NewtonConjugatePeriodReadback
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonHomogeneousConjugateReadback
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Energy

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Topology.Surface.Sewing

public section

/-! One retained bank of conjugate physical comparisons controls every
coefficient vector on a common tail. All signed physical and cut terms remain. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs energyBoundary
  energyBoundary_pairs)
open Purelib.Riemann.Periods.NewtonCombinedPeriodArea (combinedEdgeValue resplitPeriodMatrix combined_energy_resplit)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea)
open Purelib.Riemann.RootContinuation.NewtonHomogeneousConjugateReadback (combined_conjugate_period_area)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Integration.Energy.Polygon (energyBoundaryArea)
open Purelib.LinearAlgebra.Gaussian.Energy (periodCombination)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_add)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    (prepared : Prepared paired)
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars}

/-- The complete matrix of original conjugate physical requests for the retained basis differential pairs. -/
@[expose] def Requests (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (magnitudes : Data.Vector.DependentVector (fun basis : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (floor : Nat) :=
  Data.Vector.DependentVector fun first : Fin genus => Data.Vector.DependentVector fun second : Fin genus =>
    ConjugatePhysicalRequest.PairRequest prepared newSheet excision (magnitudes.get first) (magnitudes.get second) error
      floor

/-- Every actual entry request is paid by the supplied common stage. -/
@[expose] def Requests.IndexBound {newSheet : Fin 2} {excision : Excision.AllHoleExcision grid current}
    {magnitudes : Data.Vector.DependentVector (fun basis : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential basis))}
    {error : Fraction.Rational} {floor : Nat}
    (entries : Requests prepared newSheet excision
      magnitudes error floor) (index : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ index

set_option genInjectivity false in
/-- The retained matrix of physical requests and its common paid stage.

Every entry keeps the original prepared magnitude and excision owners; the cached index pays both the requested floor
and all entry thresholds. -/
structure Request (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (magnitudes : Data.Vector.DependentVector (fun basis : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (floor : Nat) where
  /-- The actual pair requests in the original basis order. -/ entries :
    Requests prepared newSheet excision magnitudes
    error floor
  /-- The cached stage paying every retained pair request. -/ index : Nat
  /-- The requested floor is at most the retained common stage. -/ floor_le : floor ≤ index
  /-- Every actual entry threshold is at most the retained common stage. -/ index_ge :
    Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Requests.IndexBound prepared entries index

constructive_injectivity Request

namespace Request

/-- Prepare the complete original pair-request matrix and cache its maximum paid stage. -/
@[expose] def build (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (magnitudes : Data.Vector.DependentVector (fun basis : Fin genus => MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes error
      floor := by
  let entries : Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Requests prepared newSheet excision
    magnitudes error floor :=
    DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
      ConjugatePhysicalRequest.PairRequest.build prepared newSheet excision (magnitudes.get first) (magnitudes.get
          second) error positive floor
  let maximum := entries.maximum (fun _ row => row.maximum fun _ request => request.index)
  refine ⟨entries, max floor maximum, Nat.Order.le_max_left _ _, ?_⟩
  intro first second
  exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first).trans
      (Nat.Order.le_max_right _ _))

variable {prepared} {newSheet : Fin 2} {excision :
  AllHoleExcision grid current}
  {magnitudes : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis))}
  {error : Rational} {floor stage : Nat}
  {cache : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis) stage domains)}
  (triangles : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    TriangleReadings (cache.get basis)
    current.mesh))
  (surfaces : EnergySurfaces current.cutPolygon.patch (fun basis
    => (triangles.get basis).values))
  (pairs : EnergyPairs surfaces)

/-- The actual samples of all retained pair requests on the original triangle and sewn-surface banks. -/
@[expose] def Samples (request : Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared
  newSheet excision magnitudes error floor) :=
  Data.Vector.DependentVector fun first : Fin genus => Data.Vector.DependentVector fun second : Fin genus =>
    ConjugatePhysicalRequest.PairRequest.Sample (triangles.get first) (triangles.get second) (surfaces.get first)
        (surfaces.get second)
      ((pairs.get first).get second) ((request.entries.get first).get second)

/-- Acquire each original pair request on the supplied shared triangle and sewn-surface samples. -/
@[expose] def Samples.build (request : Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared
  newSheet excision magnitudes error floor) :
    Samples triangles surfaces pairs request :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    ConjugatePhysicalRequest.PairRequest.Sample.build (triangles.get first) (triangles.get second) (surfaces.get first)
        (surfaces.get second)
      ((pairs.get first).get second) ((request.entries.get first).get second)

variable {triangles surfaces pairs} {request :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
  error floor}

/-- The contraction consumes cached signed corrections, including the inner hole boundaries, sewing jumps, defects and
word offsets. -/
@[expose] def Samples.correction (samples :
  Samples triangles surfaces pairs request)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients
    first) * coefficients second *
    ((samples.get first).get second).correction

/-- The retained physical exterior is part of this contraction. -/
@[expose] def Samples.area (samples : Samples
  triangles surfaces pairs request) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients
    first) * coefficients second *
    ((samples.get first).get second).area

/-- This sum reads the cached exterior contributions from the same samples. -/
@[expose] def Samples.exterior (samples :
  Samples triangles surfaces pairs request)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients
    first) * coefficients second *
    ((samples.get first).get second).exterior

/-- Split off the actual homogeneous period area. The other summand is the cached physical exterior on the very same
compiler and basis readings. -/
theorem Samples.area_split (samples : Samples
  triangles surfaces pairs request) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    samples.area coefficients =
      OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges current.vertices newSheet
        (NewtonCombinedPeriodArea.combinedEdgeValue current.vertices coefficients
          (fun basis => CanonicalEdgeValues.edgeValuation current.mesh (triangles.get basis).values)) +
      samples.exterior coefficients := by
  erw [NewtonHomogeneousConjugateReadback.combined_conjugate_period_area prepared]
  have read := FiniteSum.Fin.sumFin_congr fun first : Fin genus => FiniteSum.Fin.sumFin_congr fun second : Fin genus =>
    show
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
        second).area =
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        NewtonConjugatePeriodReadback.conjugateResplitPeriodArea prepared grid.shrunk.included current.edges
          current.vertices newSheet
          (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
          (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values) +
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
        second).exterior by
    rw [((samples.get first).get second).area_eq, ConjugatePhysicalRequest.physical_split,
      ← ((samples.get first).get second).exterior_eq]
    ring1
  exact read.trans (by simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add]; rfl)

/-- The index is independent of the coefficient vector. The bound pays the complete pair count and is homogeneous in the
squared coefficient norm. -/
theorem Samples.accurate (samples : Samples
  triangles surfaces pairs request)
    (later : request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (SewnEnergyCombination.energyBoundary surfaces coefficients -
      samples.correction coefficients -
      (samples.area coefficients + samples.area coefficients)) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients basis)))^2 * error := by
  let residual := fun first second => ((pairs.get first).get second).boundaryArea -
    ((samples.get first).get second).correction -
    (((samples.get first).get second).area + ((samples.get first).get second).area)
  have bounded (first second : Fin genus) : Data.Gaussian.Norm.Basic.normSq (residual first second) ≤ error :=
    (((samples.get first).get second).accurate ((request.index_ge first second).trans later)).le
  have estimate := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients
    basis)) coefficients residual bounded
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have read : SewnEnergyCombination.energyBoundary surfaces coefficients - samples.correction coefficients -
      (samples.area coefficients + samples.area coefficients) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
        (coefficients first) * coefficients second * residual first second)) := by
    rw [SewnEnergyCombination.energyBoundary_pairs surfaces pairs coefficients]
    have expanded := FiniteSum.Fin.sumFin_congr fun first : Fin genus => FiniteSum.Fin.sumFin_congr fun second : Fin
      genus => show
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * residual first second =
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((pairs.get first).get
          second).boundaryArea -
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
          second).correction -
        (Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
          second).area +
          Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
            second).area) by
      unfold residual
      ring1
    rw [expanded]
    simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add]
    rfl
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le (estimate.trans_eq (by ring1))

/-- The comparison now names the actual corrected period matrices. Only cached cut and physical-exterior terms remain
outside their energy boundary. -/
theorem Samples.period_accurate (samples :
  Samples triangles surfaces pairs request)
    (later : request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    let values := fun basis => CanonicalEdgeValues.edgeValuation current.mesh (triangles.get basis).values
    let aMatrix := NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values false
    let bMatrix := NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values true
    Data.Gaussian.Norm.Basic.normSq (SewnEnergyCombination.energyBoundary surfaces coefficients -
      samples.correction coefficients -
      (Polygon.energyBoundaryArea (Energy.periodCombination coefficients aMatrix)
        (Energy.periodCombination coefficients bMatrix) + 2 * samples.exterior coefficients)) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients basis)))^2 * error := by
  intro values aMatrix bMatrix
  have estimate := samples.accurate later coefficients
  rw [samples.area_split] at estimate
  have energy := NewtonCombinedPeriodArea.combined_energy_resplit prepared grid.shrunk.included current.edges
    current.vertices newSheet coefficients values
  change Polygon.energyBoundaryArea (Energy.periodCombination coefficients aMatrix)
    (Energy.periodCombination coefficients bMatrix) = _ at energy
  rw [energy]
  have scalar (boundary correction period exterior : Data.Gaussian.Basic.Canonical) :
      boundary - correction - (2 * period + 2 * exterior) =
        boundary - correction - ((period + exterior) + (period + exterior)) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (scalar _ _ _ _)).trans_le estimate

end Request
end Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
