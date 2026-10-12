module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
public import Purelib.Integration.Path.AreaComparison
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-!
# Actual retained source and canonical chart observations

Supplied source observations and summaries are consumed unchanged. Only chart
entries are acquired by realizeSupplied; payment and readback acquire no data.
The differential-specific bridges retain the original signed requests and the
actual reading banks establishing this geometric relation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (MagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Integration.Path.AreaComparison (Cached)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic
  (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

/-- Exact field families keep retained ownership and bank dependencies compact. They introduce no nominal owner or
replacement witness. -/
@[reducible, expose] def DomainFamily (owner : OwnedPuncturedMesh curve) :=
  DomainBanks.FaceDomainBank owner.frames owner.base.faces.regulars

/-- Exact equality of the retained mesh owner with the original requested owner. -/
@[reducible, expose] def OwnerIdentity (owner retained : OwnedPuncturedMesh curve) : Prop := retained = owner

/-- Exact equality of the retained mixing coefficient with the original requested coefficient. -/
@[reducible, expose] def CoefficientIdentity (coefficient retained : Data.Gaussian.Basic.Canonical) : Prop := retained =
  coefficient

/-- The original differential primitive bank at the supplied stage and exact mesh domain family. -/
@[reducible, expose] def ReadingBank (owner : OwnedPuncturedMesh curve) (differential : Differentials.Basic.Differential
  genus)
    (stage : Nat) (domains : DomainFamily owner) :=
  PrimitiveData.FacePrimitiveBank differential stage domains

/-- The actual triangle readings dependent on the original retained differential bank and mesh. -/
@[reducible, expose] def BankReadings (owner : OwnedPuncturedMesh curve) (differential :
  Differentials.Basic.Differential genus)
    (stage : Nat) (domains : DomainFamily owner) (bank : ReadingBank owner differential stage domains) :=
  TrianglePrimitiveReadings.TriangleReadings bank owner.mesh

/-- Bundle only the existing retained grid fields. This does not rebuild any vertices, frames, edges, faces or numerical
bank. -/
@[reducible, expose] def ownerFromMesh
    {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree}
    {base : Meshes.FramedPuncturedGrid curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
    {vertices : LiftedVertices.VertexBank base.bank.grid}
    {edges : RootEdgeBank frames}
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    OwnedPuncturedMesh curve :=
  OwnedPuncturedMesh.ofExisting branches higher base
    ({ vertices := vertices, frames := frames, edges := edges, mesh := mesh } :
      Purelib.Riemann.Meshes.LiftedPuncturedGrid base)

set_option genInjectivity false in
/-- The original single differential, bank and reading at one selected stage. No mixed coefficient or additional reading
is introduced. -/
structure SingleReadings (domains : DomainFamily owner) (differential : Differentials.Basic.Differential genus) where
  /-- The retained original owned punctured mesh. -/ meshOwner : OwnedPuncturedMesh curve
  /-- The retained mesh owner is exactly the original requested owner. -/ meshOwner_eq : OwnerIdentity owner meshOwner
  /-- The actual common numerical stage retained by this reading bundle. -/ stage : Nat
  /-- The original differential primitive bank at the retained stage. -/ bank : ReadingBank owner differential stage
    domains
  /-- The actual triangle readings from that exact original bank. -/ readings : BankReadings owner differential stage
    domains bank

constructive_injectivity SingleReadings

namespace SingleReadings

/-- The actual original single-differential triangle values from the retained reading bank. -/
@[reducible, expose] def values {domains : DomainFamily owner} {differential : Differentials.Basic.Differential genus}
    (sample : SingleReadings (owner := owner) domains differential) : Values owner := sample.readings.values

/-- Bundle the existing original single-differential bank and triangle readings without reacquiring data. -/
@[expose] def ofReadings {domains : DomainFamily owner} {differential : Differentials.Basic.Differential genus}
    {stage : Nat} {bank : ReadingBank owner differential stage domains}
    (readings : BankReadings owner differential stage domains bank) : SingleReadings (owner := owner) domains
      differential :=
  ⟨owner, rfl, stage, bank, readings⟩

/-- Certify the actual retained single reading at its original magnitude floor. -/
@[expose] def magnitude {domains : DomainFamily owner} {differential : Differential genus}
    (sample : SingleReadings (owner := owner) domains differential)
    (fixed : MagnitudeBank owner domains differential) (later : fixed.index ≤ sample.stage) :
    EdgeMagnitude (owner := owner) sample.values :=
  EdgeMagnitude.ofBank fixed later sample.readings

end SingleReadings

set_option genInjectivity false in
/-- Both original differential banks and their readings at one retained stage.

The original mesh owner and dependent banks are retained unchanged. No mixing coefficient or mixed numerical reading is
introduced; direct and conjugate comparisons can consume the same two parents. -/
structure PairedReadings (domains : DomainFamily owner)
    (leftDifferential rightDifferential : Differential genus) where
  /-- The original retained punctured mesh owner. -/ meshOwner : OwnedPuncturedMesh curve
  /-- The retained owner is exactly the requested mathematical owner. -/ meshOwner_eq : OwnerIdentity owner meshOwner
  /-- The common numerical stage of both original banks. -/ stage : Nat
  /-- The original first differential bank at the retained stage. -/
  leftBank : ReadingBank owner leftDifferential stage domains
  /-- The original second differential bank at the same stage. -/
  rightBank : ReadingBank owner rightDifferential stage domains
  /-- The original readings dependent on the first bank. -/
  leftReadings : BankReadings owner leftDifferential stage domains leftBank
  /-- The original readings dependent on the second bank. -/
  rightReadings : BankReadings owner rightDifferential stage domains rightBank

namespace PairedReadings

/-- Retain the supplied banks, readings and original owner without acquiring any additional data. -/
@[expose] def ofReadings {domains : DomainFamily owner}
    {leftDifferential rightDifferential : Differential genus} {stage : Nat}
    {leftBank : ReadingBank owner leftDifferential stage domains}
    {rightBank : ReadingBank owner rightDifferential stage domains}
    (left : BankReadings owner leftDifferential stage domains leftBank)
    (right : BankReadings owner rightDifferential stage domains rightBank) :
    PairedReadings (owner := owner) domains leftDifferential rightDifferential :=
  ⟨owner, rfl, stage, leftBank, rightBank, left, right⟩

/-- The original first reading's magnitude certificate at its own validity floor. -/
@[expose] def leftMagnitude {domains : DomainFamily owner}
    {leftDifferential rightDifferential : Differential genus}
    (sample : PairedReadings (owner := owner) domains leftDifferential rightDifferential)
    (fixed : MagnitudeBank owner domains leftDifferential) (later : fixed.index ≤ sample.stage) :
    EdgeMagnitude (owner := owner) sample.leftReadings.values :=
  EdgeMagnitude.ofBank fixed later sample.leftReadings

/-- The original second reading's magnitude certificate at its own validity floor. -/
@[expose] def rightMagnitude {domains : DomainFamily owner}
    {leftDifferential rightDifferential : Differential genus}
    (sample : PairedReadings (owner := owner) domains leftDifferential rightDifferential)
    (fixed : MagnitudeBank owner domains rightDifferential) (later : fixed.index ≤ sample.stage) :
    EdgeMagnitude (owner := owner) sample.rightReadings.values :=
  EdgeMagnitude.ofBank fixed later sample.rightReadings

end PairedReadings

set_option genInjectivity false in
/-- Retain both actual numerical banks/readings at the supplied common stage. -/
structure MixedReadings (domains : DomainFamily owner)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) (coefficient :
      Data.Gaussian.Basic.Canonical) where
  /-- The retained original owned punctured mesh. -/ meshOwner : OwnedPuncturedMesh curve
  /-- The retained mesh owner is exactly the original requested owner. -/ meshOwner_eq : OwnerIdentity owner meshOwner
  /-- The retained original Gaussian mixing coefficient. -/ mixCoefficient : Data.Gaussian.Basic.Canonical
  /-- The retained mixing coefficient is exactly the supplied original coefficient. -/ mixCoefficient_eq :
    CoefficientIdentity coefficient mixCoefficient
  /-- The actual common numerical stage retained by this reading bundle. -/ stage : Nat
  /-- The original first differential primitive bank at the shared retained stage. -/ leftBank : ReadingBank owner
    leftDifferential stage domains
  /-- The original second differential primitive bank at that same retained stage. -/ rightBank : ReadingBank owner
    rightDifferential stage domains
  /-- The actual triangle readings dependent on the retained first bank. -/ leftReadings : BankReadings owner
    leftDifferential stage domains leftBank
  /-- The actual triangle readings dependent on the retained second bank. -/ rightReadings : BankReadings owner
    rightDifferential stage domains rightBank

constructive_injectivity MixedReadings

namespace MixedReadings

/-- Bundle both existing original banks and their actual readings at the shared stage with the exact supplied
coefficient. -/
@[expose] def ofReadings {domains : DomainBanks.FaceDomainBank owner.frames owner.base.faces.regulars}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus} (coefficient :
      Data.Gaussian.Basic.Canonical)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank owner.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank owner.mesh) :
    MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient :=
  ⟨owner, rfl, coefficient, rfl, stage, leftBank, rightBank, left, right⟩

/-- Mix the two actual original triangle readings by conjugating the first and scaling the second with the retained
coefficient. -/
@[expose] def values {domains : DomainBanks.FaceDomainBank owner.frames owner.base.faces.regulars}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus} {coefficient :
      Data.Gaussian.Basic.Canonical}
    (sample : MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient) : Values owner :=
  EdgeMagnitude.mixValues (owner := owner) sample.leftReadings.values sample.rightReadings.values coefficient

/-- Each actual mixed reading is the conjugate original first reading plus the retained coefficient times the second. -/
theorem values_readback {domains : DomainBanks.FaceDomainBank owner.frames owner.base.faces.regulars}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus} {coefficient :
      Data.Gaussian.Basic.Canonical}
    (sample : MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient)
    (triangle : Fin owner.mesh.triangles.length) (which : Fin 3) :
    sample.values triangle which = conj (sample.leftReadings.values triangle which) +
      sample.mixCoefficient * sample.rightReadings.values triangle which := by
  rw [sample.mixCoefficient_eq]
  exact EdgeMagnitude.mixValues_apply (owner := owner)
    sample.leftReadings.values sample.rightReadings.values coefficient triangle which

/-- Certify the retained mixed reading using the two original magnitude banks and their distinct floors. -/
@[expose] def magnitude {domains : DomainFamily owner}
    {leftDifferential rightDifferential : Differential genus} {coefficient : Gaussian}
    (sample : MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient)
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential)
    (leftLater : leftFixed.index ≤ sample.stage) (rightLater : rightFixed.index ≤ sample.stage) :
    EdgeMagnitude (owner := owner) sample.values :=
  EdgeMagnitude.mix (EdgeMagnitude.ofBank leftFixed leftLater sample.leftReadings)
    (EdgeMagnitude.ofBank rightFixed rightLater sample.rightReadings) coefficient

end MixedReadings

/-- The original source increment list in the exact retained signed occurrence order. -/
@[reducible, expose] def IncrementList (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)) :=
  sources.map (fun source => source.increment values)

set_option genInjectivity false in
/-- A reusable actual source polygon, with executable one-pass summary data. -/
structure SourceObservations (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)) where
  /-- The cached actual source increment list. -/ increments : List Data.Gaussian.Basic.Canonical
  /-- The cached increments equal the original source readings in their retained occurrence order. -/ increments_eq :
    increments = IncrementList values sources
  /-- The executable cached summary of that exact original source increment list. -/ summary : IncrementArea.Summary
    increments

constructive_injectivity SourceObservations

namespace SourceObservations

/-- Read the original source increments once and cache their complete executable summary. -/
@[expose] def realize (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)) :
    SourceObservations values sources :=
  let increments := IncrementList values sources
  ⟨increments, rfl, IncrementArea.Summary.build increments⟩

/-- The cached original source area equals the full path area of the retained source readings. -/
theorem area_readback {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    (observations : SourceObservations values sources) :
    observations.summary.area = IncrementArea.pathArea (IncrementList values sources) :=
  observations.summary.area_eq.trans (congrArg IncrementArea.pathArea observations.increments_eq)

end SourceObservations

/-- Transport cached scalar data across an exact index equality. No list scan or numerical summary computation is
repeated. -/
@[expose] def reindexSummary {first second : List Data.Gaussian.Basic.Canonical} (equal : first = second)
    (summary : IncrementArea.Summary first) : IncrementArea.Summary second where
  total := summary.total
  total_eq := summary.total_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum equal)
  area := summary.area
  area_eq := summary.area_eq.trans (congrArg IncrementArea.pathArea equal)

/-- Zipping two mapped readings of one original list equals mapping their paired readings in that same order. -/
private theorem zip_maps {α : Type} (first second : α → Data.Gaussian.Basic.Canonical) (entries : List α) :
    List.zip (entries.map first) (entries.map second) = entries.map (fun entry => (first entry, second entry)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (first head, second head)) ih

/-- The canonical chart increment list on the exact original projected source occurrences. -/
@[reducible, expose] def ChartIncrements (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)) :=
  sources.map (fun source => CanonicalEdgeValues.edgeValuation owner.mesh values (source.project
    owner.mesh.triangulation.faces))

/-- The original paired source and canonical chart readings in retained occurrence order. -/
@[reducible, expose] def PairSpecification (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)) :=
  sources.map (fun source => (source.increment values,
    CanonicalEdgeValues.edgeValuation owner.mesh values (source.project owner.mesh.triangulation.faces)))

/-- The cached numerical area comparison on the exact supplied source and chart summaries.

The retained readback equalities transport the original caches to the pair projections without recomputing either
summary. -/
@[reducible, expose] def NumericCertificate {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    (source : SourceObservations values sources) (pairs : List (Data.Gaussian.Basic.Canonical ×
      Data.Gaussian.Basic.Canonical))
    (firstReadback : pairs.map Prod.fst = source.increments)
    (chart : List Data.Gaussian.Basic.Canonical) (secondReadback : pairs.map Prod.snd = chart)
    (chartSummary : IncrementArea.Summary chart) (error magnitude : Fraction.Rational) :=
  Cached pairs error magnitude
    (reindexSummary firstReadback.symm source.summary)
    (reindexSummary secondReadback.symm chartSummary)

set_option genInjectivity false in
/-- Cached observations beneath a single or mixed source/chart request. The typed request bridge retains the actual
signed location/chart witnesses. -/
structure Comparison (values : Values owner) (sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length))
    (suppliedSource : SourceObservations values sources) (error magnitude : Fraction.Rational) where
  /-- The retained actual original source observation cache. -/ source : SourceObservations values sources
  /-- The retained source observation cache is exactly the supplied original cache. -/ source_eq : source =
    suppliedSource
  /-- The acquired canonical chart increment list. -/ chart : List Data.Gaussian.Basic.Canonical
  /-- The acquired chart entries are exactly the original canonical projected-edge readings. -/ chart_eq : chart =
    ChartIncrements values sources
  /-- The retained paired original-source and acquired-chart readings. -/ pairs : List (Data.Gaussian.Basic.Canonical ×
    Data.Gaussian.Basic.Canonical)
  /-- The retained pairs equal the canonical source/chart specification in original occurrence order. -/ pairs_eq :
    pairs = PairSpecification values sources
  /-- The first projection of the actual retained pairs is exactly the original source increment cache. -/
    first_readback : pairs.map Prod.fst = source.increments
  /-- The second projection of the actual retained pairs is exactly the acquired chart increment list. -/
    second_readback : pairs.map Prod.snd = chart
  /-- The retained pair count equals the complete original source occurrence count. -/ count_readback : pairs.length =
    sources.length
  /-- The cached executable summary of the actual acquired chart increment list. -/ chartSummary : IncrementArea.Summary
    chart
  /-- The retained numerical certificate on those exact original source and acquired chart summaries. -/ numeric :
    NumericCertificate source pairs first_readback chart second_readback chartSummary error magnitude

constructive_injectivity Comparison

namespace Comparison

/-- The cached actual source-area minus chart-area residual. -/
@[expose] def residual {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) : Gaussian := comparison.numeric.residual

/-- The cached squared-norm bound for the actual source/chart area residual. -/
@[expose] def areaBound {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) : Fraction.Rational := comparison.numeric.areaBound

/-- The retained residual reads the exact supplied source summary area minus the acquired chart summary area. -/
theorem residual_cached {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) :
    comparison.residual = source.summary.area - comparison.chartSummary.area := by
  have cached := comparison.numeric.residual_eq
  change comparison.residual = comparison.source.summary.area - comparison.chartSummary.area at cached
  rw [comparison.source_eq] at cached
  exact cached

/-- The cached residual is the original source polygon area minus the canonical projected-edge word area. -/
theorem residual_readback {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) :
    comparison.residual = IncrementArea.pathArea (IncrementList values sources) -
      Purelib.Topology.Mesh.RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh values)
        (sources.map (fun source => source.project owner.mesh.triangulation.faces)) := by
  rw [comparison.residual_cached, source.area_readback, comparison.chartSummary.area_eq, comparison.chart_eq]
  unfold ChartIncrements RetracingWords.wordArea
  rw [Map.map_map]
  rfl

/-- The cached area bound is the exact original occurrence-count expression with retained error and magnitude. -/
theorem bound_readback {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) :
    comparison.areaBound = 16 * (sources.length : Fraction.Rational)^4 * error * magnitude := by
  rw [areaBound, comparison.numeric.areaBound_eq, comparison.count_readback]

/-- A paid retained area bound controls the squared norm of the actual cached source/chart residual. -/
theorem pay {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge owner.mesh.triangles.length)}
    {source : SourceObservations values sources} {error magnitude target : Fraction.Rational}
    (comparison : Comparison values sources source error magnitude) (paid : comparison.areaBound ≤ target) :
    normSq comparison.residual ≤ target := comparison.numeric.pay paid

end Comparison

/-- A Gaussian reading within the retained small error of a bounded original reading has squared norm at most the
corresponding enlarged bound. -/
private theorem changed_magnitude (original changed : Data.Gaussian.Basic.Canonical) {bound error : Fraction.Rational}
    (originalBound : normSq original ≤ 4 * bound) (accurate : normSq (original - changed) ≤ error)
    (small : error ≤ 1) : normSq changed ≤ 8 * bound + 2 := by
  have initial : normSq (original - (original - changed)) ≤
      2 * (normSq original + normSq (original - changed)) := by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two original (original - changed)
  have estimate := initial.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      originalBound (accurate.trans small)) (by decide))
  rw [show original - (original - changed) = changed by ring1] at estimate
  exact estimate.trans_eq (by ring1)

/-- Reuse the supplied source list and summary. The executable body evaluates only chart entries, list pairing and the
chart summary; source increments occur only in erased canonical certificates. -/
@[expose] def realizeSupplied {values : Values owner} {sources : List (SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length)}
    (source : SourceObservations values sources) (magnitude : EdgeMagnitude values)
    (error : Fraction.Rational) (nonnegative : 0 ≤ error) (small : error ≤ 1)
    (errors : ∀ occurrence ∈ sources,
      normSq (occurrence.increment values - CanonicalEdgeValues.edgeValuation owner.mesh values
        (occurrence.project owner.mesh.triangulation.faces)) ≤ error) :
    Comparison values sources source error (8 * magnitude.bound + 2) :=
  let chart := ChartIncrements values sources
  let pairs := List.zip source.increments chart
  have canonical : pairs = PairSpecification values sources := by
    change List.zip source.increments (ChartIncrements values sources) = PairSpecification values sources
    rw [source.increments_eq]
    exact zip_maps _ _ sources
  have first : pairs.map Prod.fst = source.increments := by
    rw [canonical, PairSpecification, Map.map_map]
    exact source.increments_eq.symm
  have second : pairs.map Prod.snd = chart := by
    rw [canonical, PairSpecification, Map.map_map]
    rfl
  have count : pairs.length = sources.length := by rw [canonical, PairSpecification, Map.length_map]
  let chartSummary := IncrementArea.Summary.build chart
  let firstSummary := reindexSummary first.symm source.summary
  let secondSummary := reindexSummary second.symm chartSummary
  have pairErrors : ∀ pair ∈ pairs, normSq (pair.1 - pair.2) ≤ error := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, inSources, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact errors occurrence inSources
  have firstBound : ∀ pair ∈ pairs, normSq pair.1 ≤ 8 * magnitude.bound + 2 := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    have sourceBound : normSq (occurrence.increment values) ≤ 4 * magnitude.bound := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        magnitude.source_bounded occurrence
    refine sourceBound.trans ?_
    rw [show 8 * magnitude.bound + 2 = 4 * magnitude.bound + (4 * magnitude.bound + 2) by ring1]
    exact le_add_of_nonneg_right (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      magnitude.nonnegative) (by decide))
  have secondBound : ∀ pair ∈ pairs, normSq pair.2 ≤ 8 * magnitude.bound + 2 := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, inSources, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    have sourceBound : normSq (occurrence.increment values) ≤ 4 * magnitude.bound := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        magnitude.source_bounded occurrence
    exact changed_magnitude _ _ sourceBound (errors occurrence inSources) small
  let numeric := Cached.realize pairs error (8 * magnitude.bound + 2) firstSummary secondSummary nonnegative
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitude.nonnegative) (by decide)) pairErrors
      firstBound secondBound
  ⟨source, rfl, chart, rfl, pairs, canonical, first, second, count, chartSummary, numeric⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
