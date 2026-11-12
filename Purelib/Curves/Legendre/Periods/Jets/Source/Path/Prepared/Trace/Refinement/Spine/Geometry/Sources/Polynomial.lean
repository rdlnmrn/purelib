module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Requests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement

/-! # Actual numerator gap words against the same six-channel source preparations

Both ordinary value numerators use their genuine full polynomial model and
numerical bank. Whole original cover equality transports the retained
source preparation, and the existing query-root comparison pays its own
independent model/source stages. The numerical word keeps its actual gaps.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (add_le_add_direct mul_le_mul_of_nonneg_left_direct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
variable {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {point : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient point point}
variable {owner : Owner ((Paths.polynomial parameter).eval point)} {prepared : PreparedPath clearPath owner}
variable {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) point owner point
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)

namespace Geometry.Sources

variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}
variable (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
variable {target : Rational} (requests : RequestedParents count target retained.parents)
variable (sameCovered : requests.covered = retained.covered)
variable (childChain : CenteredPathChain retained.parents
  (start := (⟨point, sheet⟩ : LiftedPoint 2)) (finish := (⟨point, sheet⟩ : LiftedPoint 2)))
variable (coordinate : Fin 2) {polynomialFloor polynomialStage : Nat}
variable (work : PolynomialWork requests.covered polynomialFloor
  (Specification.valueSpecification parameter coordinate))
variable (models : work.Models polynomialStage)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {rootFrames : RootFrames base.bank.grid} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank rootFrames base.faces.regulars} {numericIndex : Nat}
variable {meshPoints : List Canonical} {meshTolerance : Rational}
variable {numerics : FacePrimitiveBank basis numericIndex
  (numerator := (Specification.valueSpecification parameter coordinate).numerator.scale
    (Specification.valueSpecification parameter coordinate).scale) domains}
variable {budgets : FaceMeshBudgets basis meshPoints meshTolerance
  (numerator := (Specification.valueSpecification parameter coordinate).numerator.scale
    (Specification.valueSpecification parameter coordinate).scale) domains}
variable (shared : FaceSharedMeshes (numerator :=
  (Specification.valueSpecification parameter coordinate).numerator.scale
    (Specification.valueSpecification parameter coordinate).scale) budgets numerics)
variable {splits : PrimitiveSplits axes retained.parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (entries : SplitSheets domains fragments requests) {root : Named}
variable (roots : RootChain retained.parents root root)
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ meshPoints}
variable (closed : SplitSheets.Closed shared entries childChain roots included)

/-- The original same-bank preparation views and one actual full-numerator closed-word comparison.

The whole cover identity carries the complete retained patch spine. Both
actual source preparations remain data, and the ordinary full-numerator
model/word result retains its one original factory. There is no second
source preparation or value-zero comparison for a coordinate-one bank.
-/
abbrev PolynomialAttachment :=
  {value : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory ×
      Sources (count := count) (floor := floor) (targets := targets) retained × (Fin 2 × Nat × Nat × Nat × Nat) //
    value = (retained, sourceBank, (coordinate, polynomialFloor, polynomialStage, floor, stage))} ×
  (Σ original : {value : PreparedParents retained.covered floor targets //
      value = preparations (count := count) (floor := floor) (targets := targets) retained sourceBank},
  Σ _viewed : {value : PreparedParents requests.covered floor targets //
      value = original.val.castCovered sameCovered.symm},
  Σ compared : {value : SplitSheets.PolynomialComparison.Cache
      shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) //
    value = SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate)},
  {value : Rational // value = 2 * (compared.val.bound +
    16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents)})

namespace PolynomialAttachment

/-- Assemble the original source views around the GIVEN whole polynomial comparison and its actual build factory.

The input comparison is retained unchanged. Only the original source-bank
preparation projection, its whole-cover view and the displayed scalar bound
are assembled; no polynomial model, numerical bank or comparison executes.
-/
def ofComparison (compared : {value : SplitSheets.PolynomialComparison.Cache
      shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) //
      value = SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
        (Specification.valueSpecification_denominatorPairs parameter coordinate)}) :
    PolynomialAttachment retained sourceBank requests sameCovered
      childChain coordinate work models shared entries roots closed :=
  let original : {value : PreparedParents retained.covered floor targets //
      value = preparations (count := count) (floor := floor) (targets := targets) retained sourceBank} :=
    ⟨preparations (count := count) (floor := floor) (targets := targets) retained sourceBank, rfl⟩
  let viewed : {value : PreparedParents requests.covered floor targets //
      value = original.val.castCovered sameCovered.symm} :=
    ⟨original.val.castCovered sameCovered.symm, rfl⟩
  let bound : {value : Rational // value = 2 * (compared.val.bound +
      16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents)} :=
    ⟨2 * (compared.val.bound +
      16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents), rfl⟩
  ⟨⟨(retained, sourceBank, (coordinate, polynomialFloor, polynomialStage, floor, stage)), rfl⟩,
    original, viewed, compared, bound⟩

end PolynomialAttachment

/-- Project the SAME source preparation and compare the genuine numerical numerator word once. -/
def comparePolynomialWord : PolynomialAttachment retained sourceBank requests sameCovered
    childChain coordinate work models shared entries roots closed :=
  let compared : {value : SplitSheets.PolynomialComparison.Cache
      shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) //
      value = SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
        (Specification.valueSpecification_denominatorPairs parameter coordinate)} :=
    ⟨SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate), rfl⟩
  PolynomialAttachment.ofComparison retained sourceBank requests sameCovered
    childChain coordinate work models shared entries roots closed compared

namespace PolynomialAttachment

variable {retained sourceBank requests sameCovered childChain coordinate work models shared entries roots closed}
variable (kept : PolynomialAttachment retained sourceBank requests sameCovered
  childChain coordinate work models shared entries roots closed)

/-- Read the original whole retained geometry with all cached Head/front/tail owner and stationary-role evidence. -/
@[expose] def geometry : Materialized.Geometry (count := count)
    diameter positive lineage inputCenters materialized factory := kept.1.val.1

/-- Read the actual same six-channel bank without preparing any source cell again. -/
@[expose] def bank : Sources (count := count) (floor := floor) (targets := targets) retained := kept.1.val.2.1

/-- Read the literal value coordinate and independent polynomial/source floor and stage inputs as actual data. -/
@[expose] def stages : Fin 2 × Nat × Nat × Nat × Nat := kept.1.val.2.2

/-- Read the SAME complete source preparation product before its exact whole cover-index transport. -/
@[expose] def original : PreparedParents retained.covered floor targets := kept.2.1.val

/-- Read that actual product under the original request patch spine. -/
@[expose] def viewed : PreparedParents requests.covered floor targets := kept.2.2.1.val

/-- Read the one actual full-numerator word/model comparison, with every genuine primitive constant and gap. -/
@[expose] def comparison :
    SplitSheets.PolynomialComparison.Cache shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) := kept.2.2.2.1.val

/-- The original complete geometry and six-channel source input remain their literal supplied values. -/
theorem originals_eq : kept.1.val =
    (retained, sourceBank, (coordinate, polynomialFloor, polynomialStage, floor, stage)) := kept.1.property

/-- The original preparation is the whole bank's existing projection, with no source factory execution. -/
theorem original_eq : kept.original =
    preparations (count := count) (floor := floor) (targets := targets) retained sourceBank := kept.2.1.property

/-- The request-index view uses the whole original cover equality, preserving every nominal patch owner. -/
theorem viewed_eq : kept.viewed = kept.original.castCovered sameCovered.symm := kept.2.2.1.property

/-- Both dependent views retain the same entire actual prepared source product heterogeneously. -/
theorem viewed_heq : HEq kept.viewed kept.original :=
  (heq_of_eq kept.viewed_eq).trans (PreparedParents.castCovered_heq kept.original sameCovered.symm)

/-- The actual same-word numerical comparison retains its complete one-constructor factory. -/
theorem comparison_eq : kept.comparison =
    SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) := kept.2.2.2.1.property

/-- Assembly retains exactly the GIVEN complete comparison cache, not only its numerical reading. -/
theorem ofComparison_comparison (compared : {value : SplitSheets.PolynomialComparison.Cache
      shared requests entries childChain roots closed work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) //
      value = SplitSheets.PolynomialComparison.build shared requests entries childChain roots closed work models
        (Specification.valueSpecification_denominatorPairs parameter coordinate)}) :
    (ofComparison retained sourceBank requests sameCovered
      childChain coordinate work models shared entries roots closed compared).comparison = compared.val := by
  unfold ofComparison comparison
  rfl

/-- The same whole-bank channel is read after the original whole-cover transport and actual child chain. -/
theorem model_eq : PathModel.mk ((PreparedParents.sources requests.covered kept.viewed childChain).cells
      (Specification.Table.valueIndex coordinate)) =
    model (count := count) (floor := floor) (targets := targets) retained sourceBank
      (Specification.Table.valueIndex coordinate) := by
  have viewedSources := congrArg (fun value : PreparedParents requests.covered floor targets =>
    PreparedParents.sources requests.covered value childChain) kept.viewed_eq
  have originalSources := PreparedParents.sources_castCovered kept.original sameCovered.symm childChain
  have givenSources := congrArg (fun value : PreparedParents retained.covered floor targets =>
    PreparedParents.sources retained.covered value childChain) kept.original_eq
  exact (congrArg (fun value : Path parameter childChain.path =>
    PathModel.mk (value.cells (Specification.Table.valueIndex coordinate)))
      (viewedSources.trans (originalSources.trans givenSources))).trans
    (model_eq_sources (count := count) (floor := floor) (targets := targets)
      retained sourceBank childChain (Specification.Table.valueIndex coordinate)).symm

include kept in
/-- The full ordinary model pays its own stage and the SAME independently prepared source channel's allowance. -/
theorem model_error_le : normSq
    ((PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample -
      (model (count := count) (floor := floor) (targets := targets) retained sourceBank
        (Specification.Table.valueIndex coordinate)).integralSample) ≤
    16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents :=
  Eq.mp (congrArg (fun value : PathModel => normSq
    ((PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample - value.integralSample) ≤
      16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents)
    kept.model_eq)
    (PreparedParents.polynomial_integral_difference_le requests.covered coordinate work models kept.viewed childChain)

/-- Read the SAME once computed combined allowance used by choosing, payment and the final certificate. -/
@[expose] def bound : Rational := kept.2.2.2.2.val

/-- Both independent actual allowances compose with the original squared-norm factor two. -/
theorem bound_eq : kept.bound = 2 * (kept.comparison.bound +
    16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass retained.parents) :=
  kept.2.2.2.2.property

/-- The literal same retained numerator gap word and six-channel source model obey their internally derived bound. -/
theorem accurate : normSq (kept.comparison.value -
    (model (count := count) (floor := floor) (targets := targets) retained sourceBank
      (Specification.Table.valueIndex coordinate)).integralSample) ≤ kept.bound :=
  ((Norm.Bounds.normSq_sub_le_via kept.comparison.value
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample
    (model (count := count) (floor := floor) (targets := targets) retained sourceBank
      (Specification.Table.valueIndex coordinate)).integralSample).trans
    (mul_le_mul_of_nonneg_left_direct
      (add_le_add_direct kept.comparison.accurate kept.model_error_le) (by decide +kernel))).trans_eq kept.bound_eq.symm

/-- The existing certified programme reads the SAME original channel at its independent selected precision. -/
theorem programme_error_le
    (precision : Nat → Nat)
    (requested : (index : Nat) → {value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    (precisionFloor : ∀ index, index ≤ precision index) (index : Nat)
    (current : PolynomialAttachment (count := count) (floor := floor) (targets := (requested index).val)
      retained (sourceBanks index) requests sameCovered childChain coordinate work models shared entries roots closed) :
    normSq (current.comparison.value -
      ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor
        (Specification.Table.valueIndex coordinate)).integral.model index).integralSample) ≤ current.bound :=
  Eq.mpr (congrArg (fun value : PathModel => normSq (current.comparison.value - value.integralSample) ≤ current.bound)
    (certifiedAtPrecision_model retained childChain precision requested sourceBanks precisionFloor
      (Specification.Table.valueIndex coordinate) index)) current.accurate

/-- A strict requested bound check retaining the actual source/numerical stages, word and all finite comparisons. -/
abbrev Payment (requested : Rational) :=
  {value : PolynomialAttachment retained sourceBank requests sameCovered childChain coordinate
      work models shared entries roots closed × Rational // value = (kept, requested)} ×
  ({_value : Unit // kept.bound < requested ∧ normSq (kept.comparison.value -
    (model (count := count) (floor := floor) (targets := targets) retained sourceBank
      (Specification.Table.valueIndex coordinate)).integralSample) < requested} ⊕
    {_value : Unit // ¬kept.bound < requested})

/-- Check the computed bound; an insufficient result proves neither a large actual error nor impossibility. -/
def pay (requested : Rational) : kept.Payment requested :=
  if admitted : kept.bound < requested then
    ⟨⟨(kept, requested), rfl⟩, Sum.inl ⟨(), admitted, kept.accurate.trans_lt admitted⟩⟩
  else ⟨⟨(kept, requested), rfl⟩, Sum.inr ⟨(), admitted⟩⟩

end PolynomialAttachment
end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized
