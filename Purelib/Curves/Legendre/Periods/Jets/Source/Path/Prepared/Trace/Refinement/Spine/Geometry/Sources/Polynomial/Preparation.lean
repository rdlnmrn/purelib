module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Polynomial
public import
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Programs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Requested progressive source values on the same retained outgoing-gap word

The source programme and its actual precision/bank rule are fixed before
accuracy. One geometric selection pays the two independent programme/model
indices. The given physical word is genuinely revalued once by its original
polynomial preparation, and the SAME comparison cache is attached to the
actual source bank at the independently supplied programme index.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
  (quarterRadius quarterRadius_antitone quarterRadius_eq_mul_pow)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
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
variable {diameter : Rational} {diameterPositive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter diameterPositive lineage inputCenters materialized factory)

namespace Geometry.Sources

variable {target : Rational} (requests : RequestedParents count target retained.parents)
variable (sameCovered : requests.covered = retained.covered)
variable (childChain : CenteredPathChain retained.parents
  (start := (⟨point, sheet⟩ : LiftedPoint 2)) (finish := (⟨point, sheet⟩ : LiftedPoint 2)))
variable (coordinate : Fin 2)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {rootFrames : RootFrames base.bank.grid} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank rootFrames base.faces.regulars} {numericIndex : Nat}
variable {meshPoints : List Canonical} {meshTolerance : Rational}
variable {oldNumerator : CoefficientPolynomial}
variable {numerics : FacePrimitiveBank basis numericIndex
  (numerator := oldNumerator) domains}
variable {budgets : FaceMeshBudgets basis meshPoints meshTolerance
  (numerator := oldNumerator) domains}
variable (shared : FaceSharedMeshes (numerator := oldNumerator) budgets numerics)
variable {splits : PrimitiveSplits axes retained.parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (entries : SplitSheets domains fragments requests) {root : Named}
variable (roots : RootChain retained.parents root root)
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ meshPoints}
variable (closed : SplitSheets.Closed shared entries childChain roots included)

variable (precision : Nat → Nat)
variable (programmeTargets : (index : Nat) →
  {value : CellEndpoints.Targets childChain.path (precision index) //
    value = CellEndpoints.Targets.build childChain.path (precision index)})
variable (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
  (original := childChain.path) (stage := precision index) (targets := (programmeTargets index).val) retained)
variable (precisionFloor : ∀ index, index ≤ precision index)

namespace PolynomialAttachment

/-- Compute one actual common floor for independent source-programme and polynomial-model indices.

The geometry is fixed before the positive request. The scale may be zero;
no division by movement mass or positive-length hypothesis is required.
-/
def programmeSelection (requested : Rational) (positive : 0 < requested)
    (programmeStart modelStart : Nat) :
    Search.Selection (32 * movementMass retained.parents) (max programmeStart modelStart) (requested / 4) :=
  Search.Selection.build (32 * movementMass retained.parents)
    (mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative retained.parents))
    (max programmeStart modelStart) (requested / 4)
    (Order.Field.div_pos_direct positive
      (Cast.Order.natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3)))

include precisionFloor in
/-- Both actual stages pay the same geometric source/model allowance without sharing their indices. -/
theorem source_model_payment {requested : Rational} {programmeStart modelStart : Nat}
    (selected : Search.Selection (32 * movementMass retained.parents)
      (max programmeStart modelStart) (requested / 4))
    (programmeIndex modelStage : Nat)
    (programmeAfter : selected.stage ≤ programmeIndex) (modelAfter : selected.stage ≤ modelStage) :
    16 * (quarterRadius 1 modelStage + (programmeTargets programmeIndex).val.localBound) *
      movementMass retained.parents < requested / 4 := by
  let scale : Rational := 16 * movementMass retained.parents
  have nonnegative : 0 ≤ scale :=
    mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative retained.parents)
  have sourceBound := (programmeTargets programmeIndex).val.mul_localBound_le_quarterRadius scale nonnegative
  have sourceOrder := quarterRadius_antitone nonnegative
    (programmeAfter.trans (precisionFloor programmeIndex))
  have sourcePaid : scale * (programmeTargets programmeIndex).val.localBound ≤
      quarterRadius scale selected.stage := sourceBound.trans sourceOrder
  have modelPaid : scale * quarterRadius 1 modelStage ≤ quarterRadius scale selected.stage := by
    have ownStage : scale * quarterRadius 1 modelStage = quarterRadius scale modelStage := by
      rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      ring1
    exact Eq.mpr (congrArg (fun value : Rational => value ≤ quarterRadius scale selected.stage) ownStage)
      (quarterRadius_antitone nonnegative modelAfter)
  calc
    _ = scale * quarterRadius 1 modelStage + scale * (programmeTargets programmeIndex).val.localBound := by
      dsimp only [scale]
      ring1
    _ ≤ quarterRadius scale selected.stage + quarterRadius scale selected.stage :=
      add_le_add_direct modelPaid sourcePaid
    _ = quarterRadius (32 * movementMass retained.parents) selected.stage := by
      rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      dsimp only [scale]
      ring1
    _ < requested / 4 := selected.later_accurate (Nat.le_refl selected.stage)

/-- The retained numerical comparison and two independently paid model allowances give the full requested error.

The given word preparation may carry an independent face-stage minimum.
Its same complete comparison cache and attachment identity pay the bound;
the programme and model floors remain separate, and no bank is rebuilt.
-/
theorem attachment_payment (requested : Rational) (positive : 0 < requested)
    (programmeStart modelStart minimumWorkFloor programmeIndex modelStage : Nat)
    (selected : Search.Selection (32 * movementMass retained.parents)
      (max programmeStart modelStart) (requested / 4))
    (programmeAfter : selected.stage ≤ programmeIndex) (modelAfter : selected.stage ≤ modelStage)
    {minimumFaceStage : Option Nat}
    (prepared : Closed.PolynomialPreparation.Preparation closed
      (Specification.valueSpecification parameter coordinate)
      (Specification.valueSpecification_denominatorPairs parameter coordinate)
      (requested / 4) (Order.Field.div_pos_direct positive
        (Cast.Order.natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3)))
      minimumWorkFloor modelStage minimumFaceStage)
    (compared : PolynomialAttachment (count := count) (floor := floor)
      (targets := (programmeTargets programmeIndex).val)
      retained (sourceBanks programmeIndex) requests sameCovered childChain coordinate
      prepared.work prepared.models prepared.sharedMeshes entries roots prepared.word)
    (sameComparison : compared.comparison = prepared.comparison) :
    compared.bound < requested ∧ normSq (prepared.value -
      ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
        (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested := by
  have wordPaid : compared.comparison.bound < requested / 4 :=
    (congrArg (fun actual : SplitSheets.PolynomialComparison.Cache prepared.sharedMeshes requests entries
      childChain roots prepared.word prepared.work prepared.models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) => actual.bound)
      sameComparison).trans_lt prepared.bound_lt
  have sourcePaid := source_model_payment retained childChain precision programmeTargets precisionFloor
    selected programmeIndex modelStage programmeAfter modelAfter
  have combined : 2 * (compared.comparison.bound +
      16 * (quarterRadius 1 modelStage + (programmeTargets programmeIndex).val.localBound) *
        movementMass retained.parents) < requested :=
    (mul_lt_mul_of_pos_left_direct (by decide +kernel : (0 : Rational) < 2)
      (add_lt_add_direct wordPaid sourcePaid)).trans_eq
        ((by ring1 : 2 * (requested / 4 + requested / 4) = (requested / 4) * 4).trans
          (Data.Rat.Fraction.Field.div_mul_cancel_of_ne requested 4 (by decide +kernel)))
  have paid : compared.bound < requested := compared.bound_eq.trans_lt combined
  have programmePaid := (PolynomialAttachment.programme_error_le (count := count) (floor := floor)
    (retained := retained) (requests := requests) (sameCovered := sameCovered) (childChain := childChain)
    (coordinate := coordinate) (work := prepared.work) (models := prepared.models)
    (shared := prepared.sharedMeshes) (entries := entries) (roots := roots) (closed := prepared.word)
    precision programmeTargets sourceBanks precisionFloor programmeIndex compared).trans_lt paid
  have sameValue : compared.comparison.value = prepared.value :=
    congrArg (fun actual : SplitSheets.PolynomialComparison.Cache prepared.sharedMeshes requests entries
      childChain roots prepared.word prepared.work prepared.models
      (Specification.valueSpecification_denominatorPairs parameter coordinate) => actual.value) sameComparison
  have accurate : normSq (prepared.value -
      ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
        (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested :=
    Eq.mp (congrArg (fun value : Canonical => normSq (value -
      ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
        (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested)
      sameValue) programmePaid
  exact ⟨paid, accurate⟩

/-- The given selection, one actual requested word/model preparation and its SAME complete source attachment.

Both numerical products remain actual original owners with whole factories.
The source programme and selected precision rule stay fixed, while its
sample index, polynomial-model stage, source work floor and face stage
remain separate. The payload certifies the literal outgoing-gap value.
-/
@[expose] def ProgrammeComparison (requested : Rational) (positive : 0 < requested)
    (programmeStart modelStart minimumWorkFloor programmeIndex modelStage : Nat)
    (selected : Search.Selection (32 * movementMass retained.parents)
      (max programmeStart modelStart) (requested / 4)) : Type _ :=
  {value : Search.Selection (32 * movementMass retained.parents)
      (max programmeStart modelStart) (requested / 4) //
    value = selected ∧ value.stage ≤ programmeIndex ∧ value.stage ≤ modelStage} ×
  (Σ prepared : Closed.PolynomialPreparation.Preparation closed
      (Specification.valueSpecification parameter coordinate)
      (Specification.valueSpecification_denominatorPairs parameter coordinate)
      (requested / 4) (Order.Field.div_pos_direct positive
        (Cast.Order.natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3)))
      minimumWorkFloor modelStage,
  {attached : PolynomialAttachment (count := count) (floor := floor)
      (targets := (programmeTargets programmeIndex).val)
      retained (sourceBanks programmeIndex) requests sameCovered childChain coordinate
      prepared.work prepared.models prepared.sharedMeshes entries roots prepared.word //
    attached.comparison = prepared.comparison ∧ attached.bound < requested ∧
      normSq (prepared.value -
        ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
          (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested})

/-- Revalue the given physical word once and attach its SAME comparison to the actual paid programme sample.

The supplied selection precedes all new observations. Each independent
index pays that same floor. This operation invokes the fixed bank rule at
its actual programme index once, and the original polynomial preparation
once; no source geometry, root chain, jet or progressive programme is built.
Independent invocations remain independent executions.
-/
def prepareProgramme (requested : Rational) (positive : 0 < requested)
    (programmeStart modelStart minimumWorkFloor programmeIndex modelStage : Nat)
    (selected : Search.Selection (32 * movementMass retained.parents)
      (max programmeStart modelStart) (requested / 4))
    (programmeAfter : selected.stage ≤ programmeIndex) (modelAfter : selected.stage ≤ modelStage) :
    ProgrammeComparison retained requests sameCovered childChain coordinate shared entries roots closed
      precision programmeTargets sourceBanks precisionFloor requested positive
      programmeStart modelStart minimumWorkFloor programmeIndex modelStage selected := by
  have sharePositive : 0 < requested / 4 :=
    Order.Field.div_pos_direct positive
      (Cast.Order.natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3))
  let prepared := Closed.PolynomialPreparation.build closed
    (Specification.valueSpecification parameter coordinate)
    (Specification.valueSpecification_denominatorPairs parameter coordinate)
    (requested / 4) sharePositive minimumWorkFloor modelStage
  let sourceBank := sourceBanks programmeIndex
  let compared := PolynomialAttachment.ofComparison (count := count) (floor := floor)
    (targets := (programmeTargets programmeIndex).val)
    retained sourceBank requests sameCovered childChain coordinate
    prepared.work prepared.models prepared.sharedMeshes entries roots prepared.word
    ⟨prepared.comparison, prepared.comparison_eq⟩
  have sameComparison : compared.comparison = prepared.comparison :=
    PolynomialAttachment.ofComparison_comparison (count := count) (floor := floor)
      (targets := (programmeTargets programmeIndex).val) (retained := retained) (sourceBank := sourceBank)
      (requests := requests) (sameCovered := sameCovered) (childChain := childChain) (coordinate := coordinate)
      (work := prepared.work) (models := prepared.models) (shared := prepared.sharedMeshes)
      (entries := entries) (roots := roots) (closed := prepared.word)
      ⟨prepared.comparison, prepared.comparison_eq⟩
  have payment := attachment_payment retained requests sameCovered childChain coordinate shared entries roots closed
    precision programmeTargets sourceBanks precisionFloor requested positive
    programmeStart modelStart minimumWorkFloor programmeIndex modelStage selected
    programmeAfter modelAfter prepared compared sameComparison
  exact ⟨⟨selected, rfl, programmeAfter, modelAfter⟩, prepared, compared, sameComparison, payment.1, payment.2⟩

namespace ProgrammeComparison

variable {retained requests sameCovered childChain coordinate shared entries roots closed}
variable {precision programmeTargets sourceBanks precisionFloor}
variable {requested : Rational} {positive : 0 < requested}
variable {programmeStart modelStart minimumWorkFloor programmeIndex modelStage : Nat}
variable {selected : Search.Selection (32 * movementMass retained.parents)
  (max programmeStart modelStart) (requested / 4)}
variable (compared : ProgrammeComparison retained requests sameCovered childChain coordinate shared entries roots closed
  precision programmeTargets sourceBanks precisionFloor requested positive
  programmeStart modelStart minimumWorkFloor programmeIndex modelStage selected)

/-- Read the SAME original requested word/model preparation with all actual work, P-bank and floor factories. -/
@[expose] def preparation : Closed.PolynomialPreparation.Preparation closed
    (Specification.valueSpecification parameter coordinate)
    (Specification.valueSpecification_denominatorPairs parameter coordinate)
    (requested / 4) (Order.Field.div_pos_direct positive
      (Cast.Order.natCast_pos_direct (n := 4) (Nat.zero_lt_succ 3)))
    minimumWorkFloor modelStage := compared.2.1

/-- Read the original complete source attachment containing that SAME numerical comparison cache. -/
@[expose] def attachment : PolynomialAttachment (count := count) (floor := floor)
    (targets := (programmeTargets programmeIndex).val)
    retained (sourceBanks programmeIndex) requests sameCovered childChain coordinate
    compared.preparation.work compared.preparation.models compared.preparation.sharedMeshes
    entries roots compared.preparation.word := compared.2.2.val

/-- The complete stored geometric selection is the actual request input. -/
theorem selection_eq : compared.1.val = selected := compared.1.property.1

/-- The retained programme index pays the original computed selection floor. -/
theorem programme_after : compared.1.val.stage ≤ programmeIndex := compared.1.property.2.1

/-- The independently retained polynomial-model stage pays that SAME original selection floor. -/
theorem model_after : compared.1.val.stage ≤ modelStage := compared.1.property.2.2

/-- The source attachment stores exactly the original preparation's complete comparison cache. -/
theorem comparison_eq : compared.attachment.comparison = compared.preparation.comparison :=
  compared.2.2.property.1

/-- The actual combined word/model/source allowance strictly pays the positive request. -/
theorem bound_lt : compared.attachment.bound < requested := compared.2.2.property.2.1

/-- The SAME literal outgoing-gap sum and actual fixed programme sample obey the arbitrary requested bound.

The programme index has its own actual selected precision. The gap value
comes from the retained revalued word; no output-name index or model-stage
identification is used.
-/
theorem accurate : normSq (gaussianSum (Closed.gaps compared.preparation.sharedMeshes entries childChain roots
    compared.preparation.word) -
    ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
      (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested :=
  Eq.mp (congrArg (fun value : Canonical => normSq (value -
    ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
      (Specification.Table.valueIndex coordinate)).integral.model programmeIndex).integralSample) < requested)
    compared.preparation.value_eq) compared.2.2.property.2.2

/-- Every sufficiently late actual programme reading compares with the SAME retained outgoing-gap value.

The polynomial-model stage and numerical word stay fixed in the given
preparation. The original bank rule is used only pointwise in the proof of
its actual programme samples; no second numerical preparation, comparison,
root acquisition or source geometry is executed or asserted to be memoized.
-/
theorem later_accurate (later : Nat) (after : compared.1.val.stage ≤ later) :
    normSq (gaussianSum (Closed.gaps compared.preparation.sharedMeshes entries childChain roots
      compared.preparation.word) -
      ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
        (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested := by
  let prepared := compared.preparation
  let attached := PolynomialAttachment.ofComparison (count := count) (floor := floor)
    (targets := (programmeTargets later).val)
    retained (sourceBanks later) requests sameCovered childChain coordinate
    prepared.work prepared.models prepared.sharedMeshes entries roots prepared.word
    ⟨prepared.comparison, prepared.comparison_eq⟩
  have sameComparison : attached.comparison = prepared.comparison :=
    PolynomialAttachment.ofComparison_comparison (count := count) (floor := floor)
      (targets := (programmeTargets later).val) (retained := retained) (sourceBank := sourceBanks later)
      (requests := requests) (sameCovered := sameCovered) (childChain := childChain) (coordinate := coordinate)
      (work := prepared.work) (models := prepared.models) (shared := prepared.sharedMeshes)
      (entries := entries) (roots := roots) (closed := prepared.word)
      ⟨prepared.comparison, prepared.comparison_eq⟩
  have payment := attachment_payment retained requests sameCovered childChain coordinate shared entries roots closed
    precision programmeTargets sourceBanks precisionFloor requested positive
    programmeStart modelStart minimumWorkFloor later modelStage compared.1.val
    after compared.model_after prepared attached sameComparison
  exact Eq.mp (congrArg (fun value : Canonical => normSq (value -
    ((certifiedAtPrecision retained childChain precision programmeTargets sourceBanks precisionFloor
      (Specification.Table.valueIndex coordinate)).integral.model later).integralSample) < requested)
    prepared.value_eq) payment.2

end ProgrammeComparison

end PolynomialAttachment
end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
