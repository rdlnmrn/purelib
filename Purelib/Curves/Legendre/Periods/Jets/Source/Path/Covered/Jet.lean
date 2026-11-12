module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Connection
public import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Fin.Two
import Purelib.Integration.Program.Comparison
import Purelib.Approximation.Gaussian.Equivalence

/-! # Original fixed-cycle source jets and internally constructed relation certificates

Each finite request retains its original preparation product and exact
source Stage. Both completion contracts retain their actual admissions. All six progressive programmes
read that same preparation family. The source attachment consumes the exact
completed source lists; existing ofJet operations derive connection and scalar
residual comparisons on their original arithmetic names.

The derivative specifications are fixed-parameter algebraic integrands here.
No same-cycle parameter-derivative realization or geometric monodromy is
inferred from these relation certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

section

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (stages : (index : Nat) → Stage parameter ⟨point, chain.path⟩ index)
    (exactSources : ∀ index, (stages index).sources = sources covered (prepared index) chain)

/-- Reuse the actual source Stage source lists as the integral models of the certified fixed-cycle programme.

The original progressive programme supplies its proven finite bounds.
withModels retains those same bounds and actual samples on the retained
Stage's stored lists. Uniform certificates are transported by the exact
source-cache equality; no source list is reconstructed by the final model.
-/
def staged (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (constantCycle chain) := by
  let original := certified covered chain prepared channel
  let models := fun index => PathModel.mk ((stages index).sources.cells channel)
  have cellsEq : ∀ index, (models index).cells = (original.integral.model index).cells := by
    intro index
    exact (congrArg (fun sources => sources.cells channel)
      (exactSources index)).trans
        (certified_cells covered chain prepared channel index).symm
  have modelsEq : ∀ index, models index = original.integral.model index := by
    intro index
    exact congrArg PathModel.mk (cellsEq index)
  let actual := original.integral.withModels models (fun index =>
    congrArg (fun model : PathModel => model.integralSample) (modelsEq index)) (by
      intro index
      rewrite [modelsEq index]
      exact original.integral.modelAllowance_le index)
  exact
    { integral := actual
      certificates := by
        intro index
        change UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
          (models index).cells ((constantCycle chain).liftedPath index).path
        exact Eq.mp (congrArg
          (fun cells => UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
            cells ((constantCycle chain).liftedPath index).path) (cellsEq index).symm)
          (original.certificates index) }

/-- The final certified programme retains each actual source Stage's stored original source list. -/
theorem staged_cells (channel : Fin 6) (index : Nat) :
    ((staged covered chain prepared stages exactSources channel).integral.model index).cells =
      (stages index).sources.cells channel := by rfl

/-- The Stage-backed programme keeps the movement scale of the same original physical parent list. -/
theorem staged_errorScale (channel : Fin 6) :
    (staged covered chain prepared stages exactSources channel).integral.errorScale = errorScale parents := by
  change (certified covered chain prepared channel).integral.errorScale = _
  rewrite [certified_integral]
  exact program_errorScale covered chain prepared channel

/-- The stored Stage programme and original prepared programme have the same operational output at every channel.

Only their literal cell readbacks and the same retained source equation
are used. Both original productive programmes and their factories remain
unchanged; this operation constructs their exact same-stage comparison.
-/
def staged_outputEquivalent (channel : Fin 6) :
    NamedEquivalent (staged covered chain prepared stages exactSources channel).integral.output.name
      (certified covered chain prepared channel).integral.output.name :=
  Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_eq _ _ (by
    intro index
    have stored := staged_cells covered chain prepared stages exactSources channel index
    have source := congrArg (fun sources => sources.cells channel) (exactSources index)
    have original := certified_cells covered chain prepared channel index
    exact congrArg (fun cells => (PathModel.mk cells).integralSample)
      (stored.trans (source.trans original.symm)))

/-- The two value programmes consume the identical retained original preparation family and fixed lifted cycle. -/
def value : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.valueSpecification parameter coordinate) (constantCycle chain) :=
  Fin.cases (staged covered chain prepared stages exactSources 0)
    (Fin.cases (staged covered chain prepared stages exactSources 1) (fun index => Fin.elim0 index))

/-- The two first symbolic derivative programmes use the same original preparation and cycle owners. -/
def first : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.firstDerivativeSpecification parameter coordinate) (constantCycle chain) :=
  Fin.cases (staged covered chain prepared stages exactSources 2)
    (Fin.cases (staged covered chain prepared stages exactSources 3) (fun index => Fin.elim0 index))

/-- The two second symbolic derivative programmes use that same original preparation family. -/
def second : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.secondDerivativeSpecification parameter coordinate) (constantCycle chain) :=
  Fin.cases (staged covered chain prepared stages exactSources 4)
    (Fin.cases (staged covered chain prepared stages exactSources 5) (fun index => Fin.elim0 index))

/-- Attach the actual source Stages to the six identical retained original source-cell lists.

The only equalities used are exact target-index transport, the retained
Stage's original sources readback and the programme's literal cell-list
readback. No period comparison or assumed endpoint cancellation is an input.
-/
def attachment : Attachment frame (constantCycle chain) (value covered chain prepared stages exactSources)
    (first covered chain prepared stages exactSources) (second covered chain prepared stages exactSources) where
  stages := stages
  valueZero_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 0).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 0 index
  valueOne_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 1).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 1 index
  firstZero_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 2).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 2 index
  firstOne_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 3).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 3 index
  secondZero_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 4).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 4 index
  secondOne_eq := by
    intro index
    change ((staged covered chain prepared stages exactSources 5).integral.model index).cells = _
    exact staged_cells covered chain prepared stages exactSources 5 index

/-- Construct the original synchronized fixed-parameter jet with its actual same-cache source attachment. -/
def jet : SynchronizedPeriodJet frame :=
  SynchronizedPeriodJet.ofSource (constantCycle chain) (value covered chain prepared stages exactSources)
    (first covered chain prepared stages exactSources) (second covered chain prepared stages exactSources)
    (attachment covered chain prepared stages exactSources)

/-- The original jet keeps the identical staged value integral at each coordinate. -/
theorem jet_value_integral (coordinate : Fin 2) :
    (((jet covered chain prepared stages exactSources).value coordinate).integral) =
      (staged covered chain prepared stages exactSources (Specification.Table.valueIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- Each original jet value output agrees with the certified programme on its identical retained prepared bank. -/
def jet_value_outputEquivalent (coordinate : Fin 2) :
    NamedEquivalent ((jet covered chain prepared stages exactSources).value coordinate).integral.output.name
      (certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.output.name := by
  rewrite [jet_value_integral]
  exact staged_outputEquivalent covered chain prepared stages exactSources (Specification.Table.valueIndex coordinate)

/-- The original jet keeps the identical staged first differential-derivative integral at each coordinate. -/
theorem jet_first_integral (coordinate : Fin 2) :
    (((jet covered chain prepared stages exactSources).first coordinate).integral) =
      (staged covered chain prepared stages exactSources (Specification.Table.firstIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- The original jet keeps the identical staged second differential-derivative integral at each coordinate. -/
theorem jet_second_integral (coordinate : Fin 2) :
    (((jet covered chain prepared stages exactSources).second coordinate).integral) =
      (staged covered chain prepared stages exactSources (Specification.Table.secondIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- Retain the actual constructed jet and both internally paid original-name relation certificates.

Both ofJet operations consume this same jet value and its actual completed
source Stages. Their finite operational comparisons, selected indices and
budgets derive connection_samples_close and residual_samples_close internally.
No such final inequality is supplied by a consumer.
-/
def build : (actual : SynchronizedPeriodJet frame) ×
    Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  let actual := jet covered chain prepared stages exactSources
  let connection := Connection.ConnectionCertificate.ofJet actual
  let residual := PicardFuchs.PicardFuchsCertificate.ofJet actual
  ⟨actual, connection, residual⟩

/-- The relation bundle retains the same actual jet constructor without another source or comparison execution. -/
theorem build_jet :
    (build covered chain prepared stages exactSources).1 = jet covered chain prepared stages exactSources := by rfl

/-- The jet retains the exact fixed lifted cycle supplied to all six programmes. -/
theorem jet_cycle : (jet covered chain prepared stages exactSources).cycle = constantCycle chain := by rfl

/-- The jet reads the whole original Stage at every requested source index, preserving its cycle indices. -/
theorem jet_stages (index : Nat) :
    HEq ((jet covered chain prepared stages exactSources).source.stages index) (stages index) := by rfl

end

namespace StageAttempt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor rootStage : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (retained : (index : Nat) → Completed covered chain index floor rootStage)

/-- Reuse the actual completed Stage source lists as the integral models of the certified fixed-cycle programme.

The original progressive programme supplies its proven finite bounds.
withModels retains those same bounds and actual samples on the completed
Stage's stored lists. Uniform certificates are transported by the exact
source-cache equality; no source list is reconstructed by the final model.
-/
def staged (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (constantCycle chain) :=
  PreparedParents.staged (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2) channel

/-- The final certified programme retains each actual completed Stage's stored original source list. -/
theorem staged_cells (channel : Fin 6) (index : Nat) :
    ((staged covered chain retained channel).integral.model index).cells =
      (retained index).2.2.val.sources.cells channel := by rfl

/-- The two value programmes consume the identical retained original preparation family and fixed lifted cycle. -/
def value : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.valueSpecification parameter coordinate) (constantCycle chain) :=
  PreparedParents.value (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- The two first symbolic derivative programmes use the same original preparation and cycle owners. -/
def first : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.firstDerivativeSpecification parameter coordinate) (constantCycle chain) :=
  PreparedParents.first (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- The two second symbolic derivative programmes use that same original preparation family. -/
def second : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.secondDerivativeSpecification parameter coordinate) (constantCycle chain) :=
  PreparedParents.second (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- Attach the actual completed Stages to the six identical retained original source-cell lists.

The only equalities used are exact target-index transport, the completed
Stage's original sources readback and the programme's literal cell-list
readback. No period comparison or assumed endpoint cancellation is an input.
-/
def attachment : Attachment frame (constantCycle chain) (value covered chain retained)
    (first covered chain retained) (second covered chain retained) :=
  PreparedParents.attachment (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- Construct the original synchronized fixed-parameter jet with its actual same-cache source attachment. -/
def jet : SynchronizedPeriodJet frame :=
  PreparedParents.jet (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- The original jet keeps the identical staged value integral at each coordinate. -/
theorem jet_value_integral (coordinate : Fin 2) :
    (((jet covered chain retained).value coordinate).integral) =
      (staged covered chain retained (Specification.Table.valueIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- The original jet keeps the identical staged first differential-derivative integral at each coordinate. -/
theorem jet_first_integral (coordinate : Fin 2) :
    (((jet covered chain retained).first coordinate).integral) =
      (staged covered chain retained (Specification.Table.firstIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- The original jet keeps the identical staged second differential-derivative integral at each coordinate. -/
theorem jet_second_integral (coordinate : Fin 2) :
    (((jet covered chain retained).second coordinate).integral) =
      (staged covered chain retained (Specification.Table.secondIndex coordinate)).integral := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- Retain the actual constructed jet and both internally paid original-name relation certificates.

Both ofJet operations consume this same jet value and its actual completed
source Stages. Their finite operational comparisons, selected indices and
budgets derive connection_samples_close and residual_samples_close internally.
No such final inequality is supplied by a consumer.
-/
def build : (actual : SynchronizedPeriodJet frame) ×
    Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  PreparedParents.build (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.2.val)
    (fun index => Completion.stage_sources (retained index).1 (retained index).2)

/-- The relation bundle retains the same actual jet constructor without another source or comparison execution. -/
theorem build_jet : (build covered chain retained).1 = jet covered chain retained := by rfl

/-- Construct the actual fixed-cycle jet and relation certificates from retained attempts and genuine geometric inputs.

Each finite completion callback reads its actual attempt once. Independent
callbacks remain independent executions. The actual
original distinct bank and the supplied closed RootChain pay completion;
ready old Commons are reused by the original completion operation. The same
completed request family supplies all six programme and source-stage owners.
-/
def ofAttempts (attempts : (index : Nat) → StageAttempt covered chain index floor rootStage)
    (distinct : ∀ index, Vertex.Bank.Distinct (attempts index).2.2.1.val) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    (actual : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  let completed := fun index => Completed.acquire (attempts index) (distinct index) roots
  build covered chain completed

/-- Construct the same source-attached fixed-cycle jet from actual successful original attempts without Distinct.

Each callback retains its actual attempt once. Completion reads that
attempt's already stored successful Stage and ready Commons/admissions;
all six programmes consume the identical original sources and targets.
The input success certificate concerns the actual finite checks, not a
desired relation inequality. Total repeated-visit coherence remains separate.
-/
def ofReadyAttempts (attempts : (index : Nat) → StageAttempt covered chain index floor rootStage)
    (paid : ∀ index, (attempts index).Ready) :
    (actual : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  let completed := fun index =>
    let attempt := attempts index
    Completed.ofReady attempt (paid index)
  build covered chain completed

end StageAttempt

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
