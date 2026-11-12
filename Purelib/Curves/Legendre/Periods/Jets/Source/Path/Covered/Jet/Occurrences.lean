module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences

/-! # Six-channel jets from the same positional completion caches

Both the original preparation and the Stage belong to each retained
occurrence completion. Their exact source-list readback supplies the shared
fixed-cycle programme construction; the original ofJet operations derive
the connection and scalar relation bounds internally.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

section

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor rootStage : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (retained : (index : Nat) →
      (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt)

/-- Certify one original channel on the exact source lists of the same positional completion family. -/
def staged (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (constantCycle chain) :=
  PreparedParents.staged (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) channel

/-- Every certified model reads the complete original source list of the retained positional Stage. -/
theorem staged_cells (channel : Fin 6) (index : Nat) :
    ((staged covered chain retained channel).integral.model index).cells =
      (retained index).2.stage.sources.cells channel :=
  PreparedParents.staged_cells (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) channel index

/-- Construct the same fixed-cycle jet from the actual positional Stage and original source preparation family. -/
def jet : SynchronizedPeriodJet frame :=
  PreparedParents.jet (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm)

/-- The positional jet retains the exact fixed lifted cycle supplied to all six programmes. -/
theorem jet_cycle : (jet covered chain retained).cycle = constantCycle chain :=
  PreparedParents.jet_cycle (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm)

/-- The jet attachment retains the same whole positional Stage with its original cycle and request indices. -/
theorem jet_stages (index : Nat) :
    HEq ((jet covered chain retained).source.stages index) ((retained index).2.stage) :=
  PreparedParents.jet_stages (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) index

/-- The positional jet's value integral is the original corresponding six-channel staged integral. -/
theorem jet_value_integral (coordinate : Fin 2) :
    (((jet covered chain retained).value coordinate).integral) =
      (staged covered chain retained (Specification.Table.valueIndex coordinate)).integral :=
  PreparedParents.jet_value_integral (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) coordinate

/-- The positional jet's first integral is the original corresponding six-channel staged integral. -/
theorem jet_first_integral (coordinate : Fin 2) :
    (((jet covered chain retained).first coordinate).integral) =
      (staged covered chain retained (Specification.Table.firstIndex coordinate)).integral :=
  PreparedParents.jet_first_integral (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) coordinate

/-- The positional jet's second integral is the original corresponding six-channel staged integral. -/
theorem jet_second_integral (coordinate : Fin 2) :
    (((jet covered chain retained).second coordinate).integral) =
      (staged covered chain retained (Specification.Table.secondIndex coordinate)).integral :=
  PreparedParents.jet_second_integral (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm) coordinate

/-- Retain the positional jet and both internally derived original-name relation certificates.

The original ofJet constructions consume this same jet and its actual
Stage admissions. No connection or residual closeness estimate is an input.
-/
def build : (actual : SynchronizedPeriodJet frame) ×
    Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  PreparedParents.build (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm)

/-- The relation bundle retains precisely its original positional source jet. -/
theorem build_jet : (build covered chain retained).1 = jet covered chain retained :=
  PreparedParents.build_jet (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) covered chain (fun index => (retained index).1.preparations)
    (fun index => (retained index).2.stage)
    (fun index => (retained index).2.stage_sources.trans (retained index).1.preparations_sources.symm)

variable {retained}

/-- Complete each actual attempt positionally, retaining its whole attempt and new endpoint refinements.

Each callback executes completeOccurrences once. Its original preparations,
Point/Query bank and both old check outcomes remain cached in the returned
member; the new refinements and admissions supply the positional Stage.
Independent callback invocations remain independent executions.
-/
def ofAttempts (attempts : (index : Nat) → StageAttempt covered chain index floor rootStage)
    {root : Named} (roots : RootChain (parent :: parents) root root) :
    (actual : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual :=
  let completed : (index : Nat) →
      (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
    let actual := (attempts index).completeOccurrences roots
    ⟨actual.1, actual.2.val⟩
  build covered chain completed

end

/-- The constructor delegates to the shared six-channel producer on its identical whole positional completion family. -/
private theorem packaged_ofAttempts_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count floor rootStage : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (attempts : (index : Nat) → StageAttempt covered chain index floor rootStage)
    {root : Named} (roots : RootChain (parent :: parents) root root) :
    ofAttempts covered chain attempts roots =
      let completed : (index : Nat) →
          (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
        let actual := (attempts index).completeOccurrences roots
        ⟨actual.1, actual.2.val⟩
      build covered chain completed := by
  unfold ofAttempts
  rfl

/-- The constructor delegates to the shared six-channel producer on its identical whole positional completion family. -/
theorem ofAttempts_factory {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor rootStage : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (attempts : (index : Nat) → StageAttempt covered chain index floor rootStage)
    {root : Named} (roots : RootChain (parent :: parents) root root) :
    ofAttempts covered chain attempts roots =
      let completed : (index : Nat) →
          (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
        let actual := (attempts index).completeOccurrences roots
        ⟨actual.1, actual.2.val⟩
      build covered chain completed := packaged_ofAttempts_factory covered chain attempts roots

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

end
