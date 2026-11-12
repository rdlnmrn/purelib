module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences.Preparations
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-! # Actual value samples of the same completed preparation family

The whole constructor law identifies the original attempted preparation and
its positional completion. Source-list and programme readbacks then identify
each scalar value sample, including both independently requested value
channels. No name comparison or numerical accuracy bound is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

/-- Each value sample of the completed jet is the same sample of the original supplied preparation programme.

The completion's returned attempt is identified by its retained whole
factory law. Its raw and computed-index sources are related by the owned
preparation readbacks, then the actual Stage cells give the scalar sample.
All transport is proof-only; no completion or preparation cache is replayed
by a runtime comparison constructed from this theorem.
-/
private theorem packaged_ofPreparations_value_sample
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {point : LiftedPoint 2} (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (coordinate : Fin 2) (stage : Nat) :
    (((ofPreparations covered chain prepared rootStage roots nonempty).1.value coordinate).integral.model
      stage).integralSample =
      ((PreparedParents.certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.model
        stage).integralSample := by
  cases parents with
  | nil => exact False.elim (nonempty rfl)
  | cons parent parents =>
    have same : PreparedParent.startPoint parent = point := chain.start_eq
    cases same
    let attempts := fun index => StageAttempt.ofPrepared (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) covered chain (CellEndpoints.Targets.build chain.path index) rfl
      (prepared index) rootStage
    let retained : (index : Nat) →
        (attempt : StageAttempt covered chain index floor rootStage) × OccurrenceCompletion attempt := fun index =>
      let actual := (attempts index).completeOccurrences roots
      ⟨actual.1, actual.2.val⟩
    have factory := congrArg (fun bundle : (actual : SynchronizedPeriodJet frame) ×
        Connection.ConnectionCertificate actual × PicardFuchs.PicardFuchsCertificate actual =>
      ((bundle.1.value coordinate).integral.model stage).integralSample)
      (ofPreparations_cons_factory covered chain prepared rootStage roots nonempty)
    have built := congrArg (fun actual : SynchronizedPeriodJet frame =>
      ((actual.value coordinate).integral.model stage).integralSample)
      (build_jet (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (floor := floor) (rootStage := rootStage) covered chain retained)
    have value := congrArg (fun program : RefinementProgram => (program.model stage).integralSample)
      (jet_value_integral (parameter := parameter) (frame := frame) (basis := basis)
        (count := count) (floor := floor) (rootStage := rootStage) covered chain retained coordinate)
    have attemptEq : (retained stage).1 = attempts stage :=
      ((attempts stage).completeOccurrences roots).2.property
    have preparedEq : (retained stage).1.preparations = (prepared stage).castTargets rfl :=
      (congrArg (fun attempt : StageAttempt covered chain stage floor rootStage => attempt.preparations)
        attemptEq).trans
        (StageAttempt.ofPrepared_preparations (parameter := parameter) (frame := frame) (basis := basis)
          (count := count) (index := stage) (floor := floor) covered chain
          (CellEndpoints.Targets.build chain.path stage) rfl (prepared stage) rootStage)
    have source := (retained stage).2.stage_sources.trans (retained stage).1.preparations_sources.symm
    have preparedSources := congrArg (fun actual : PreparedParents covered floor
        (CellEndpoints.Targets.build chain.path stage) => PreparedParents.sources covered actual chain) preparedEq
    have exactSources := source.trans (preparedSources.trans
      (PreparedParents.sources_castTargets covered (prepared stage) rfl chain))
    have stored := staged_cells (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain retained (Specification.Table.valueIndex coordinate) stage
    have original := PreparedParents.certified_cells (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) covered chain prepared (Specification.Table.valueIndex coordinate) stage
    have cells := stored.trans ((congrArg (fun sources => sources.cells
      (Specification.Table.valueIndex coordinate)) exactSources).trans original.symm)
    have sample := congrArg (fun cells => (PathModel.mk cells).integralSample) cells
    have finished := factory.trans (built.trans (value.trans sample))
    exact finished

/-- Each value sample of the completed jet is the same sample of the original supplied preparation programme.

The completion's returned attempt is identified by its retained whole
factory law. Its raw and computed-index sources are related by the owned
preparation readbacks, then the actual Stage cells give the scalar sample.
All transport is proof-only; no completion or preparation cache is replayed
by a runtime comparison constructed from this theorem.
-/
theorem ofPreparations_value_sample
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {point : LiftedPoint 2} (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))
    (rootStage : Nat) {root : Named} (roots : RootChain parents root root) (nonempty : parents ≠ [])
    (coordinate : Fin 2) (stage : Nat) :
    (((ofPreparations covered chain prepared rootStage roots nonempty).1.value coordinate).integral.model
      stage).integralSample =
      ((PreparedParents.certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.model
        stage).integralSample :=
  packaged_ofPreparations_value_sample covered chain prepared rootStage roots nonempty coordinate stage

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceCompletion

end
