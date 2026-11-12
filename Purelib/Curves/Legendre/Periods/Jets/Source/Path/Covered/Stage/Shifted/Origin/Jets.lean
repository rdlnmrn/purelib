module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Origin
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences.Programs
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Actual source and zero-member occurrence-jet outputs

Both supplied jets keep their own original whole completion-family factory
equations. A single six-channel bank of the original programme equivalences
is transported through exact pointwise model readbacks. Every output name
is the original given jet's name; no curve or Frame equality is used.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {sourceCurrent sourceFloor sourceRootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain sourceCurrent sourceFloor sourceRootStage accuracy)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {target : Paths.Frame (parameter + 0)} {admitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (parameter := parameter) (increment := 0) (frame := frame) (basis := basis)
      (target := target) (count := count) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)

/-- All six original given source-jet names agree operationally with the SAME actual zero-member jet names.

The two occurrence families, given jets and their whole factory equations
are fixed before any comparison tolerance. One six-channel bank retains
the original source_programmes_equivalent operations. The owned family
and Request readbacks transport their same actual models and comparisons
to the given jets; both Frame, cycle and source owners remain distinct.
-/
def source_jets_equivalent
    (sourceCompleted : source.attempt.OccurrenceFamily)
    (zeroCompleted : retained.requested.request.attempt.OccurrenceFamily)
    (sourceJet : SynchronizedPeriodJet frame) (zeroJet : SynchronizedPeriodJet target)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun selected => (sourceCompleted selected).val))
    (zeroFactory : zeroJet = OccurrenceCompletion.jet (parameter := parameter + 0) (frame := target)
      (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
      retained.requested.request.covered retained.requested.request.chain
        (fun selected => (zeroCompleted selected).val)) :
    ((coordinate : Fin 2) → NamedEquivalent (sourceJet.valueName coordinate).name (zeroJet.valueName coordinate).name) ×
    ((coordinate : Fin 2) → NamedEquivalent (sourceJet.firstName coordinate).name (zeroJet.firstName coordinate).name) ×
    ((coordinate : Fin 2) → NamedEquivalent
      (sourceJet.secondName coordinate).name (zeroJet.secondName coordinate).name) :=
  let comparisons := DependentVector.ofFn (fun channel : Fin 6 => source_programmes_equivalent
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (target := target) (admitted := admitted) (widths := widths) (roots := roots)
    source ranges allocation retained channel)
  let value := fun coordinate : Fin 2 => RefinementProgram.outputEquivalent
    (program covered chain source.attempt.preparationFamily (Specification.Table.valueIndex coordinate))
    (retained.requested.request.programme (Specification.Table.valueIndex coordinate))
    (sourceJet.value coordinate).integral (zeroJet.value coordinate).integral
    (comparisons.get (Specification.Table.valueIndex coordinate))
    (fun stage => (OccurrenceFamily.value_model
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := source.selected.stage) (floor := sourceFloor)
      (rootStage := sourceRootStage) (attempt := source.attempt)
      sourceCompleted sourceJet sourceFactory coordinate stage).trans
        (program_model covered chain source.attempt.preparationFamily
          (Specification.Table.valueIndex coordinate) stage).symm)
    (fun stage => retained.requested.request.occurrence_value_model
      (parameter := parameter) (increment := 0) (target := target) (basis := basis) (count := count)
      (geometry := retained.geometry) (index := retained.requested.selected.stage)
      (floor := targetFloor) (rootStage := targetRootStage) zeroCompleted zeroJet zeroFactory coordinate stage)
  let first := fun coordinate : Fin 2 => RefinementProgram.outputEquivalent
    (program covered chain source.attempt.preparationFamily (Specification.Table.firstIndex coordinate))
    (retained.requested.request.programme (Specification.Table.firstIndex coordinate))
    (sourceJet.first coordinate).integral (zeroJet.first coordinate).integral
    (comparisons.get (Specification.Table.firstIndex coordinate))
    (fun stage => (OccurrenceFamily.first_model
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := source.selected.stage) (floor := sourceFloor)
      (rootStage := sourceRootStage) (attempt := source.attempt)
      sourceCompleted sourceJet sourceFactory coordinate stage).trans
        (program_model covered chain source.attempt.preparationFamily
          (Specification.Table.firstIndex coordinate) stage).symm)
    (fun stage => retained.requested.request.occurrence_first_model
      (parameter := parameter) (increment := 0) (target := target) (basis := basis) (count := count)
      (geometry := retained.geometry) (index := retained.requested.selected.stage)
      (floor := targetFloor) (rootStage := targetRootStage) zeroCompleted zeroJet zeroFactory coordinate stage)
  let second := fun coordinate : Fin 2 => RefinementProgram.outputEquivalent
    (program covered chain source.attempt.preparationFamily (Specification.Table.secondIndex coordinate))
    (retained.requested.request.programme (Specification.Table.secondIndex coordinate))
    (sourceJet.second coordinate).integral (zeroJet.second coordinate).integral
    (comparisons.get (Specification.Table.secondIndex coordinate))
    (fun stage => (OccurrenceFamily.second_model
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := source.selected.stage) (floor := sourceFloor)
      (rootStage := sourceRootStage) (attempt := source.attempt)
      sourceCompleted sourceJet sourceFactory coordinate stage).trans
        (program_model covered chain source.attempt.preparationFamily
          (Specification.Table.secondIndex coordinate) stage).symm)
    (fun stage => retained.requested.request.occurrence_second_model
      (parameter := parameter) (increment := 0) (target := target) (basis := basis) (count := count)
      (geometry := retained.geometry) (index := retained.requested.selected.stage)
      (floor := targetFloor) (rootStage := targetRootStage) zeroCompleted zeroJet zeroFactory coordinate stage)
  ⟨value, first, second⟩

/-- Actual source and zero-member base readings obey the original six-channel all-later radius.

The same two given jets and whole family factories identify the actual
models. The original zero-Step signed comparison supplies the bound;
source and generated-zero Frames remain distinct retained owners.
-/
theorem source_base_difference_le
    (sourceCompleted : source.attempt.OccurrenceFamily)
    (zeroCompleted : retained.requested.request.attempt.OccurrenceFamily)
    (sourceJet : SynchronizedPeriodJet frame) (zeroJet : SynchronizedPeriodJet target)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun selected => (sourceCompleted selected).val))
    (zeroFactory : zeroJet = OccurrenceCompletion.jet (parameter := parameter + 0) (frame := target)
      (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
      retained.requested.request.covered retained.requested.request.chain
        (fun selected => (zeroCompleted selected).val))
    (order coordinate : Fin 2) (earlier firstIndex lastIndex : Nat)
    (firstAfter : earlier ≤ firstIndex) (lastAfter : earlier ≤ lastIndex) :
    Norm.Basic.normSq
      (((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((zeroJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((zeroJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model lastIndex).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  have firstModel := (OccurrenceFamily.base_model (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (index := source.selected.stage) (floor := sourceFloor) (rootStage := sourceRootStage)
    (attempt := source.attempt) sourceCompleted sourceJet sourceFactory order coordinate firstIndex).trans
      (program_model covered chain source.attempt.preparationFamily
        (Specification.Table.baseIndex order coordinate) firstIndex).symm
  have lastModel := retained.requested.request.occurrence_base_model
    (parameter := parameter) (increment := 0) (target := target) (basis := basis) (count := count)
    (geometry := retained.geometry) (index := retained.requested.selected.stage)
    (floor := targetFloor) (rootStage := targetRootStage) zeroCompleted zeroJet zeroFactory order coordinate lastIndex
  have original := source_programmes_later_close
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (target := target) (admitted := admitted) (widths := widths) (roots := roots)
    source ranges allocation retained (Specification.Table.baseIndex order coordinate)
    earlier firstIndex lastIndex firstAfter lastAfter
  exact (congrArg₂ (fun first last : PathModel => Norm.Basic.normSq
    (first.integralSample - last.integralSample)) firstModel lastModel).trans_le original

/-- Actual source and zero-member slope readings obey the original six-channel all-later radius.

The same two given jets and whole family factories identify the actual
models. The original zero-Step signed comparison supplies the bound;
source and generated-zero Frames remain distinct retained owners.
-/
theorem source_slope_difference_le
    (sourceCompleted : source.attempt.OccurrenceFamily)
    (zeroCompleted : retained.requested.request.attempt.OccurrenceFamily)
    (sourceJet : SynchronizedPeriodJet frame) (zeroJet : SynchronizedPeriodJet target)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun selected => (sourceCompleted selected).val))
    (zeroFactory : zeroJet = OccurrenceCompletion.jet (parameter := parameter + 0) (frame := target)
      (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
      retained.requested.request.covered retained.requested.request.chain
        (fun selected => (zeroCompleted selected).val))
    (order coordinate : Fin 2) (earlier firstIndex lastIndex : Nat)
    (firstAfter : earlier ≤ firstIndex) (lastAfter : earlier ≤ lastIndex) :
    Norm.Basic.normSq
      (((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((zeroJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((zeroJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model lastIndex).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  have firstModel := (OccurrenceFamily.slope_model (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (index := source.selected.stage) (floor := sourceFloor) (rootStage := sourceRootStage)
    (attempt := source.attempt) sourceCompleted sourceJet sourceFactory order coordinate firstIndex).trans
      (program_model covered chain source.attempt.preparationFamily
        (Specification.Table.slopeIndex order coordinate) firstIndex).symm
  have lastModel := retained.requested.request.occurrence_slope_model
    (parameter := parameter) (increment := 0) (target := target) (basis := basis) (count := count)
    (geometry := retained.geometry) (index := retained.requested.selected.stage)
    (floor := targetFloor) (rootStage := targetRootStage) zeroCompleted zeroJet zeroFactory order coordinate lastIndex
  have original := source_programmes_later_close
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (target := target) (admitted := admitted) (widths := widths) (roots := roots)
    source ranges allocation retained (Specification.Table.slopeIndex order coordinate)
    earlier firstIndex lastIndex firstAfter lastAfter
  exact (congrArg₂ (fun first last : PathModel => Norm.Basic.normSq
    (first.integralSample - last.integralSample)) firstModel lastModel).trans_le original

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
