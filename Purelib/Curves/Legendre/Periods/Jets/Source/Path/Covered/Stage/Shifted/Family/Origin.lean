module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Origin.Jets
public import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring

/-! # Original source readings on an actual cached zero-offset member

The existing source/zero programme comparison is read through the two
given occurrence jets' original model factories. Exact zero-offset
reindexing retains the actual member and its own Frame, without equating
it with the source Frame or reconstructing either preparation family.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (zipWith_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.LinearAlgebra.Gaussian
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {offset : Canonical} {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)

/-- Actual source and cached zero-member value readings obey the original all-later geometric comparison.

The two whole jet factories identify each actual model with its original
programme model. The existing signed occurrence comparison supplies the
bound at their own requested indices. Equality elimination reindexes only
the exact zero offset; the member, preparation families, Frames and source
owners remain distinct retained inputs.
-/
theorem sourceValue_difference_le (zero : offset = 0)
    (sourceCompleted : source.attempt.OccurrenceFamily) (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (sourceCompleted selected).val))
    (coordinate : Fin 2) (earlier firstIndex lastIndex : Nat)
    (firstAfter : earlier ≤ firstIndex) (lastAfter : earlier ≤ lastIndex) :
    Norm.Basic.normSq
      ((((sourceJet.value coordinate).integral.model firstIndex).integralSample) -
        (((cached.jet.value coordinate).integral.model lastIndex).integralSample)) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  cases zero
  exact Shifted.source_base_difference_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (sourceCurrent := current) (sourceFloor := floor) (sourceRootStage := rootStage) (accuracy := reference)
    (target := cached.targetFrame) (admitted := admitted) (widths := widths) (roots := roots)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    source ranges allocation cached.member sourceCompleted cached.completed sourceJet cached.jet
    sourceFactory cached.jet_eq 0 coordinate earlier firstIndex lastIndex firstAfter lastAfter

/-- Two actual value-vector readbacks pay twice the same original source/zero-member comparison radius.

Each vector retains its own pointwise readings from the two original jets.
The scalar comparison applies at both actual coordinate slots; their sum
is the squared vector norm used by finite connection stability. No vector
identity or initial-discrepancy bound is an input.
-/
theorem sourceValues_difference_le (zero : offset = 0)
    (sourceCompleted : source.attempt.OccurrenceFamily) (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (sourceCompleted selected).val))
    (earlier firstIndex lastIndex : Nat) (firstAfter : earlier ≤ firstIndex) (lastAfter : earlier ≤ lastIndex)
    (firstValues lastValues : Vec Canonical 2)
    (firstFactory : ∀ coordinate, firstValues coordinate =
      ((sourceJet.value coordinate).integral.model firstIndex).integralSample)
    (lastFactory : ∀ coordinate, lastValues coordinate =
      ((cached.jet.value coordinate).integral.model lastIndex).integralSample) :
    Norm.vector (zipWith (fun first last => first - last) firstValues lastValues) ≤
      2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  let radius := Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier
  have coordinates (coordinate : Fin 2) : Norm.Basic.normSq
      (zipWith (fun first last => first - last) firstValues lastValues coordinate) ≤ radius :=
    (congrArg Norm.Basic.normSq ((zipWith_apply _ _ _ coordinate).trans
      (congrArg₂ (fun first last : Canonical => first - last)
        (firstFactory coordinate) (lastFactory coordinate)))).trans_le
      (cached.sourceValue_difference_le zero sourceCompleted sourceJet sourceFactory
        coordinate earlier firstIndex lastIndex firstAfter lastAfter)
  have finite := Order.Arithmetic.add_le_add_direct (coordinates 0) (coordinates 1)
  calc
    _ = Norm.Basic.normSq (zipWith (fun first last => first - last) firstValues lastValues 0) +
        Norm.Basic.normSq (zipWith (fun first last => first - last) firstValues lastValues 1) := by
      unfold Norm.vector
      rewrite [sumFin_succ, sumFin_succ]
      rewrite [show (0 : Fin 1).succ = (1 : Fin 2) from rfl]
      change _ + (_ + 0) = _
      ring1
    _ ≤ radius + radius := finite
    _ = 2 * radius := by ring1

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
