module

import Purelib.Examples.Curves.Legendre.RegularCycle.Periods
import Purelib.Examples.Curves.Legendre.RegularCycle.Rotated
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Approximation.Gaussian.Name.Sampling

/-!
# Operational relations on the original admitted four-cell cycle

Both original sheets retain all six differential programs, actual finite
model discrepancies and source-stage endpoint admissions. The connection
and scalar constructors consume that original jet without a final sample
comparison premise. The local cycle is contractible; these regressions do
not assert a nonzero period or differentiation of a moving cycle.
-/

namespace TestPurelib.Curves.Legendre.PeriodRelations

open Purelib
open Purelib.Examples.Curves.Legendre.RegularCycle
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Rational
open Purelib.Integration.Path.Primitive

private def original (sheet : Fin 2) := (Schedule.build sheet).jet

attribute [local irreducible] original

private def firstSource (sheet coordinate : Fin 2) : CoherentNamed :=
  Connection.connectionPrimitiveSource (original sheet) coordinate

private def scalarSource (sheet : Fin 2) : CoherentNamed :=
  ((original sheet).source.stages 0).base.original.scalar.channel

private def connection (sheet : Fin 2) := Connection.ConnectionCertificate.ofJet (original sheet)

private def scalar (sheet : Fin 2) := PicardFuchs.PicardFuchsCertificate.ofJet (original sheet)

/-- Use all six original programs on the same cells with their actual rotated lifted basepoint. -/
private def rotated (sheet : Fin 2) := Rotated.jet (Schedule.build sheet)

attribute [local irreducible] rotated

private def rotatedConnection (sheet : Fin 2) := Connection.ConnectionCertificate.ofJet (rotated sheet)

private def rotatedScalar (sheet : Fin 2) := PicardFuchs.PicardFuchsCertificate.ofJet (rotated sheet)

/-- Retain the actual comparison made with unequal original starting indices. -/
private def delayedConnection (sheet coordinate : Fin 2) :=
  ((connection sheet).coordinate_with_primitive coordinate).compare 2 5 1 (by decide)

/-- The scalar client independently requests its own unequal starting indices. -/
private def delayedScalar (sheet : Fin 2) :=
  (scalar sheet).residual_equivalent_primitive.compare 3 7 1 (by decide)

/-- One actual bundled request supplies both original row selections. -/
private def selectedRows (sheet : Fin 2) (request : Nat) :=
  let retained := (connection sheet).select request
  (retained.firstSelection, retained.secondSelection)

example (sheet coordinate : Fin 2) :
    NamedEquivalent (Connection.connectionScaledFirst (original sheet) coordinate).name
      (Connection.connectionAction (original sheet) coordinate).name :=
  (connection sheet).coordinate_connection coordinate

example (sheet : Fin 2) :
    NamedEquivalent (PicardFuchs.picardFuchsResidual (original sheet)).name (Coherence.exact 0).name :=
  (scalar sheet).operational_zero

example (sheet coordinate : Fin 2) :
    NamedEquivalent (Connection.connectionScaledFirst (rotated sheet) coordinate).name
      (Connection.connectionAction (rotated sheet) coordinate).name :=
  (rotatedConnection sheet).coordinate_connection coordinate

example (sheet : Fin 2) :
    NamedEquivalent (PicardFuchs.picardFuchsResidual (rotated sheet)).name (Coherence.exact 0).name :=
  (rotatedScalar sheet).operational_zero

example (sheet coordinate : Fin 2) : 2 ≤ (delayedConnection sheet coordinate).leftIndex :=
  (delayedConnection sheet coordinate).left_ge

example (sheet coordinate : Fin 2) : 5 ≤ (delayedConnection sheet coordinate).rightIndex :=
  (delayedConnection sheet coordinate).right_ge

example (sheet coordinate : Fin 2) (leftLater rightLater : Nat)
    (leftOrder : (delayedConnection sheet coordinate).leftIndex ≤ leftLater)
    (rightOrder : (delayedConnection sheet coordinate).rightIndex ≤ rightLater) :
    Data.Gaussian.Norm.Basic.normSq
      (((Sampling.approximation
          (Connection.connectionScaledFirst (original sheet) coordinate).name).sample leftLater) -
        ((Sampling.approximation
          (Connection.connectionWithPrimitive (original sheet) (connection sheet).primitive coordinate).name).sample
            rightLater)) < 1 :=
  (delayedConnection sheet coordinate).close leftOrder rightOrder

example (sheet : Fin 2) : 3 ≤ (delayedScalar sheet).leftIndex :=
  (delayedScalar sheet).left_ge

example (sheet : Fin 2) : 7 ≤ (delayedScalar sheet).rightIndex :=
  (delayedScalar sheet).right_ge

example (sheet : Fin 2) (leftLater rightLater : Nat)
    (leftOrder : (delayedScalar sheet).leftIndex ≤ leftLater)
    (rightOrder : (delayedScalar sheet).rightIndex ≤ rightLater) :
    Data.Gaussian.Norm.Basic.normSq
      (((Sampling.approximation
          (PicardFuchs.picardFuchsResidual (original sheet)).name).sample leftLater) -
        ((Sampling.approximation
          (scalar sheet).primitive.integralSum.name).sample rightLater)) < 1 :=
  (delayedScalar sheet).close leftOrder rightOrder

example (sheet coordinate : Fin 2) (request : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (((Integration.Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (Connection.connectionScaledFirst (original sheet) coordinate)).model
            ((connection sheet).schedule.targetIndex request)).integralSample -
        ((Integration.Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (Connection.connectionWithPrimitive (original sheet) (connection sheet).primitive coordinate)).model
            ((connection sheet).schedule.comparisonIndex request)).integralSample) ≤
      Geometric.Basic.quarterRadius (connection sheet).budget.total request :=
  (connection sheet).connection_samples_close coordinate request

example (sheet : Fin 2) (request : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (((Integration.Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (PicardFuchs.picardFuchsResidual (original sheet))).model
            ((scalar sheet).schedule.targetIndex request)).integralSample -
        ((Integration.Program.Gaussian.Basic.RefinementProgram.ofCoherentNamed
          (scalar sheet).primitive.integralSum).model
            ((scalar sheet).schedule.comparisonIndex request)).integralSample) ≤
      Geometric.Basic.quarterRadius (scalar sheet).budget.total request :=
  (scalar sheet).residual_samples_close request

example (sheet : Fin 2) (request : Nat) :
    (selectedRows sheet request).1.observation.leftIndex =
      (selectedRows sheet request).2.observation.leftIndex := rfl

example (sheet : Fin 2) (request : Nat) :
    (selectedRows sheet request).1.observation.rightIndex =
      (selectedRows sheet request).2.observation.rightIndex := rfl

example (sheet coordinate : Fin 2) :
    ∃ edge : PrimitiveEdge (firstSource sheet coordinate) (firstSource sheet coordinate),
      edge.program = Connection.connectionResidualProgram (original sheet) coordinate ∧
        (Connection.connectionPrimitive (original sheet) coordinate).path =
          .cons edge (.nil (firstSource sheet coordinate)) :=
  ClosedPrimitiveBoundary.ofClosedSampleComparison_nonempty _ _ _ _ _

example (sheet : Fin 2) :
    ∃ edge : PrimitiveEdge (scalarSource sheet) (scalarSource sheet),
      edge.program = PicardFuchs.picardFuchsResidualProgram (original sheet) ∧
        (PicardFuchs.picardFuchsPrimitive (original sheet)).path =
          .cons edge (.nil (scalarSource sheet)) :=
  ClosedPrimitiveBoundary.ofClosedSampleComparison_nonempty _ _ _ _ _

end TestPurelib.Curves.Legendre.PeriodRelations
