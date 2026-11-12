module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Vector.Dependent
import Purelib.Calculus.Jet.DifferenceQuotient
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Cast.Order

/-! # Actual period-base readings in the retained four-row stage quotient

Only the value rows change their base reading. The first and second
source channels remain the derivatives in the same original source jet;
the actual moving StageData and its complete factory remain unchanged.
Independent period/model comparisons pay the base division internally.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
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
    {targetCurrent targetFloor targetRootStage : Nat} {offset : Canonical}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)

/-- One same-member quotient with an independent period base only in its value row.

Order one keeps the original source-first base and source-second slope.
The period stages remain independent of the original source stage and
moving-stage owner; no canonical derivative programme is introduced.
-/
@[expose] def OriginQuotientAt (sourceJet : SynchronizedPeriodJet frame)
    (base : Fin 2 → RefinementProgram) (accuracy : AccuracyRequest) (order coordinate : Fin 2)
    (sourceIndex : Nat) (periodIndex : Fin 2 → Nat) (lastIndex : Nat)
    (retained : StageData cached lastIndex) : Prop :=
  Norm.Basic.normSq
    (((PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
        cached.member.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
      (Fin.cases ((base coordinate).model (periodIndex coordinate)).integralSample
        (Fin.cases ((sourceJet.first coordinate).integral.model sourceIndex).integralSample
          (fun index => Fin.elim0 index)) order)) / offset -
      ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
          (fun index => Fin.elim0 index)) order).model sourceIndex).integralSample) < accuracy.tolerance

/-- All four same-member quotients retain independent source, two period and moving MODEL indices. -/
@[expose] def OriginQuotientBounds (sourceJet : SynchronizedPeriodJet frame)
    (base : Fin 2 → RefinementProgram) (accuracy : AccuracyRequest)
    (sourceFloor : Nat) (periodFloor : Fin 2 → Nat) (lastFloor : Nat) : Prop :=
  ∀ (order coordinate : Fin 2) (sourceIndex : Nat) (periodIndex : Fin 2 → Nat) (lastIndex : Nat),
    sourceFloor ≤ sourceIndex → (∀ coordinate, periodFloor coordinate ≤ periodIndex coordinate) →
    lastFloor ≤ lastIndex →
    ∀ (retained : StageData cached lastIndex), retained = (cached.completed lastIndex).val →
      OriginQuotientAt cached sourceJet base accuracy order coordinate sourceIndex periodIndex lastIndex retained

/-- The existing paid quotient and actual base comparisons derive all four changed-origin bounds.

The original member and source slopes remain unchanged. Each actual
comparison pays tolerance times increment quadrance before division;
its independent source and period floors are retained. The existing
scalar perturbation theorem derives the final bound, including the two
unchanged source-first/source-second rows.
-/
theorem originQuotient_accurate (sourceJet : SynchronizedPeriodJet frame)
    (base : Fin 2 → RefinementProgram) (accuracy : AccuracyRequest) (nonzero : offset ≠ 0)
    (unit : Norm.Basic.normSq offset ≤ 1) {firstFloor lastFloor sourceStart : Nat} {periodStart : Fin 2 → Nat}
    (original : StageQuotientBounds cached sourceJet (accuracy.divide 16
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))) firstFloor lastFloor)
    (compared : DependentVector (fun coordinate : Fin 2 =>
      Comparison (sourceJet.value coordinate).integral.approximation (base coordinate).approximation
        sourceStart (periodStart coordinate) ((accuracy.tolerance / 16) * Norm.Basic.normSq offset))) :
    OriginQuotientBounds cached sourceJet base accuracy
      (Nat.max firstFloor (compared.maximum (fun _ value => value.leftIndex)))
      (fun coordinate => (compared.get coordinate).rightIndex) lastFloor := by
  intro order coordinate sourceIndex periodIndex lastIndex sourceLater periodLater lastLater retained factory
  have originalLater := (Order.le_max_left _ _).trans sourceLater
  have zeroPaid : (0 : Rational) < (accuracy.tolerance / 16) * Norm.Basic.normSq offset :=
    Arithmetic.mul_pos_direct (accuracy.divide 16
      (natCast_pos_direct (n := 16) (Nat.zero_lt_succ 15))).positive (Norm.Basic.normSq_pos nonzero)
  refine Fin.cases ?_ ?_ order
  · let output := (PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
      cached.member.requested.request.chain).cells (Specification.Table.baseIndex 0 coordinate))).integralSample
    let oldBase := ((sourceJet.value coordinate).integral.model sourceIndex).integralSample
    let newBase := ((base coordinate).model (periodIndex coordinate)).integralSample
    let slope := ((sourceJet.first coordinate).integral.model sourceIndex).integralSample
    have oldPaid : Norm.Basic.normSq ((output - oldBase) / offset - slope) < accuracy.tolerance / 16 :=
      original 0 coordinate sourceIndex lastIndex originalLater lastLater retained factory
    have leftLater := (DependentVector.get_le_maximum (fun _ value => value.leftIndex)
      compared coordinate).trans ((Order.le_max_right _ _).trans sourceLater)
    have bounded := (compared.get coordinate).close leftLater (periodLater coordinate)
    have samples := congrArg Norm.Basic.normSq (congrArg₂ (fun first last : Canonical => first - last)
      ((sourceJet.value coordinate).integral.certifiedView_sample sourceIndex)
      ((base coordinate).certifiedView_sample (periodIndex coordinate)))
    have basePaid : Norm.Basic.normSq (newBase - oldBase) <
        (accuracy.tolerance / 16) * Norm.Basic.normSq offset :=
      (Norm.Bounds.normSq_sub_symm newBase oldBase).trans_lt (samples.symm.trans_lt bounded)
    have slopePaid : Norm.Basic.normSq (slope - slope) <
        (accuracy.tolerance / 16) * Norm.Basic.normSq offset := by
      rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
      exact zeroPaid
    exact Calculus.Jet.DifferenceQuotient.perturbation_lt accuracy offset newBase output slope oldBase slope
      nonzero unit basePaid slopePaid oldPaid
  · intro next
    refine Fin.cases ?_ (fun index => Fin.elim0 index) next
    let output := (PathModel.mk ((sources cached.member.requested.request.covered retained.1.preparations
      cached.member.requested.request.chain).cells (Specification.Table.baseIndex 1 coordinate))).integralSample
    let oldBase := ((sourceJet.first coordinate).integral.model sourceIndex).integralSample
    let slope := ((sourceJet.second coordinate).integral.model sourceIndex).integralSample
    have oldPaid : Norm.Basic.normSq ((output - oldBase) / offset - slope) < accuracy.tolerance / 16 :=
      original 1 coordinate sourceIndex lastIndex originalLater lastLater retained factory
    have basePaid : Norm.Basic.normSq (oldBase - oldBase) <
        (accuracy.tolerance / 16) * Norm.Basic.normSq offset := by
      rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
      exact zeroPaid
    have slopePaid : Norm.Basic.normSq (slope - slope) <
        (accuracy.tolerance / 16) * Norm.Basic.normSq offset := by
      rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
      exact zeroPaid
    exact Calculus.Jet.DifferenceQuotient.perturbation_lt accuracy offset oldBase output slope oldBase slope
      nonzero unit basePaid slopePaid oldPaid

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
