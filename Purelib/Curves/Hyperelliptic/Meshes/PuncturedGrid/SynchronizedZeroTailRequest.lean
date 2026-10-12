module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Budget.VanishingSamples
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest

open Purelib.Curves.Hyperelliptic.Periods

open Purelib.Data.Rat

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

public section

/-!
# Retained uniform tails of the corrected synchronized first relation

One geometric request is acquired after paying the sample stream's movement
allowance. Its cached sample controls every later index, allowing the energy
construction to choose a common later sample without acquiring geometry again.
-/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Periods.Pairing (synchronizedPeriodPairingResidual)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {prepared : Prepared paired} {preparation :
    NewtonPreparation base.bank.toBranchCellBank}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {first second : Fin genus} {error radius : Rational} {minimum : Nat}

namespace SynchronizedZeroTailRequest

/-- Exact equality with the original first geometric search paying the retained quarter-target movement budget. -/
@[expose] def SynchronizedTailCutoff (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus)
    (error : Fraction.Rational) (minimum cutoff : Nat) : Prop :=
  cutoff = Search.firstQuarterBelow
    (Pairing.synchronizedPeriodPairingResidual prepared.periodData first second).errorScale minimum (error / 4)

/-- The original synchronized small-sample request at the retained movement cutoff and quarter tolerance. -/
@[expose] def SynchronizedTailSample (prepared : PeriodPrograms.Prepared paired) (preparation :
  BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (cutoff : Nat) :=
  SynchronizedZeroRequest prepared preparation domains first second (error / 4) radius cutoff

/-- The original stream's geometric movement at the retained sample stage is below the quarter target. -/
@[expose] def SynchronizedTailMovement (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus)
    (error : Fraction.Rational) (stage : Nat) : Prop :=
  Geometric.Basic.quarterRadius (Pairing.synchronizedPeriodPairingResidual prepared.periodData first second).errorScale
    stage < error / 4

end SynchronizedZeroTailRequest

set_option genInjectivity false in
/-- A retained original synchronized sample controlling every sufficiently late stream value.

The exact finite movement cutoff and acquired geometric request remain cached for reuse at all later indices. -/
structure SynchronizedZeroTailRequest (prepared : PeriodPrograms.Prepared paired) (preparation :
  BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (minimum : Nat) where
  /-- The cached original geometric movement cutoff. -/ cutoff : Nat
  /-- The cutoff is exactly the retained first geometric search beyond the supplied minimum. -/ cutoff_eq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroTailRequest.SynchronizedTailCutoff prepared first second
    error minimum cutoff
  /-- The actual original geometric small-sample request at the retained cutoff. -/ request :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroTailRequest.SynchronizedTailSample prepared preparation
    domains first second error radius cutoff
  /-- The original stream's movement from the retained acquired stage is paid by the quarter tolerance. -/ movement :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroTailRequest.SynchronizedTailMovement prepared first second
    error request.sample.stage

constructive_injectivity SynchronizedZeroTailRequest

namespace SynchronizedZeroTailRequest

/-- Retain the original acquired small sample and transport the paid geometric movement bound to its actual stage. -/
@[expose] def ofRequest (cutoff : Nat)
    (cutoff_eq : SynchronizedTailCutoff prepared
      first second error minimum cutoff)
    (positive : 0 < error / 4)
    (request : SynchronizedTailSample prepared
      preparation domains first second error radius cutoff) :
    SynchronizedZeroTailRequest prepared
      preparation domains first second error radius minimum := by
  let source := Pairing.synchronizedPeriodPairingResidual prepared.periodData first second
  have paid : Geometric.Basic.quarterRadius source.errorScale cutoff < error / 4 := by
    rw [cutoff_eq]
    exact Search.firstQuarterBelow_accurate source.errorScale source.errorScale_nonneg minimum _ positive
  exact ⟨cutoff, cutoff_eq, request,
    (quarterRadius_antitone source.errorScale_nonneg request.sample.stage_ge).trans_lt paid⟩

/-- Select the original movement cutoff, acquire one quarter-tolerance synchronized sample and retain its uniform tail
certificate. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (preparation : BranchCellBank.NewtonPreparation
  base.bank.toBranchCellBank)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second : Fin genus)
    (error radius : Fraction.Rational) (positive : 0 < error) (radiusPositive : 0 < radius) (minimum : Nat) :
    SynchronizedZeroTailRequest prepared
      preparation domains first second error radius minimum :=
  let source := Pairing.synchronizedPeriodPairingResidual prepared.periodData first second
  let cutoff := Search.firstQuarterBelow source.errorScale minimum (error / 4)
  let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  ofRequest cutoff rfl
    quarterPositive
    (SynchronizedZeroRequest.build prepared preparation domains first second (error / 4) radius quarterPositive
      radiusPositive cutoff)

/-- The actual cached stage of the original acquired synchronized sample. -/
@[expose] def stage (tail :
  SynchronizedZeroTailRequest prepared preparation
  domains first second error radius minimum) : Nat :=
  tail.request.sample.stage

/-- The retained tail stage pays the original supplied minimum. -/
theorem minimum_le (tail :
  SynchronizedZeroTailRequest prepared preparation
  domains first second error radius minimum) :
    minimum ≤ tail.stage := by
  have cutoff : minimum ≤ tail.cutoff := by
    rw [tail.cutoff_eq]
    exact Search.firstQuarterBelow_ge _ _ _
  exact cutoff.trans tail.request.sample.stage_ge

/-- Only the retained sample and geometric movement certificate are used; no new branch isolation, surface preparation,
or integration is performed. -/
theorem later_small (tail :
  SynchronizedZeroTailRequest prepared preparation
  domains first second error radius minimum)
    {later : Nat} (after : tail.stage ≤ later) :
    Data.Gaussian.Norm.Basic.normSq ((Pairing.synchronizedPeriodPairingResidual prepared.periodData first
      second).sample later) < error := by
  let source := Pairing.synchronizedPeriodPairingResidual prepared.periodData first second
  have movement : Data.Gaussian.Norm.Basic.normSq (source.sample later - source.sample tail.stage) < error / 4
    :=
    (source.later_close after).trans_lt tail.movement
  have selected : Data.Gaussian.Norm.Basic.normSq (source.sample tail.stage) < error / 4 :=
    (congrArg Data.Gaussian.Norm.Basic.normSq tail.request.sample.value_eq).symm.trans_lt
      tail.request.sample.small
  have equal : source.sample later - source.sample tail.stage + source.sample tail.stage = source.sample later := by
    ring1
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (source.sample later - source.sample tail.stage)
    (source.sample tail.stage)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct movement selected))
  have budget : 2 * (error / 4 + error / 4) = error :=
    (show 2 * (error / 4 + error / 4) = (error / 4) * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact ((congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt estimate).trans_eq budget

end SynchronizedZeroTailRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
