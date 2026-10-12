module
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib

public section

/-!
Cache any certified dyadic bank, including the actual result of a coarser
executed check, without running its checker again.  Request provenance and
proper parameter edges are proved from the retained construction; neither
is an extra caller obligation.  Only the existing finite path module is
imported, with no additional algebra or generated-certificate dependency.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache

open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath

/-- A successful dyadic preparation retains the requested depth and diameter and strictly ordered parameter edges. -/
private theorem tryDyadic_provenance {polynomial : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {ambient :
  Riemann.Paths.PreparedClearPathModels.Box}
    {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian} (path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish)
    (within : path.WithinAmbient) (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start))
    (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    {prepared : Riemann.Paths.PreparedClearPathModels.PreparedPath path owner}
    (success : Riemann.Paths.PreparedClearPathModels.PreparedPath.tryDyadic path within owner depth diameter positive =
      some prepared) :
    Riemann.Paths.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth diameter positive prepared ∧
      Riemann.Paths.PreparedClearPathModels.PreparedPath.AllEdgesProper prepared := by
  induction path with
  | nil point =>
      simp only [Riemann.Paths.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      cases success
      exact ⟨trivial, trivial⟩
  | cons head tail ih =>
      rw [Riemann.Paths.PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      · contradiction
      · rename_i subdivision headSuccess
        simp only at success
        split at success
        · contradiction
        · rename_i preparedTail tailSuccess
          cases success
          have tailFacts := ih within.tail _ tailSuccess
          refine ⟨⟨CompleteSegment.ofTryDyadic_requests head within.head owner depth diameter positive headSuccess,
            tailFacts.1⟩, ⟨?_, tailFacts.2⟩⟩
          rw [Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofTryDyadic_parameterEdges]
          exact Riemann.Paths.PreparedClearPathModels.PreparedPath.dyadicEdges_strictParameterEdges depth
            Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint (by
            decide)

/-- An executed checked dyadic spine retains its original request provenance and proper parameter edges. -/
private theorem executed_provenance {polynomial : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {ambient :
  Riemann.Paths.PreparedClearPathModels.Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian} {path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)}
    (checked : Riemann.Paths.PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic depth diameter positive path
      owner) :
    Riemann.Paths.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth diameter positive checked.prepared ∧
      Riemann.Paths.PreparedClearPathModels.PreparedPath.AllEdgesProper checked.prepared := by
  induction checked with
  | nil => exact ⟨trivial, trivial⟩
  | cons head tail owner within safe remaining ih =>
      refine ⟨⟨?_, ih.1⟩, ⟨?_, ih.2⟩⟩
      · exact Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofTryDyadic_requests head within owner depth
          diameter positive _
      · rw [Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofExecutedDyadic_parameterEdges]
        exact Riemann.Paths.PreparedClearPathModels.PreparedPath.dyadicEdges_strictParameterEdges depth
          Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint (by
          decide)

namespace DyadicBank

open Purelib.RootIsolation
/-- Every supported dyadic bank carries the requested parameters and proper edges in its actual prepared spine. -/
theorem prepared_provenance {polynomial : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {ambient :
  Riemann.Paths.PreparedClearPathModels.Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian} {path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)} (bank :
      Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth diameter positive path owner) :
    Riemann.Paths.PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth diameter positive bank.prepared ∧
      Riemann.Paths.PreparedClearPathModels.PreparedPath.AllEdgesProper bank.prepared := by
  cases bank with
  | safe checked =>
      exact ⟨Riemann.Paths.PreparedPathGluing.CheckedDyadic.prepared_generated checked,
        Riemann.Paths.PreparedPathGluing.CheckedDyadic.prepared_proper checked⟩
  | executed within prepared success =>
      exact SquareRoot.Preparation.Bank.Cache.tryDyadic_provenance path within owner
        depth diameter positive success
  | executedCertified checked => exact SquareRoot.Preparation.Bank.Cache.executed_provenance checked
  | certified certificate => exact ⟨certificate.generated, certificate.prepared_allEdgesProper⟩

/-- Retain the actual prepared spine once.  Correctness proofs consume its
existing evidence, not a replay of the executable comparisons. -/
@[expose] def cache {polynomial : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {ambient :
  Riemann.Paths.PreparedClearPathModels.Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian} {path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)} (bank :
      Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth diameter positive path owner) :
    Riemann.Paths.PreparedClearPathModels.PreparedPath.CertifiedDyadic depth diameter positive path owner where
  within := bank.within
  prepared := bank.prepared
  generated := (SquareRoot.Preparation.Bank.Cache.DyadicBank.prepared_provenance bank).1
  prepared_allEdgesProper := (SquareRoot.Preparation.Bank.Cache.DyadicBank.prepared_provenance bank).2
  prepared_stepCount := bank.prepared_stepCount
  prepared_toClearPath := bank.prepared_toClearPath_eq_dyadicRefinePath

end DyadicBank

namespace CertifiedDyadic

open Purelib.Data.Nat in
/-- Construct the certified dyadic cache from the original clear-path spine.

Each accepted head subdivision is retained before its actual terminal owner is passed to the recursive tail. Request
provenance, cell counts and clear-path equality are proved from those same caches. -/
@[expose] def totalCachedAt {polynomial : Riemann.Paths.PreparedClearPathModels.GaussianPolynomial} {ambient :
  Riemann.Paths.PreparedClearPathModels.Box} (depth : Nat)
    (diameter : Fraction.Rational) (positive : 0 < diameter) :
    ∀ {start finish : Riemann.Paths.PreparedClearPathModels.Gaussian} (path : Polynomial.Geometry.ClearPath polynomial
      ambient start finish)
      (_within : path.WithinAmbient) (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)),
      Riemann.Paths.PreparedClearPathModels.sufficientDepth path diameter ≤ depth →
        Riemann.Paths.PreparedClearPathModels.PreparedPath.CertifiedDyadic depth diameter positive path owner
  | _, _, .nil point, within, owner, _ =>
      { within := within
        prepared := .nil point owner
        generated := trivial
        prepared_allEdgesProper := trivial
        prepared_stepCount := (Nat.mul_zero _).symm
        prepared_toClearPath := rfl }
  | _, _, .cons head tail, within, owner, enough => by
      have headEnough := (Riemann.Paths.PreparedClearPathModels.headSufficientDepth_le head tail diameter).trans enough
      have tailEnough := (Riemann.Paths.PreparedClearPathModels.tailSufficientDepth_le head tail diameter).trans enough
      have safe := Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
        head Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
          (Riemann.Paths.PreparedClearPathModels.ownerAtStart head owner) depth diameter positive (by decide) headEnough
      let first := Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofSafeDyadic head within.head owner depth
        diameter positive safe
      let rest := Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache.CertifiedDyadic.totalCachedAt depth diameter
        positive tail within.tail first.finishOwner tailEnough
      exact
        { within := within
          prepared := .cons head tail owner within.head first rest.prepared
          generated := ⟨CompleteSegment.ofSafeDyadic_requests head within.head owner depth diameter positive safe,
            rest.generated⟩
          prepared_allEdgesProper := ⟨by
            rw [Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofSafeDyadic_parameterEdges]
            exact Riemann.Paths.PreparedClearPathModels.PreparedPath.dyadicEdges_strictParameterEdges depth
              Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint (by
              decide),
            rest.prepared_allEdgesProper⟩
          prepared_stepCount := by
            change first.subdivision.stepCount + rest.prepared.stepCount = _
            rw [rest.prepared_stepCount, Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofSafeDyadic_stepCount]
            dsimp only [Polynomial.Geometry.ClearPath.segmentCount]
            rw [Multiplication.left_distrib, Nat.mul_one]
            exact Nat.add_comm _ _
          prepared_toClearPath := by
            change first.clearPath.append rest.prepared.toClearPath = _
            rw [rest.prepared_toClearPath, Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofSafeDyadic_clearPath]
            rfl }

end CertifiedDyadic

end Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
