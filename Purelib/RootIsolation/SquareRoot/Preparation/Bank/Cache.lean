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
private theorem tryDyadic_provenance {polynomial : GaussianPolynomial} {ambient :
  Box}
    {start finish : Gaussian} (path : Geometry.ClearPath polynomial
      ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (diameter : Fraction.Rational) (positive : 0 < diameter)
    {prepared : PreparedPath path owner}
    (success : tryDyadic path within owner depth diameter positive =
      some prepared) :
    AllRequestsDyadic depth diameter positive prepared ∧
      AllEdgesProper prepared := by
  induction path with
  | nil point =>
      simp only [tryDyadic] at success
      cases success
      exact ⟨trivial, trivial⟩
  | cons head tail ih =>
      rw [tryDyadic] at success
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
          rw [CompleteSegment.ofTryDyadic_parameterEdges]
          exact dyadicEdges_strictParameterEdges depth
            zeroEndpoint oneEndpoint (by
            decide)

/-- An executed checked dyadic spine retains its original request provenance and proper parameter edges. -/
private theorem executed_provenance {polynomial : GaussianPolynomial} {ambient :
  Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Owner (polynomial.eval start)}
    (checked : ExecutedCheckedDyadic depth diameter positive path
      owner) :
    AllRequestsDyadic depth diameter positive checked.prepared ∧
      AllEdgesProper checked.prepared := by
  induction checked with
  | nil => exact ⟨trivial, trivial⟩
  | cons head tail owner within safe remaining ih =>
      refine ⟨⟨?_, ih.1⟩, ⟨?_, ih.2⟩⟩
      · exact CompleteSegment.ofTryDyadic_requests head within owner depth
          diameter positive _
      · rw [CompleteSegment.ofExecutedDyadic_parameterEdges]
        exact dyadicEdges_strictParameterEdges depth
          zeroEndpoint oneEndpoint (by
          decide)

namespace DyadicBank

open Purelib.RootIsolation
/-- Every supported dyadic bank carries the requested parameters and proper edges in its actual prepared spine. -/
theorem prepared_provenance {polynomial : GaussianPolynomial} {ambient :
  Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Owner (polynomial.eval start)} (bank :
      DyadicBank depth diameter positive path owner) :
    AllRequestsDyadic depth diameter positive bank.prepared ∧
      AllEdgesProper bank.prepared := by
  cases bank with
  | safe checked =>
      exact ⟨Riemann.Paths.PreparedPathGluing.CheckedDyadic.prepared_generated checked,
        Riemann.Paths.PreparedPathGluing.CheckedDyadic.prepared_proper checked⟩
  | executed within prepared success =>
      exact tryDyadic_provenance path within owner
        depth diameter positive success
  | executedCertified checked => exact executed_provenance checked
  | certified certificate => exact ⟨certificate.generated, certificate.prepared_allEdgesProper⟩

/-- Retain the actual prepared spine once.  Correctness proofs consume its
existing evidence, not a replay of the executable comparisons. -/
@[expose] def cache {polynomial : GaussianPolynomial} {ambient :
  Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Geometry.ClearPath polynomial
      ambient start finish}
    {owner : Owner (polynomial.eval start)} (bank :
      DyadicBank depth diameter positive path owner) :
    CertifiedDyadic depth diameter positive path owner where
  within := bank.within
  prepared := bank.prepared
  generated := (prepared_provenance bank).1
  prepared_allEdgesProper := (prepared_provenance bank).2
  prepared_stepCount := bank.prepared_stepCount
  prepared_toClearPath := bank.prepared_toClearPath_eq_dyadicRefinePath

end DyadicBank

namespace CertifiedDyadic

open Purelib.Data.Nat in
/-- Construct the certified dyadic cache from the original clear-path spine.

Each accepted head subdivision is retained before its actual terminal owner is passed to the recursive tail. Request
provenance, cell counts and clear-path equality are proved from those same caches. -/
@[expose] def totalCachedAt {polynomial : GaussianPolynomial} {ambient :
  Box} (depth : Nat)
    (diameter : Fraction.Rational) (positive : 0 < diameter) :
    ∀ {start finish : Gaussian} (path : Geometry.ClearPath polynomial
      ambient start finish)
      (_within : path.WithinAmbient) (owner : Owner (polynomial.eval start)),
      sufficientDepth path diameter ≤ depth →
        CertifiedDyadic depth diameter positive path owner
  | _, _, .nil point, within, owner, _ =>
      { within := within
        prepared := .nil point owner
        generated := trivial
        prepared_allEdgesProper := trivial
        prepared_stepCount := (Nat.mul_zero _).symm
        prepared_toClearPath := rfl }
  | _, _, .cons head tail, within, owner, enough => by
      have headEnough := (headSufficientDepth_le head tail diameter).trans enough
      have tailEnough := (tailSufficientDepth_le head tail diameter).trans enough
      have safe := Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
        head zeroEndpoint oneEndpoint
          (ownerAtStart head owner) depth diameter positive (by decide) headEnough
      let first := CompleteSegment.ofSafeDyadic head within.head owner depth
        diameter positive safe
      let rest := CertifiedDyadic.totalCachedAt depth diameter
        positive tail within.tail first.finishOwner tailEnough
      exact
        { within := within
          prepared := .cons head tail owner within.head first rest.prepared
          generated := ⟨CompleteSegment.ofSafeDyadic_requests head within.head owner depth diameter positive safe,
            rest.generated⟩
          prepared_allEdgesProper := ⟨by
            rw [CompleteSegment.ofSafeDyadic_parameterEdges]
            exact dyadicEdges_strictParameterEdges depth
              zeroEndpoint oneEndpoint (by
              decide),
            rest.prepared_allEdgesProper⟩
          prepared_stepCount := by
            change first.subdivision.stepCount + rest.prepared.stepCount = _
            rw [rest.prepared_stepCount, CompleteSegment.ofSafeDyadic_stepCount]
            dsimp only [Geometry.ClearPath.segmentCount]
            rw [Multiplication.left_distrib, Nat.mul_one]
            exact Nat.add_comm _ _
          prepared_toClearPath := by
            change first.clearPath.append rest.prepared.toClearPath = _
            rw [rest.prepared_toClearPath, CompleteSegment.ofSafeDyadic_clearPath]
            rfl }

end CertifiedDyadic

end Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
