module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Split
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational.Factorization

set_option genInjectivity false in
/-- One squarefree factor together with its displayed cofactor in the source
factor and its exact equality/apart relation to every condition already
processed.

The original factor, cofactor and ordered condition relations retain their exact source factorization and condition
readback. -/
structure ConditionProfile (source : Dense.Rational.Squarefree.Factor) (conditions : List
  BoundaryFactorization.CoefficientPolynomial)
    where
  /-- The retained normalized squarefree factor. -/ factor : Dense.Rational.Squarefree.Factor
  /-- The displayed cofactor in the original source factor. -/ cofactor : BoundaryFactorization.CoefficientPolynomial
  /-- The source factor is the product of the retained factor and cofactor. -/ factorization :
    Factorization source.polynomial factor.polynomial cofactor
  /-- Exact equality or coprimality evidence for each processed condition, retaining the condition itself. -/ relations
    : List (Sigma fun condition : BoundaryFactorization.CoefficientPolynomial =>
    Dense.Rational.Factorization.ConditionRelation condition factor)
  /-- The relation entries list exactly the original ordered conditions. -/ conditions_eq : relations.map Sigma.fst =
    conditions

constructive_injectivity ConditionProfile

namespace ConditionProfile

/-- Descend an existing profile through one newly computed condition piece,
and prepend the new condition relation.

The same computed condition piece refines the retained source factorization and prepends its relation before descending
the original remaining relations. -/
@[expose] def extendPiece
    {source : Dense.Rational.Squarefree.Factor} {conditions : List BoundaryFactorization.CoefficientPolynomial}
    (profile : Dense.Rational.Factorization.ConditionProfile source conditions)
    (condition : BoundaryFactorization.CoefficientPolynomial)
    (piece : Dense.Rational.Factorization.ConditionPiece profile.factor condition) :
    Dense.Rational.Factorization.ConditionProfile source (condition :: conditions) where
  factor := piece.factor
  cofactor := piece.cofactor * profile.cofactor
  factorization := by
    apply Dense.Rational.Factorization.factorizationOfEvals
    intro point
    rw [Dense.Rational.Factorization.eval_factorization profile.factorization point,
      Dense.Rational.Factorization.eval_factorization piece.factorization point, Dense.Basic.DensePolynomial.eval_mul]
    ring1
  relations := ⟨condition, piece.relation⟩ ::
    profile.relations.map fun entry =>
      ⟨entry.1, entry.2.descend piece⟩
  conditions_eq := by
    have mapped :
        (profile.relations.map fun entry =>
          (⟨entry.1, entry.2.descend piece⟩ :
            Sigma fun queried : BoundaryFactorization.CoefficientPolynomial =>
              Dense.Rational.Factorization.ConditionRelation queried piece.factor)).map Sigma.fst =
          profile.relations.map Sigma.fst := by
      induction profile.relations with
      | nil => rfl
      | cons entry remaining inductionHypothesis =>
          simp only [List.map_cons]
          exact congrArg (List.cons entry.1) inductionHypothesis
    simp only [List.map_cons]
    rw [mapped, profile.conditions_eq]

/-- Split one profile against the next condition.

The original gcd split is computed once, and its ordered pieces become profiles with the same source owner. -/
@[expose] def extend
    {source : Dense.Rational.Squarefree.Factor} {conditions : List BoundaryFactorization.CoefficientPolynomial}
    (profile : Dense.Rational.Factorization.ConditionProfile source conditions)
    (condition : BoundaryFactorization.CoefficientPolynomial) :
    List (Dense.Rational.Factorization.ConditionProfile source (condition :: conditions)) :=
  let partition := Dense.Rational.Factorization.splitAgainstCondition profile.factor condition
  partition.pieces.map fun piece => profile.extendPiece condition piece

/-- Splitting a retained condition profile against another condition produces at least one profile.

The computed condition partition retains at least one piece; mapping the original profile extension preserves that
nonempty list. -/
theorem extend_nonempty
    {source : Dense.Rational.Squarefree.Factor} {conditions : List BoundaryFactorization.CoefficientPolynomial}
    (profile : Dense.Rational.Factorization.ConditionProfile source conditions)
    (condition : BoundaryFactorization.CoefficientPolynomial) : profile.extend condition ≠ [] := by
  let partition := Dense.Rational.Factorization.splitAgainstCondition profile.factor condition
  intro empty
  have piecesEmpty : partition.pieces = [] := by
    have mappedEmpty : partition.pieces.map
        (fun piece => profile.extendPiece condition piece) = [] := empty
    cases pieces : partition.pieces with
    | nil => rfl
    | cons head tail =>
        rw [pieces] at mappedEmpty
        cases mappedEmpty
  exact partition.nonempty piecesEmpty

/-- The extended profiles cover exactly the roots of the original profile factor.

Both directions retain the original condition-partition piece and its membership witness, preserving exactly the
rational root set. -/
theorem extend_rootCoverage
    {source : Dense.Rational.Squarefree.Factor} {conditions : List BoundaryFactorization.CoefficientPolynomial}
    (profile : Dense.Rational.Factorization.ConditionProfile source conditions)
    (condition : BoundaryFactorization.CoefficientPolynomial) (point : Fraction.Rational) :
    profile.factor.polynomial.eval point = 0 ↔
      ∃ next ∈ profile.extend condition,
        next.factor.polynomial.eval point = 0 := by
  let partition := Dense.Rational.Factorization.splitAgainstCondition profile.factor condition
  constructor
  · intro profileZero
    rcases (partition.rootCoverage point).mp profileZero with
      ⟨piece, pieceMember, pieceZero⟩
    refine ⟨profile.extendPiece condition piece, ?_, ?_⟩
    · exact Data.List.Map.mem_map.mpr ⟨piece, pieceMember, rfl⟩
    · exact pieceZero
  · rintro ⟨next, nextMember, nextZero⟩
    have mappedMember : next ∈ partition.pieces.map
        (fun piece => profile.extendPiece condition piece) := nextMember
    rcases Data.List.Map.mem_map.mp mappedMember with ⟨piece, pieceMember, nextEq⟩
    subst next
    exact (partition.rootCoverage point).mpr ⟨piece, pieceMember, nextZero⟩

end ConditionProfile

set_option genInjectivity false in
/-- Complete finite profile family after processing a displayed list of
conditions.

The retained nonempty family carries the original factor and condition indices and covers exactly that factor's rational
roots. -/
structure ConditionProfiles (factor : Dense.Rational.Squarefree.Factor) (conditions : List
  BoundaryFactorization.CoefficientPolynomial)
    where
  /-- The finite family of refined factors and their condition relations. -/ profiles : List
    (Dense.Rational.Factorization.ConditionProfile factor conditions)
  /-- The retained profile family is nonempty. -/ nonempty : profiles ≠ []
  /-- The family covers exactly the rational roots of the original squarefree factor. -/ rootCoverage : ∀ point :
    Fraction.Rational,
    factor.polynomial.eval point = 0 ↔
      ∃ profile ∈ profiles, profile.factor.polynomial.eval point = 0

constructive_injectivity ConditionProfiles

/-- Repeated executable gcd splitting.  Every final squarefree piece is
classified as equality-owned or explicitly coprime for every input
condition, and the finite family has exactly the original roots.

The original finite recursion splits each retained prior factor against the next condition, preserving its ordered
profiles and source-root coverage. -/
@[expose] def classifyConditions (factor : Dense.Rational.Squarefree.Factor) :
    (conditions : List BoundaryFactorization.CoefficientPolynomial) → Dense.Rational.Factorization.ConditionProfiles
      factor
      conditions
  | [] => by
      let baseProfile : Dense.Rational.Factorization.ConditionProfile factor [] :=
        { factor := factor
          cofactor := Dense.Basic.DensePolynomial.constant 1
          factorization := by
            apply Dense.Rational.Factorization.factorizationOfEvals
            intro point
            simp only [Dense.Basic.DensePolynomial.eval_constant,
              Fraction.Field.mul_one_direct, -eq_self, -iff_self]
            rfl
          relations := []
          conditions_eq := rfl }
      exact
        { profiles := [baseProfile]
          nonempty := List.cons_ne_nil _ _
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              exact ⟨baseProfile, List.mem_cons_self, factorZero⟩
            · rintro ⟨profile, member, profileZero⟩
              have equal : profile = baseProfile :=
                Data.List.Membership.mem_singleton.mp member
              subst profile
              exact profileZero }
  | condition :: remaining => by
      let prior := Purelib.Polynomial.Dense.Rational.Factorization.classifyConditions factor remaining
      let profiles := prior.profiles.flatMap fun profile =>
        profile.extend condition
      have profilesNonempty : profiles ≠ [] := by
        cases priorProfilesEq : prior.profiles with
        | nil => exact (prior.nonempty priorProfilesEq).elim
        | cons profile otherProfiles =>
            cases extensionEq : profile.extend condition with
            | nil =>
                exact (profile.extend_nonempty condition extensionEq).elim
            | cons next otherExtensions =>
                intro empty
                have profileMember : profile ∈ prior.profiles := by
                  rw [priorProfilesEq]
                  exact List.mem_cons_self
                have nextMember : next ∈ profile.extend condition := by
                  rw [extensionEq]
                  exact List.mem_cons_self
                have flattenedMember : next ∈ profiles :=
                  Data.List.Flatten.mem_flatMap.mpr
                    ⟨profile, profileMember, nextMember⟩
                rw [empty] at flattenedMember
                exact List.not_mem_nil flattenedMember
      exact
        { profiles := profiles
          nonempty := profilesNonempty
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              rcases (prior.rootCoverage point).mp factorZero with
                ⟨profile, profileMember, profileZero⟩
              rcases (profile.extend_rootCoverage condition point).mp
                  profileZero with ⟨next, nextMember, nextZero⟩
              exact ⟨next,
                Data.List.Flatten.mem_flatMap.mpr
                  ⟨profile, profileMember, nextMember⟩,
                nextZero⟩
            · rintro ⟨next, nextMember, nextZero⟩
              dsimp only [profiles] at nextMember
              rcases Data.List.Flatten.mem_flatMap.mp nextMember with
                ⟨profile, profileMember, nextMember⟩
              have profileZero :=
                (profile.extend_rootCoverage condition point).mpr
                  ⟨next, nextMember, nextZero⟩
              exact (prior.rootCoverage point).mpr
                ⟨profile, profileMember, profileZero⟩ }
end Purelib.Polynomial.Dense.Rational.Factorization

end
