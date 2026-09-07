import CCL.Knot.BraidInvariance
import CCL.Knot.PowerTorusBridge

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

namespace CCL.Knot.PolynomialBraid

open CCL.Knot.FiniteBraid
open CCL.Knot.ProjectedCrossings
open CCL.Knot.BraidInvariance

abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame

/-- All finite chamber frames visited by a projected path, including both
endpoints. -/
def chamberFrames {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → List ChamberFrame
  | _, _, .nil frame => [frame.chamber]
  | _, _, .cons (start := start) _ remaining =>
      start.chamber :: chamberFrames remaining

/-- Exact monic Gaussian-rational coefficient polynomials at every displayed
subdivision vertex. -/
def coefficientVertices {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) : List GaussianPolynomial :=
  (chamberFrames path).map CCL.FiniteMonodromy.ChamberFrame.polynomial

@[simp] theorem chamberFrames_length {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    (chamberFrames path).length = path.stepCount + 1 := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [chamberFrames, List.length_cons,
        CCL.Knot.ProjectedCrossings.ProjectedPath.stepCount,
        inductionHypothesis]

@[simp] theorem coefficientVertices_length {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    (coefficientVertices path).length = path.stepCount + 1 := by
  simp only [coefficientVertices, List.length_map, chamberFrames_length]

/-- A closed, finitely subdivided, projection-certified rational polynomial
loop based at one displayed projected chamber frame. -/
structure AdmissibleLoop {strands : Nat} (base : ProjectedFrame strands) where
  path : ProjectedPath base base

namespace AdmissibleLoop

def word {strands : Nat} {base : ProjectedFrame strands}
    (loop : AdmissibleLoop base) : Word strands :=
  loop.path.word

def closure {strands : Nat} {base : ProjectedFrame strands}
    (loop : AdmissibleLoop base) : Closure where
  strands := strands
  word := loop.word

def identity {strands : Nat} (base : ProjectedFrame strands) :
    AdmissibleLoop base where
  path := .nil base

def reverse {strands : Nat} {base : ProjectedFrame strands}
    (loop : AdmissibleLoop base) : AdmissibleLoop base where
  path := loop.path.reverse

@[simp] theorem identity_word {strands : Nat}
    (base : ProjectedFrame strands) : (identity base).word = [] := rfl

@[simp] theorem reverse_word {strands : Nat}
    {base : ProjectedFrame strands} (loop : AdmissibleLoop base) :
    loop.reverse.word = loop.word.inverse :=
  ProjectedPath.word_reverse loop.path

def coefficientVertices {strands : Nat} {base : ProjectedFrame strands}
    (loop : AdmissibleLoop base) : List GaussianPolynomial :=
  CCL.Knot.PolynomialBraid.coefficientVertices loop.path

@[simp] theorem coefficientVertices_length {strands : Nat}
    {base : ProjectedFrame strands} (loop : AdmissibleLoop base) :
    loop.coefficientVertices.length = loop.path.stepCount + 1 :=
  CCL.Knot.PolynomialBraid.coefficientVertices_length loop.path

/-- Headline finite polynomial-loop braid theorem.  The existential witness
is the directly evaluated word, and its equation is the previously proved
finite extraction calculation. -/
theorem yieldsCertifiedBraid {strands : Nat}
    {base : ProjectedFrame strands} (loop : AdmissibleLoop base) :
    ∃ word : Word strands,
      ∀ position : Fin strands,
        loop.path.chamberPath.monodromy.forward
            (base.ownerIndex position) =
          base.ownerIndex (word.permutation.forward position) :=
  ⟨loop.word, loop.path.transport_agrees⟩

theorem closure_isKnot_of_monodromy_isSingleCycle {strands : Nat}
    {base : ProjectedFrame strands} (loop : AdmissibleLoop base)
    (single : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      loop.path.chamberPath.monodromy) : loop.closure.IsKnot :=
  loop.path.closure_isKnot_of_monodromy_isSingleCycle base single

/-- Concatenation of closed coefficient loops. -/
def append {strands : Nat} {base : ProjectedFrame strands}
    (first second : AdmissibleLoop base) : AdmissibleLoop base where
  path := first.path.append second.path

@[simp] theorem append_word {strands : Nat}
    {base : ProjectedFrame strands} (first second : AdmissibleLoop base) :
    (first.append second).word = first.word ++ second.word := by
  exact ProjectedPath.word_append first.path second.path

end AdmissibleLoop

/-! ## Refinement and finite homotopy -/

/-- A loopwise application of the operational subdivision relation. -/
structure LoopRefinement {strands : Nat}
    {base : ProjectedFrame strands}
    (coarse fine : AdmissibleLoop base) where
  pathRefinement : Refinement coarse.path fine.path

namespace LoopRefinement

theorem word_eq {strands : Nat}
    {base : ProjectedFrame strands} {coarse fine : AdmissibleLoop base}
    (refinement : LoopRefinement coarse fine) : coarse.word = fine.word := by
  exact refinement.pathRefinement.word_eq

end LoopRefinement

/-- Finite admissible homotopy certificates are generated by operational
subdivision and by a displayed finite Artin-equivalence proof between two
certified projected loops.  Symmetry and transitivity retain the actual
finite proof chain. -/
inductive Homotopic {strands : Nat} {base : ProjectedFrame strands} :
    AdmissibleLoop base → AdmissibleLoop base → Prop
  | refinement {coarse fine : AdmissibleLoop base}
      (certificate : LoopRefinement coarse fine) : Homotopic coarse fine
  | artin {left right : AdmissibleLoop base}
      (relation : BraidClassSame left.path right.path) : Homotopic left right
  | refl (loop : AdmissibleLoop base) : Homotopic loop loop
  | symm {left right : AdmissibleLoop base}
      (homotopy : Homotopic left right) : Homotopic right left
  | trans {first second third : AdmissibleLoop base}
      (firstSecond : Homotopic first second)
      (secondThird : Homotopic second third) : Homotopic first third

namespace Homotopic

/-- A certified loop followed by its explicitly reversed rational path
contracts by the finite sequence of adjacent cancellation moves. -/
theorem append_reverse {strands : Nat} {base : ProjectedFrame strands}
    (loop : AdmissibleLoop base) :
    Homotopic (loop.append loop.reverse) (AdmissibleLoop.identity base) := by
  apply Homotopic.artin
  unfold BraidClassSame
  change CCL.Knot.ArtinRelations.Equivalent
    (loop.append loop.reverse).word (AdmissibleLoop.identity base).word
  rw [AdmissibleLoop.append_word, AdmissibleLoop.reverse_word,
    AdmissibleLoop.identity_word]
  exact CCL.Knot.ArtinRelations.Equivalent.append_inverse loop.word

theorem ofRewrite {strands : Nat} {base : ProjectedFrame strands}
    {left right : AdmissibleLoop base}
    (rewrite : CCL.Knot.ArtinRelations.Rewrite left.word right.word) :
    Homotopic left right :=
  .artin (.step rewrite)

/-- A certified polynomial path followed by the oppositely signed crossing
admits the finite cancellation homotopy. -/
theorem cancellation {strands : Nat} {base : ProjectedFrame strands}
    {left right : AdmissibleLoop base}
    (before after : Word strands) (generator : Generator strands)
    (leftWord : left.word =
      before ++ [generator, generator.reverse] ++ after)
    (rightWord : right.word = before ++ after) : Homotopic left right := by
  apply ofRewrite
  rw [leftWord, rightWord]
  exact CCL.Knot.ArtinRelations.Rewrite.cancel before after generator

/-- Crossings supported on disjoint pairs are exchanged by a finite
far-commutation homotopy. -/
theorem farCommutation {strands : Nat} {base : ProjectedFrame strands}
    {left right : AdmissibleLoop base}
    (before after : Word strands) (first second : Generator strands)
    (separated : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val)
    (leftWord : left.word = before ++ [first, second] ++ after)
    (rightWord : right.word = before ++ [second, first] ++ after) :
    Homotopic left right := by
  apply ofRewrite
  rw [leftWord, rightWord]
  exact CCL.Knot.ArtinRelations.Rewrite.far
    before after first second separated

/-- The standard three-strand Artin relation is a finite admissible
polynomial-loop homotopy whenever the two displayed certified loop rows have
the corresponding boundary words. -/
theorem artinRelation {strands : Nat} {base : ProjectedFrame strands}
    {left right : AdmissibleLoop base}
    (before after : Word strands) (index : Fin (strands - 2))
    (sign : CrossingSign)
    (leftWord : left.word =
      before ++
        [CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign] ++ after)
    (rightWord : right.word =
      before ++
        [CCL.Knot.ArtinRelations.Generator.upper index sign,
          CCL.Knot.ArtinRelations.Generator.lower index sign,
          CCL.Knot.ArtinRelations.Generator.upper index sign] ++ after) :
    Homotopic left right := by
  apply ofRewrite
  rw [leftWord, rightWord]
  exact CCL.Knot.ArtinRelations.Rewrite.artin before after index sign

/-- Certified finite homotopies preserve the extracted Artin braid class. -/
theorem braidClassSame {strands : Nat}
    {base : ProjectedFrame strands} {left right : AdmissibleLoop base}
    (homotopy : Homotopic left right) :
    CCL.Knot.ArtinRelations.Equivalent left.word right.word := by
  induction homotopy with
  | refinement certificate =>
      rw [certificate.word_eq]
      exact .refl _
  | artin relation => exact relation
  | refl loop => exact .refl _
  | symm homotopy inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

theorem writhe_eq {strands : Nat}
    {base : ProjectedFrame strands} {left right : AdmissibleLoop base}
    (homotopy : Homotopic left right) :
    left.word.writhe = right.word.writhe :=
  homotopy.braidClassSame.writhe_eq

/-- Concatenation respects finite admissible homotopy. -/
theorem append {strands : Nat}
    {base : ProjectedFrame strands}
    {firstLeft firstRight secondLeft secondRight : AdmissibleLoop base}
    (first : Homotopic firstLeft firstRight)
    (second : Homotopic secondLeft secondRight) :
    CCL.Knot.ArtinRelations.Equivalent
      (firstLeft.append secondLeft).word
      (firstRight.append secondRight).word := by
  rw [AdmissibleLoop.append_word, AdmissibleLoop.append_word]
  exact CCL.Knot.ArtinRelations.Equivalent.append
    first.braidClassSame second.braidClassSame

end Homotopic

end CCL.Knot.PolynomialBraid
