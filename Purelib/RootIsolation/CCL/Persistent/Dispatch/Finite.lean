module
import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Data.List.Erase

import Purelib.Data.List.Map
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.BoxSign.Cache

import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Boundary.Finite
public import Purelib.RootIsolation.CCL.Persistent.Boundary.Inspection
import Purelib.RootIsolation.CCL.Persistent.Controller.Basic
public import Purelib.RootIsolation.CCL.Persistent.Dispatch.Basic
import Purelib.RootIsolation.CCL.Persistent.Next.Strict
import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.CCL.Persistent.State.Basic
import Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Decision
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Inspection
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare (SourcePersistentDispatchPreparedAlias)

public section

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Dispatch.Finite

/-- Every atom form that can occur in either local child formula at a fixed
raw prefix.  The list deliberately retains duplicates: erasing the first
occurrence of a newly resolved form still gives a strict natural measure,
and the cache prevents that form from being returned again. -/
@[expose] def candidateForms (word : List Bool) : List
  Geometry.Projective.Hermitian.HermitianForm :=
  let parser := Data.CCL.Encoding.Parser.State.parse word
  (((Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula parser false).atoms ++
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula parser true).atoms).map
      fun atom => atom.form)

/-- Every atom of either original child formula has its form in the retained candidate multiset. -/
theorem form_mem_candidateForms
    (word : List Bool) (bit : Bool)
    {atom : Atom}
    (member : atom ∈
      (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
        (Data.CCL.Encoding.Parser.State.parse word) bit).atoms) :
    atom.form ∈ candidateForms word := by
  apply Data.List.Map.mem_map.mpr
  refine ⟨atom, ?_, rfl⟩
  cases bit with
  | false => exact List.mem_append_left _ member
  | true => exact List.mem_append_right _ member

/-- Lift a prepared state's stable one-bit result back through all same-prefix
finite-boundary refinements to the dispatcher input. -/
@[expose] def liftStable
    {p : CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (prepared :
      SourcePersistentDispatchPreparedAlias current)
    (stable : CCL.Persistent.Next.Strict.StableNext prepared.state) :
    CCL.Persistent.Controller.Basic.SourcePersistentDispatchStepResultAlias current :=
  .next stable.bit stable.state prepared.boxRefines (by
    rw [CCL.Persistent.Next.Strict.StableNext.state_word,
      prepared.word_eq])

/-- The exact dependent input tuple for finite boundary dispatch.

It retains the prepared same-word state, positive denominator certificate, unresolved form multiset, sign cache and
complete coverage of both original child formulas. -/
-- The explicit dependent tuple already used by the finite recursion compiler.
@[expose] def FiniteDispatchInput {p :
  CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) :=
  PSigma fun prepared : SourcePersistentDispatchPreparedAlias current =>
  PSigma fun _denominator : CCL.Persistent.Dispatch.Basic.DenominatorCertificate prepared =>
  PSigma fun unresolved : List Geometry.Projective.Hermitian.HermitianForm =>
  PSigma fun overrides : List (Geometry.Projective.Hermitian.Formula.Box.FormOverride prepared.state.numerical.box) =>
  ∀ (bit : Bool) (atom : Atom),
      atom ∈ (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
        (Data.CCL.Encoding.Parser.State.parse prepared.state.word) bit).atoms →
      atom.form ∈ unresolved ∨
        Geometry.Projective.Hermitian.Formula.Box.findFormOverride
          overrides atom.form ≠ none

/-- Resolve the retained finite boundary forms until a step is decided or a genuine curve boundary remains.

Each positive finite resolution refines the original state, preserves its word and denominator margin, adds the actual
form certificate to the cache and erases one unresolved occurrence. -/
@[expose] def dispatchFinite
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient)
    {current : State p ambient}
    (input : FiniteDispatchInput current) :
    CCL.Persistent.Dispatch.Basic.Outcome current := by
  rcases input with ⟨prepared, denominator, unresolved, overrides, covered⟩
  match CCL.Persistent.Boundary.inspectNextWith prepared.state
      denominator.margin denominator.margin_pos overrides with
  | .terminal terminal =>
      have impossible : False := by
        rcases prepared.canContinue prepared.state.currentSample with
          ⟨bit, canStep⟩
        exact terminal.none bit canStep
      exact impossible.elim
  | .stable stable => exact .decided (liftStable prepared stable)
  | .boundary next notResolved remaining =>
      cases remaining with
      | curve source analyses analysesEq =>
          exact .boundary prepared denominator next
            { source := source
              analyses := analyses
              analyses_eq := analysesEq }
      | finite points complete nonnegative _evaluations _evaluationsEq =>
          have atomUnresolved : next.atom.form ∈ unresolved := by
            rcases covered next.bit next.atom next.member with member | found
            · exact member
            · exact (found notResolved).elim
          match CCL.Persistent.Boundary.resolve degreePositive
              track prepared.state next.atom points complete nonnegative with
          | .exact root =>
              exact .decided (.exact
                { point := root.point
                  root := root.root
                  inside := prepared.boxRefines.contains root.inside })
          | .positive state boxRefines wordEq stability formEq =>
              let nextPrepared : SourcePersistentDispatchPreparedAlias current :=
                { state := state
                  boxRefines := boxRefines.trans prepared.boxRefines
                  word_eq := wordEq.trans prepared.word_eq
                  canContinue := fun sample => by
                    let priorSample :
                        CCL.Persistent.Sample.Basic.CompatibleSample
                          prepared.state.word prepared.state.numerical.box :=
                      { point := sample.point
                        inside := boxRefines.contains sample.inside
                        nonzero := sample.nonzero
                        represented := by
                          simpa only [wordEq, -eq_self, -iff_self] using sample.represented }
                    rcases prepared.canContinue priorSample with
                      ⟨bit, canStep⟩
                    exact ⟨bit, by simpa only [wordEq, -eq_self, -iff_self] using canStep⟩ }
              let refinedOverrides :=
                overrides.map fun override => override.refine boxRefines
              let nextOverrides : List
                  (Geometry.Projective.Hermitian.Formula.Box.FormOverride nextPrepared.state.numerical.box) :=
                stability :: refinedOverrides
              let nextUnresolved := Data.List.Erase.eraseForm next.atom.form unresolved
              have nextCovered : ∀ (bit : Bool)
                  (other : Atom),
                  other ∈
                    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
                      (Data.CCL.Encoding.Parser.State.parse
                        nextPrepared.state.word) bit).atoms →
                  other.form ∈ nextUnresolved ∨
                    Geometry.Projective.Hermitian.Formula.Box.findFormOverride
                      nextOverrides other.form ≠ none := by
                intro bit other member
                have sameWord : nextPrepared.state.word =
                    prepared.state.word := wordEq
                have priorMember : other ∈
                    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
                      (Data.CCL.Encoding.Parser.State.parse
                        prepared.state.word) bit).atoms := by
                  simpa only [sameWord, -eq_self, -iff_self] using member
                rcases covered bit other priorMember with candidate | found
                · by_cases equal : other.form = next.atom.form
                  · right
                    have headEqual : stability.form = other.form := by
                      rw [formEq]
                      exact equal.symm
                    change Geometry.Projective.Hermitian.Formula.Box.findFormOverride
                      (stability :: refinedOverrides) other.form ≠ none
                    rewrite [Geometry.Projective.Hermitian.Formula.Box.findFormOverride, dif_pos headEqual]
                    intro impossible
                    cases impossible
                  · left
                    exact Data.List.Erase.mem_eraseForm_of_ne equal candidate
                · right
                  exact Geometry.Projective.Hermitian.BoxSign.Cache.findFormOverride_cons_ne_none stability
                    refinedOverrides other.form
                    (Geometry.Projective.Hermitian.BoxSign.Cache.findFormOverride_refine_ne_none overrides boxRefines
                      other.form found)
              let nextDenominator : CCL.Persistent.Dispatch.Basic.DenominatorCertificate nextPrepared :=
                { margin := denominator.margin
                  margin_pos := denominator.margin_pos
                  lower := by
                    intro value inside
                    have lower := denominator.lower
                      (boxRefines.contains inside)
                    have sameWord : nextPrepared.state.word =
                        prepared.state.word := wordEq
                    simpa only [sameWord, -eq_self, -iff_self] using lower }
              exact dispatchFinite degreePositive track
                ⟨nextPrepared, nextDenominator, nextUnresolved, nextOverrides, nextCovered⟩
termination_by input.2.2.1.length
decreasing_by
  exact Data.List.Erase.length_eraseForm_lt atomUnresolved
end Purelib.RootIsolation.CCL.Persistent.Dispatch.Finite

end
