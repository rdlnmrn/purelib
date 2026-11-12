module

import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.OfFn.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
meta import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
meta import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
meta import Purelib.RootIsolation.Residual.Multiplicity
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws

/-! # Same-index coherent root caches of original multiplicity preparations -/

namespace TestPurelib.Riemann.MultiplicityRootCache

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis
open Purelib.Approximation.Rational
open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.Data.Gaussian

example {head : PositiveEntry} {tail : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor head} {remaining : Residual.Multiplicity.Family tail}
    (root : CoherentRoot.Multiplicity.Realization factor) (tailRoots : CoherentRoot.Multiplicity.Family remaining) :
    (CoherentRoot.Multiplicity.Family.cons root tailRoots).get 0 = root :=
  CoherentRoot.Multiplicity.Family.get_head root tailRoots

example {head : PositiveEntry} {tail : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor head} {remaining : Residual.Multiplicity.Family tail}
    (root : CoherentRoot.Multiplicity.Realization factor) (tailRoots : CoherentRoot.Multiplicity.Family remaining)
    (index : Fin tail.length) :
    (CoherentRoot.Multiplicity.Family.cons root tailRoots).get index.succ = tailRoots.get index :=
  CoherentRoot.Multiplicity.Family.get_tail root tailRoots index

example {entries : List PositiveEntry} (preparation : Residual.Multiplicity.Family entries)
    (index : Fin (CoherentRoot.Multiplicity.size preparation)) :
    (Multiplicity.Index.ofFin preparation index).toFin = index :=
  Multiplicity.Index.toFin_ofFin preparation index

example {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (index : Multiplicity.Index preparation) :
    Multiplicity.Index.ofFin preparation index.toFin = index :=
  Multiplicity.Index.ofFin_toFin index

example {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : CoherentRoot.Multiplicity.Family preparation) (factorIndex : Fin entries.length)
    (rootIndex : Fin (CoherentRoot.Multiplicity.count (preparation.get factorIndex))) :
    roots.candidates (Multiplicity.Index.fromFactor preparation factorIndex rootIndex).toFin =
      (roots.get factorIndex).approximation rootIndex :=
  roots.candidates_fromFactor factorIndex rootIndex

/-- The same source 4(Z-2)² supplies the original retained factor cache. -/
private def repeated : CoherentRoot.GaussianPolynomial := ⟨[4, -16, 16]⟩

/-- Execute actual same-index realization and repeated lookups without rerunning original decomposition or isolation. -/
private def checkCache : IO Unit := do
  let source := Approximation.Gaussian.Geometric.GeometricApproximation.exact 2
  let prepared := Polynomial.Approximation.Gaussian.Localization.Preparation.ofResidual repeated
    (by decide +kernel) source 0 (by decide +kernel) (by
      intro index
      change Norm.Basic.normSq (repeated.eval 2) ≤
        Geometric.Basic.quarterRadius 0 index
      rewrite [show repeated.eval 2 = 0 by decide +kernel, Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
  let roots := prepared.roots
  let observation := prepared.observe 0 (epsilon := (1 / 16 : Data.Rat.Fraction.Rational)) (by decide +kernel)
  let index := observation.localization.selected.index
  let factor := prepared.factors.factors.get index
  let realization := roots.get index
  let rootIndex := CoherentRoot.Multiplicity.firstIndex factor
  let first := realization.approximation rootIndex
  let second := observation.rootApproximation rootIndex
  let occurrence := Multiplicity.Index.fromFactor prepared.factors.factors index rootIndex
  let candidate := roots.candidates occurrence.toFin
  unless CoherentRoot.Multiplicity.size prepared.factors.factors = 1 ∧
      occurrence.toFin.val = 0 ∧ occurrence.factorIndex.val = index.val ∧
      occurrence.rootIndex.val = rootIndex.val ∧ candidate.sample 5 = 2 do
    throw (IO.userError "finite candidate lookup lost its original factor/root indices or actual cache")
  unless CoherentRoot.Multiplicity.count factor = 1 ∧ first.sample 0 = 2 ∧ second.sample 3 = 2 do
    throw (IO.userError "original exact factor root cache or same-index repeated lookup was changed")
  unless (prepared.factors.entries.get index).multiplicity = 2 do
    throw (IO.userError "original source multiplicity was replaced during root-cache realization")

#eval checkCache

/-- Two original multiplicity factors retain both exact root programs and the repeated source occurrence. -/
private def twoFactors : CoherentRoot.GaussianPolynomial := ⟨[1, -4, 4, 0]⟩

/-- Execute finite enumeration and all-later localization over two distinct retained original factor caches. -/
private def checkTwoFactorCoverage : IO Unit := do
  let source := Approximation.Gaussian.Geometric.GeometricApproximation.exact 2
  let prepared := Polynomial.Approximation.Gaussian.Localization.Preparation.ofResidual twoFactors
    (by decide +kernel) source 0 (by decide +kernel) (by
      intro index
      change Norm.Basic.normSq (twoFactors.eval 2) ≤
        Geometric.Basic.quarterRadius 0 index
      rewrite [show twoFactors.eval 2 = 0 by decide +kernel, Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
  let roots := prepared.roots
  let readings := List.ofFn (fun index : Fin (CoherentRoot.Multiplicity.size prepared.factors.factors) =>
    (roots.candidates index).sample 0)
  unless readings.length = 2 ∧ readings.contains 0 ∧ readings.contains 2 do
    throw (IO.userError "candidate enumeration omitted an original factor root")
  let selected := prepared.select
  unless selected.decide.isPrepared do
    throw (IO.userError "the original selected nonzero factor root was not prepared")
  let comparison := selected.equivalent.compare 4 6 (1 / 16 : Data.Rat.Fraction.Rational) (by decide +kernel)
  unless comparison.leftIndex ≥ 4 ∧ comparison.rightIndex ≥ 6 ∧
      selected.approximation.sample comparison.rightIndex = 2 ∧
      (prepared.factors.entries.get selected.occurrence.factorIndex).multiplicity = 2 do
    throw (IO.userError "stable selection lost original starts, result root or repeated-source multiplicity")
  if bound : 1 < CoherentRoot.Multiplicity.size prepared.factors.factors then
    let pair := selected.rootPairs.get ⟨0, Nat.lt_trans (by decide) bound⟩ ⟨1, bound⟩
    unless pair.leftIndex = 0 ∧ pair.rightIndex = 0 ∧ pair.gap > 0 do
      throw (IO.userError "the original exact factor pair lost its retained positive squared gap")
  else
    throw (IO.userError "the stored pair bank omitted an original factor-root index")
  let coverage := prepared.coverage
  let observation := coverage.prepare 3 (1 / 16 : Data.Rat.Fraction.Rational) (by decide +kernel)
  let nearby := observation.locate observation.index (Nat.le_refl _)
  let occurrence := Multiplicity.Index.ofFin prepared.factors.factors nearby.owner
  let originalEntry := prepared.factors.entries.get occurrence.factorIndex
  unless observation.index ≥ 3 ∧ (roots.candidates nearby.owner).sample nearby.index = 2 ∧
      originalEntry.multiplicity = 2 do
    throw (IO.userError "coverage lost its original start, selected root cache or source multiplicity")
  let later := observation.locate (observation.index + 4) (Nat.le_add_right _ _)
  unless (roots.candidates later.owner).sample (later.index + 2) = 2 do
    throw (IO.userError "all-later coverage failed to reuse the original cached factor root")

#eval checkTwoFactorCoverage

/-- Execute stable zero selection and its certified exclusion on the same original two-factor polynomial. -/
private def checkZeroSelection : IO Unit := do
  let source := Approximation.Gaussian.Geometric.GeometricApproximation.exact 0
  let prepared := Polynomial.Approximation.Gaussian.Localization.Preparation.ofResidual twoFactors
    (by decide +kernel) source 0 (by decide +kernel) (by
      intro index
      change Norm.Basic.normSq (twoFactors.eval 0) ≤
        Geometric.Basic.quarterRadius 0 index
      rewrite [show twoFactors.eval 0 = 0 by decide +kernel, Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index)
  let selected := prepared.select
  unless selected.approximation.sample 7 = 0 ∧ !selected.decide.isPrepared ∧
      (prepared.factors.entries.get selected.occurrence.factorIndex).multiplicity = 1 do
    throw (IO.userError "stable zero decision lost its actual cached branch or original source multiplicity")

#eval checkZeroSelection

/-- Prepare the same two-factor source outside the measured pair and anchor actions. -/
@[noinline, nospecialize] private def withPreparedFactors
    (observe : Localization.Preparation twoFactors (Geometric.GeometricApproximation.exact 2) → IO Unit) :
    IO Unit :=
  observe (Localization.Preparation.ofResidual twoFactors (by decide +kernel)
    (Geometric.GeometricApproximation.exact 2) 0 (by decide +kernel) (by
      intro index
      change Norm.Basic.normSq (twoFactors.eval 2) ≤
        Geometric.Basic.quarterRadius 0 index
      rewrite [show twoFactors.eval 2 = 0 by decide +kernel, Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index))

/-- Retain the same original ordered factor certificates before measuring root separation. -/
@[noinline, nospecialize] private def withFactorPairs {source : Geometric.GeometricApproximation}
    (prepared : Localization.Preparation twoFactors source)
    (observe : Positive.CoprimePairs prepared.factors.entries → IO Unit) : IO Unit :=
  have pairwise : prepared.factors.entries.Pairwise fun left right =>
      Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation left.part right.part := by
    rewrite [prepared.factors.entries_eq]
    exact prepared.decomposition.positiveMultiplicityEntries_pairwise
  observe (Positive.CoprimePairs.ofPairwise prepared.factors.entries pairwise)

/-- Construct the actual root-pair bank inside its timed IO continuation. -/
@[noinline, nospecialize] private def withRootPairs {source : Geometric.GeometricApproximation}
    (prepared : Localization.Preparation twoFactors source)
    (factorPairs : Positive.CoprimePairs prepared.factors.entries)
    (observe : Sequence.Selection.Pairs prepared.roots.candidates → IO Unit) : IO Unit :=
  observe (prepared.roots.pairs factorPairs)

/-- Identify the actual source occurrence using the same retained pair bank and coverage. -/
@[noinline, nospecialize] private def withAnchor {source : Geometric.GeometricApproximation}
    (prepared : Localization.Preparation twoFactors source)
    (pairs : Sequence.Selection.Pairs prepared.roots.candidates)
    (observe : Sequence.Selection.Anchor prepared.source.toApproximation pairs.separated → IO Unit) : IO Unit :=
  observe (Sequence.Selection.Anchor.ofCoverage prepared.source.toApproximation pairs.separated prepared.coverage)

/-- Measure finite pair separation and source identification on the same two original linear-factor caches.

Preparation and ordered factor Bézout data are retained before either timer.
Each interval includes construction and forcing its complete finite readbacks;
these in-memory observations claim no nonlinear isolation or deep-request cost.
-/
private def measureTwoFactorPhases : IO Unit :=
  withPreparedFactors fun prepared =>
    withFactorPairs prepared fun factorPairs => do
      let factors := List.ofFn (fun index : Fin prepared.factors.entries.length => index)
      let mut certificateCount := 0
      for first in factors do
        for second in factors do
          match factorPairs.get first second with
          | .same _ => pure ()
          | .coprime certificate =>
              unless certificate.result.gcd.natDegree = 0 ∧ certificate.result.left.natDegree = 0 ∧
                  certificate.result.right.natDegree = 0 do
                throw (IO.userError "the original linear-factor Bezout data changed")
              certificateCount := certificateCount + 1
      unless factors.length = 2 ∧ certificateCount = 2 do
        throw (IO.userError "the finite phase fixture lost its two original factors")
      let started ← IO.monoNanosNow
      withRootPairs prepared factorPairs fun pairs => do
        let candidates := List.ofFn (fun index : Fin (CoherentRoot.Multiplicity.size prepared.factors.factors) => index)
        let mut pairCount := 0
        for first in candidates do
          for second in candidates do
            let pair := pairs.get first second
            unless pair.leftIndex = 0 ∧ pair.rightIndex = 0 ∧ pair.gap = (if first = second then 1 else 4) do
              throw (IO.userError "the finite phase fixture changed an original pair entry")
            pairCount := pairCount + 1
        unless pairCount = 4 ∧ pairs.start = 0 ∧ pairs.gap = 1 do
          throw (IO.userError "the finite phase fixture changed its original pair summaries")
        let separated ← IO.monoNanosNow
        withAnchor prepared pairs fun anchor => do
          let occurrence := Multiplicity.Index.ofFin prepared.factors.factors anchor.nearby.owner
          let sourceReading := prepared.source.sample anchor.index
          let candidateReading := (prepared.roots.candidates anchor.nearby.owner).sample anchor.nearby.index
          let multiplicity := (prepared.factors.entries.get occurrence.factorIndex).multiplicity
          unless prepared.source.toApproximation.radiusSq anchor.index < pairs.gap / 16 ∧
              sourceReading = 2 ∧ candidateReading = sourceReading ∧ multiplicity = 2 do
            throw (IO.userError "the finite phase fixture lost the original source, candidate or multiplicity")
          let identified ← IO.monoNanosNow
          IO.print s!"two-linear-factor phases: factors=2 candidates=2 pair_entries={pairCount} \
            separation_ns={separated - started} identification_ns={identified - separated}; \
            pair_start={pairs.start} pair_gap=1 source_index={anchor.index} \
            candidate_owner={anchor.nearby.owner.val} candidate_index={anchor.nearby.index} \
            source=2 candidate=2 multiplicity={multiplicity}; retained original caches checked\n"

#eval measureTwoFactorPhases

end TestPurelib.Riemann.MultiplicityRootCache
