module

import Purelib.System.IO.Reference

import Purelib.Polynomial.Approximation.Gaussian.Localization
import Purelib.Polynomial.Approximation.Gaussian.Localization.Coverage
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.Approximation.Gaussian.Sequence.Selection
import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
import scripts.checkpoint.RootSelection
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Separation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.System.IO
meta import Purelib.Polynomial.Approximation.Gaussian.Localization
meta import Purelib.RootIsolation.Residual.Multiplicity
meta import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Approximation.Gaussian.Geometric

/-!
# Original multiplicity localization and finite refinement regression

A nonmonic repeated-root source retains a leading-zero representation. The
runtime requests share one preparation and original geometric sample cache.
Nonroot input localization and original factor multiplicity are checked too.
-/

namespace TestPurelib.Polynomial.RootLocalization

open Purelib
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial.Approximation.Gaussian.Localization
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.SquareRoot.Radius
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)

example {polynomial : CoefficientPolynomial} {source : GeometricApproximation}
    (preparation : Preparation polynomial source) (current : Nat) {epsilon : Rational}
    (positive : 0 < epsilon) : current ≤ (preparation.observe current positive).index :=
  (preparation.observe current positive).index_ge

example {polynomial : CoefficientPolynomial} {source : GeometricApproximation}
    (preparation : Preparation polynomial source) (current : Nat) {epsilon : Rational}
    (positive : 0 < epsilon) :
    (preparation.observe current positive).index ≤ current +
      (Nat.log2 (Data.Rat.Rounding.Floor.ceilNat
        (preparation.residualScale / (preparation.observe current positive).target)) + 1) :=
  (preparation.observe current positive).index_le

example {polynomial : CoefficientPolynomial} {source : GeometricApproximation}
    (preparation : Preparation polynomial source) (current : Nat) {epsilon : Rational}
    (positive : 0 < epsilon) :
    normSq (polynomial.normalize.eval (preparation.observe current positive).sample) <
      (preparation.observe current positive).target :=
  (preparation.observe current positive).residualSmall

/-- The same original source 4(Z-2)² with a representation-only leading zero. -/
private def repeated : CoefficientPolynomial := ⟨[0, 4, -16, 16]⟩

/-- Execute repeated-root localization, stored-factor reuse and bounded requests on the original sample program. -/
private def checkLocalization : IO Unit := do
  let source := GeometricApproximation.exact 2
  let preparation := Preparation.ofResidual repeated (by decide +kernel) source 1 (by decide +kernel) (by
    intro index
    change normSq (repeated.eval 2) ≤
      Basic.quarterRadius 1 index
    rewrite [show repeated.eval 2 = 0 by decide +kernel, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Basic.quarterRadius_nonneg (by decide +kernel) index)
  unless preparation.factors.entries.length = 1 ∧ preparation.factors.count = 2 do
    throw (IO.userError "original repeated factor or total source multiplicity was lost")
  let first := preparation.observe 0 (epsilon := (1 / 16 : Rational)) (by decide +kernel)
  let resumed := preparation.observe first.index (epsilon := (1 / 256 : Rational)) (by decide +kernel)
  let reused := preparation.observe resumed.index (epsilon := (1 / 256 : Rational)) (by decide +kernel)
  unless 0 < first.index ∧ first.index < resumed.index ∧ reused.index = resumed.index ∧
      first.sample = 2 ∧ resumed.sample = 2 do
    throw (IO.userError "same original sample or starting-stage preservation was lost")
  let later := resumed.localizeLater (by decide +kernel) (resumed.index + 3) (Nat.le_add_right _ _)
  unless later.selected.index = resumed.localization.selected.index do
    throw (IO.userError "later sample localization changed the retained original repeated-linear factor")
  let firstEntry := preparation.factors.entries.get first.localization.selected.index
  unless firstEntry.multiplicity = 2 ∧ firstEntry.part.polynomial.eval 2 = 0 do
    throw (IO.userError "selected factor no longer belongs to the original repeated-root source")
  match first.localization.localized.exact? with
  | some data =>
    unless data.point = 2 do
      throw (IO.userError "original exact linear factor root was changed")
  | none => throw (IO.userError "repeated linear factor unnecessarily entered nonlinear isolation")
  let nonroot := (2 : Data.Gaussian.Basic.Canonical) + (1 / 128 : Data.Gaussian.Basic.Canonical)
  let epsilon : Rational := 1 / 4
  if small : normSq (repeated.normalize.eval nonroot) < preparation.factors.threshold epsilon then
    let localized := preparation.factors.localize nonroot (by decide +kernel : 0 < epsilon) small
    unless nonroot ≠ 2 ∧ localized.selected.index = first.localization.selected.index do
      throw (IO.userError "nonroot localization failed to reuse the same original factor")
    match localized.localized.exact? with
    | some data =>
      unless normSq (nonroot - data.point) < epsilon ^ 2 do
        throw (IO.userError "original nonroot reading exceeded its certified localization radius")
    | none => throw (IO.userError "nonroot repeated-linear localization replaced the original factor cache")
  else
    throw (IO.userError "computed repeated-root threshold failed the concrete small-residual nonroot request")

#eval checkLocalization

/-- Retain the exact scalar sample while making each native evaluation visible. -/
@[never_extract, extern "lean_dbg_trace"] private def tracedSample
    (message : String) (work : Unit → Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical := work ()

/-- The original exact sample two, with a diagnostic at the actual sample call. -/
private def markedSource : GeometricApproximation :=
  { GeometricApproximation.exact 2 with
    sample := fun index => tracedSample s!"LOCALIZATION_SOURCE_SAMPLE {index}" fun _ => 2 }

/-- Print and flush a finite execution boundary before evaluating its retained work. -/
private def report (message : String) : IO Unit := do
  System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate one retained computation after its explicit IO boundary. -/
@[noinline] private def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- The coefficient source Z(Z-1)² with two distinct exact sites. -/
private def twoSites : CoefficientPolynomial := ⟨[1, -2, 1, 0]⟩

/-- Check exact cross-factor table reads, ordered failure and selection from the actual retained caches.

The original two coefficient-produced linear factors require no numerical
state production. Their complete pair entries exercise the shared monadic
table builder, and the same actual table supplies the later source selection.
-/
private def checkPairBank : IO Unit := do
  let source := GeometricApproximation.exact 0
  have bound : ∀ index, normSq (twoSites.eval (source.sample index)) ≤ Basic.quarterRadius 1 index := by
    intro index
    change normSq (twoSites.eval 0) ≤ Basic.quarterRadius 1 index
    rewrite [show twoSites.eval 0 = 0 by decide +kernel, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Basic.quarterRadius_nonneg (by decide +kernel) index
  let preparation := Preparation.ofResidual twoSites (by decide +kernel) source 1 (by decide +kernel) bound
  unless preparation.factors.entries.length = 2 ∧
      CoherentRoot.Multiplicity.size preparation.factors.factors = 2 do
    throw (IO.userError "exact cross-factor bank lost its two original coefficient sites")
  let states ← RootSelectionCheckpoint.Multiplicity.stateReaders preparation.roots
    (fun index => Preparation.factor_eq_ofResidual twoSites (by decide +kernel) source 1
      (by decide +kernel) bound preparation rfl index)
    { savedOnly := true } { savedOnly := true } (System.FilePath.mk "unused-exact-pair-bank")
  let factorPairs := preparation.factorPairs
  let producer := preparation.roots.pairBound factorPairs
  let calls ← System.IO.mkRef ([] : List (Nat × Nat))
  let continued ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "original-pair-entry-reader-unavailable"
  let load := fun (fail : Bool) (first second : Fin (CoherentRoot.Multiplicity.size preparation.factors.factors)) =>
    (show IO {entry : Sequence.Selection.PairBound preparation.roots.candidates first second //
      entry = producer first second} from do
      System.IO.Ref.modify calls (fun previous => previous ++ [(first.val, second.val)])
      if fail && first.val == 1 && second.val == 0 then throw absent
      return ⟨_, rfl⟩)
  Sequence.Selection.Pairs.ofFnM producer (load false) fun pairs => do
    System.IO.Ref.modify continued (fun count => count + 1)
    unless pairs.val.start = 0 ∧ pairs.val.gap = 1 do
      throw (IO.userError "the checked exact pair entries changed their original cached stage or gap")
  unless (← System.IO.Ref.get calls) = [(0, 0), (0, 1), (1, 0), (1, 1)] ∧ (← System.IO.Ref.get continued) = 1 do
    throw (IO.userError "original pair materialization changed row-major order or repeated its continuation")
  calls.set []
  continued.set 0
  try
    Sequence.Selection.Pairs.ofFnM producer (load true) fun _ => System.IO.Ref.modify continued (fun count => count + 1)
    throw (IO.userError "original pair table continued after its actual entry reader failed")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
  unless (← System.IO.Ref.get calls) = [(0, 0), (0, 1), (1, 0)] ∧ (← System.IO.Ref.get continued) = 0 do
    throw (IO.userError "pair-entry failure changed the completed prefix or invoked a later read")
  preparation.roots.pairsWithStates factorPairs states fun pairs => do
    RootSelectionCheckpoint.Multiplicity.select preparation
      (fun request => RootSelectionCheckpoint.Multiplicity.nearby preparation request fun _ =>
        pure ⟨0, by rewrite [preparation.source_eq]; rfl⟩)
      (fun selected => do
        unless selected.val.multiplicity = 1 ∧ selected.val.factorPolynomial.natDegree = 1 ∧
            (preparation.roots.candidates selected.val.anchor.nearby.owner).sample 0 = 0 do
          throw (IO.userError "supplied pair caches changed the original zero site's factor or multiplicity"))
      ⟨factorPairs, rfl⟩ pairs
  report "localization coverage: exact cross-factor bank, ordered failure and supplied caches retained"

/-- Check that coverage budgets defer samples and retain the original stage and actual later locator.

The fixed repeated linear factor has one original candidate. The explicit
reference observation calibrates the sample diagnostic; budget preparation
must emit none, while actual localization must read the same source. -/
public def checkCoverage : IO Unit := do
  checkPairBank
  let source := markedSource
  let preparation := Preparation.ofResidual repeated (by decide +kernel) source 1 (by decide +kernel) (by
    intro index
    change normSq (repeated.eval 2) ≤ Basic.quarterRadius 1 index
    rewrite [show repeated.eval 2 = 0 by decide +kernel, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Basic.quarterRadius_nonneg (by decide +kernel) index)
  let saved ← RootSelectionCheckpoint.Multiplicity.factors
    { savedOnly := true } { savedOnly := true } { savedOnly := true } (System.FilePath.mk ".")
    preparation.factors.entries 0
  let retained := RootIsolation.Residual.Multiplicity.Preparation.ofFamily preparation.decomposition
    preparation.factors.entries preparation.factors.entries_eq saved.val
    preparation.factors.unitQuadrance preparation.factors.unitQuadrance_eq
  unless retained.count = preparation.factors.count ∧ retained.unitQuadrance = preparation.factors.unitQuadrance ∧
      retained.threshold (1 / 16) = preparation.factors.threshold (1 / 16) do
    throw (IO.userError "saved-only exact factor preparation changed its original multiplicity, unit or target")
  report "localization coverage: exact factor family restored without numerical checkpoint production"
  let exactResidual := Polynomial.Approximation.Gaussian.Residual.exact 2
  RootSelectionCheckpoint.Multiplicity.prepare exactResidual
    { savedOnly := true } { savedOnly := true } { savedOnly := true } (System.FilePath.mk ".") fun original => do
    unless original.val.factors.count = 1 ∧ original.val.factors.entries.length = 1 ∧
        original.val.source.sample 0 = 2 ∧ original.val.source.sample 3 = 2 do
      throw (IO.userError "restored exact residual preparation lost its original source or complete factor cache")
    report "localization coverage: complete original exact residual preparation consumed by continuation"
    let request := original.val.coverage.request 7 (1 / 16) (by decide +kernel)
    let nearby ← RootSelectionCheckpoint.Multiplicity.nearbyPrepared exactResidual original.val original.property
      request (fun _ => pure ⟨2, by rewrite [original.val.source_eq]; rfl⟩)
      { savedOnly := true } { savedOnly := true } (System.FilePath.mk ".")
    unless nearby.val.owner.val = 0 ∧ nearby.val.index = 0 ∧
        (original.val.roots.candidates nearby.val.owner).sample nearby.val.index = 2 do
      throw (IO.userError "prepared exact locator lost its original owner, payment or source reading")
    let missing := IO.userError "prepared-source-reader-unavailable"
    try
      let _ ← RootSelectionCheckpoint.Multiplicity.nearbyPrepared exactResidual original.val original.property
        request (fun _ => throw missing) { savedOnly := true } { savedOnly := true } (System.FilePath.mk ".")
      throw (IO.userError "prepared locator continued after the original source reader failed")
    catch failure =>
      unless (System.IO.Error.toString failure) = (System.IO.Error.toString missing) do throw failure
    report "localization coverage: complete original prepared locator and source-reader failure preserved"
  report "localization coverage: budget begin"
  let cover ← evaluate fun _ => preparation.coverage.prepare 7 (1 / 16) (by decide +kernel)
  unless 7 ≤ cover.index do throw (IO.userError "coverage budget lost the original starting index")
  report "localization coverage: budget end"
  report "localization coverage: reference observation begin"
  let reference ← evaluate fun _ => preparation.observe 7
    (epsilon := Dyadic.Geometric.dyadicSquareRadius ((1 / 16) / 128))
    (Dyadic.Geometric.dyadicSquareRadius_positive _)
  unless reference.index = cover.index ∧ reference.sample = 2 do
    throw (IO.userError "coverage budget changed the complete original observation's stage")
  report "localization coverage: reference observation end"
  report "localization coverage: locator begin"
  let nearby ← evaluate fun _ => cover.locate cover.index (Nat.le_refl _)
  unless nearby.owner.val = 0 ∧ (preparation.roots.candidates nearby.owner).sample nearby.index = 2 do
    throw (IO.userError "coverage locator replaced its original candidate or actual reading")
  report "localization coverage: locator end"
  report "localization coverage: cached locator begin"
  let request := preparation.coverage.request 7 (1 / 16) (by decide +kernel)
  let cached ← RootSelectionCheckpoint.Multiplicity.nearby preparation request fun _ =>
    pure ⟨2, by rewrite [preparation.source_eq]; rfl⟩
  unless cached.val.owner.val = nearby.owner.val ∧ cached.val.index = nearby.index do
    throw (IO.userError "cached source localization changed the complete original candidate payment")
  report "localization coverage: cached locator end"
  report "localization coverage: cached selection begin"
  RootSelectionCheckpoint.Multiplicity.select preparation
    (fun request => RootSelectionCheckpoint.Multiplicity.nearby preparation request fun _ =>
      pure ⟨2, by rewrite [preparation.source_eq]; rfl⟩)
    fun selected => do
      unless selected.val.anchor.nearby.owner.val = 0 ∧ selected.val.multiplicity = 2 do
        throw (IO.userError "cached source selection changed its original occurrence or multiplicity")
      report "localization coverage: cached selection end"
  report "localization coverage: missing reader begin"
  let missing := IO.userError "cached-source-reader-unavailable"
  try
    RootSelectionCheckpoint.Multiplicity.select preparation (fun _ => throw missing) fun _ =>
      throw (IO.userError "selection continued after its original reader failed")
    throw (IO.userError "selection replaced its original reader's failure")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString missing) do throw failure
  report "localization coverage: missing reader end"
  report "localization coverage: original stage and candidate retained; deferred sample calibration passed"

end TestPurelib.Polynomial.RootLocalization
