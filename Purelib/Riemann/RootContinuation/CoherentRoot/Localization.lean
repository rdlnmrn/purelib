module

public import Purelib.Approximation.Gaussian.Sequence.Selection
public import Purelib.Riemann.RootContinuation.CoherentRoot.Assignment
import Purelib.Riemann.RootContinuation.CoherentRoot.Family
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.RootIsolation.Residual.Global.Assignment
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stable root selection from original polynomial sample residuals

The original squarefree isolation and coherent root family are cached once.
Their actual owner boxes give a positive common squared gap. Computed residual
localization supplies every finer point request; source coherence identifies
one fixed cached root and derives its all-input operational comparison.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Localization

open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.RootIsolation.Residual
open Purelib.Approximation.Rational.SquareRoot.Radius
open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Geometry.Rational renaming Box -> RationalBox
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Read the original pairwise box-gap square, with one as the unused diagonal entry. -/
private def pairGap {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output polynomial ambient count) (first second : Fin output.tracks.length) :
    Fraction.Rational :=
  if different : first ≠ second then
    (RationalBox.separationCertificate (output.tracks_get_separated first second different)).gap ^ 2
  else 1

/-- Every original pair-budget entry is positive. -/
private theorem pairGap_positive {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output polynomial ambient count) (first second : Fin output.tracks.length) :
    0 < pairGap output first second := by
  unfold pairGap
  split
  · rename_i different
    exact Order.Arithmetic.pow_pos_direct
      (RationalBox.separationCertificate (output.tracks_get_separated first second different)).positive 2
  · exact (show (0 : Fraction.Rational) < 1 by decide)

/-- Compute a common positive squared gap from the same original isolation boxes and cached root programs. -/
def separated {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output polynomial ambient count) (roots : Family output.tracks) :
    Sequence.Selection.Separated (fun index => (roots.get index).approximation) :=
  let rows := List.ofFn (fun first : Fin output.tracks.length =>
    List.ofFn (fun second : Fin output.tracks.length => pairGap output first second))
  let rowMinima := rows.map Data.Rat.List.Minimum.positiveMinimum
  let gap := Data.Rat.List.Minimum.positiveMinimum rowMinima
  have gapPositive : 0 < gap := by
    apply Data.Rat.List.Minimum.positiveMinimum_pos
    intro value member
    rcases Data.List.Map.mem_map.mp member with ⟨row, rowMember, rfl⟩
    rcases Data.List.OfFn.Basic.mem_ofFn.mp rowMember with ⟨first, row_eq⟩
    rewrite [← row_eq]
    apply Data.Rat.List.Minimum.positiveMinimum_pos
    intro value member
    rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨second, value_eq⟩
    rewrite [← value_eq]
    exact pairGap_positive output first second
  have gapLower : ∀ first second, first ≠ second → ∀ firstIndex secondIndex,
      gap ≤ normSq ((roots.get first).approximation.sample firstIndex -
        (roots.get second).approximation.sample secondIndex) := by
    intro first second different firstIndex secondIndex
    let row := List.ofFn (fun other : Fin output.tracks.length => pairGap output first other)
    have rowMember : row ∈ rows := Data.List.OfFn.Basic.mem_ofFn.mpr ⟨first, rfl⟩
    have minimumMember : Data.Rat.List.Minimum.positiveMinimum row ∈ rowMinima :=
      Data.List.Map.mem_map_of_mem rowMember
    have gapLeRow := Data.Rat.List.Minimum.positiveMinimum_le_of_mem minimumMember
    have rowLePair := Data.Rat.List.Minimum.positiveMinimum_le_of_mem
      (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨second, rfl⟩ : pairGap output first second ∈ row)
    have lower := (gapLeRow.trans rowLePair)
    unfold pairGap at lower
    rewrite [dif_pos different] at lower
    exact lower.trans ((roots.get first).separation_lower (roots.get second)
      (RationalBox.separationCertificate (output.tracks_get_separated _ _ different)) firstIndex secondIndex)
  ⟨gap, gapPositive, fun _ => 0, fun first second different firstIndex secondIndex _ _ =>
    gapLower first second different firstIndex secondIndex⟩

set_option genInjectivity false in
/-- One original squarefree isolation, root family and sample program with its quantitative residual budget.

The same stored box result owns every selected root index. The original source
program retains its defining equality and all-index polynomial residual bound.
The common separation certificate reads these actual cached root approximations.
-/
structure Preparation {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (original : GeometricApproximation) where
  /-- The retained original coefficient-computed isolation and ownership function. -/
  boxes : FTA.Squarefree.BoxResult polynomial
  /-- The actual retained isolation has the original coefficient square as support. -/
  support : boxes.isolation.support = RootRadius.Box.largeSquareBox polynomial
  /-- Each original isolated root's actual coherent cache is constructed once. -/
  roots : Family boxes.isolation.tracks
  /-- The actual original sample program retained for selection and comparison. -/
  source : GeometricApproximation
  /-- The same retained program is the original supplied program. -/
  source_eq : source = original
  /-- The common positive gap between the actual original cached root programs. -/
  separated : Sequence.Selection.Separated (fun index => (roots.get index).approximation)
  /-- The retained original polynomial sample-residual scale. -/
  residualScale : Fraction.Rational
  /-- The retained residual scale is nonnegative. -/
  residualScale_nonnegative : 0 ≤ residualScale
  /-- Every sample of the same original program satisfies the retained polynomial residual budget. -/
  residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
    Geometric.Basic.quarterRadius residualScale index

constructive_injectivity Preparation

namespace Preparation

/-- Prepare coherent selection on a retained original isolation without running another isolation producer. -/
@[expose] def ofIsolation {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (boxes : FTA.Squarefree.BoxResult polynomial)
    (support : boxes.isolation.support = RootRadius.Box.largeSquareBox polynomial)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) : Preparation input source :=
  let roots := Family.ofTracks input.degreePositive boxes.isolation.tracks
  let separation := Localization.separated boxes.isolation roots
  ⟨boxes, support, roots, source, rfl, separation, residualScale, scaleNonnegative, residual⟩

/-- Preparing on retained isolation reads back that exact original box result. -/
theorem ofIsolation_boxes {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (boxes : FTA.Squarefree.BoxResult polynomial)
    (support : boxes.isolation.support = RootRadius.Box.largeSquareBox polynomial)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) :
    (ofIsolation input boxes support source residualScale scaleNonnegative residual).boxes = boxes := rfl

/-- Prepare the original isolation, each root cache and their separation once from the original residual program. -/
@[expose] def ofResidual {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) : Preparation input source :=
  let boxes := FTA.Squarefree.Build.BoxFTA.prove input
  ofIsolation input boxes rfl source residualScale scaleNonnegative residual

/-- Residual preparation retains the exact coefficient-computed original isolation result. -/
theorem ofResidual_boxes {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) :
    (ofResidual input source residualScale scaleNonnegative residual).boxes = FTA.Squarefree.Build.BoxFTA.prove input :=
  rfl

/-- Reading an authenticated original isolation preserves the whole residual preparation. -/
private theorem ofIsolation_readback {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (boxes : FTA.Squarefree.BoxResult polynomial)
    (support : boxes.isolation.support = RootRadius.Box.largeSquareBox polynomial)
    (same : boxes = FTA.Squarefree.Build.BoxFTA.prove input)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (nonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) :
    ofIsolation input boxes support source residualScale nonnegative residual =
      ofResidual input source residualScale nonnegative residual := by
  cases same
  rfl

/-- A saved complete original isolation retains the complete original residual preparation.

Its original box result, root family, source programme, separation and residual
scale remain those of the unchanged default constructor.
-/
theorem ofIsolation_eq_ofResidual {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (boxes : FTA.Squarefree.BoxResult polynomial)
    (support : boxes.isolation.support = RootRadius.Box.largeSquareBox polynomial)
    (same : boxes = FTA.Squarefree.Build.BoxFTA.prove input)
    (source : GeometricApproximation) (residualScale : Fraction.Rational)
    (nonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Geometric.Basic.quarterRadius residualScale index) :
    ofIsolation input boxes support source residualScale nonnegative residual =
      ofResidual input source residualScale nonnegative residual :=
  ofIsolation_readback input boxes support same source residualScale nonnegative residual

/-- Prepare stable selection from the same original isolated-root cache and its computed geometric residual scale. -/
def ofCertifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial) {track : WindingOneTrack polynomial ambient}
    (root : CertifiedName track) : Preparation input root.geometric :=
  ofResidual input root.geometric (CoherentRoot.residualScale polynomial ambient track)
    (CoherentRoot.residualScale_nonneg _ _ _) (by
      intro index
      have bound := root.residual index
      rewrite [← root.approximation_eq] at bound
      exact bound)

variable {polynomial : GaussianPolynomial} {input : FTA.Squarefree.Input polynomial}
variable {original : GeometricApproximation}

/-- Read the actual original candidate approximation at its same retained isolation-track index. -/
@[expose] def candidates (preparation : Preparation input original) :
    Fin preparation.boxes.isolation.tracks.length → Sequence.ApproximationData :=
  fun index => (preparation.roots.get index).approximation

/-- Transfer a retained original localization band to the same actual cached owner program at a positive request. -/
def nearby (preparation : Preparation input original)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon preparation.boxes.isolation) :
    Sequence.Selection.Nearby preparation.candidates sample target :=
  Assignment.nearby input preparation.boxes.isolation preparation.roots sample targetPositive radiusSmall localized

/-- Derive complete finite localization coverage from the same original residual scale and isolation cache. -/
def coverage (preparation : Preparation input original) :
    Sequence.Selection.Coverage preparation.source.toApproximation preparation.candidates where
  prepare current target targetPositive := by
    let epsilon := Dyadic.Geometric.dyadicSquareRadius (target / 128)
    have epsilonPositive := Dyadic.Geometric.dyadicSquareRadius_positive (target / 128)
    have radiusSmall := Dyadic.Geometric.dyadicSquareRadius_sq_lt
      (Fraction.Order.Field.div_pos_direct targetPositive
        (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)) : 0 < target / 128)
    let residualTarget := min (Residual.Global.Bounds.outsideResidualThreshold polynomial)
      (Global.Assignment.insideResidualTarget input epsilon)
    have residualTargetPositive : 0 < residualTarget := Fraction.Order.Basic.lt_min
      (Residual.Global.Bounds.outsideResidualThreshold_pos input.degreePositive)
      (Global.Assignment.insideResidualTarget_pos input epsilonPositive)
    let index := Geometric.Search.firstQuarterBelow preparation.residualScale current residualTarget
    have smallBudget := Geometric.Search.firstQuarterBelow_accurate preparation.residualScale
      preparation.residualScale_nonnegative current residualTarget residualTargetPositive
    refine ⟨index, Geometric.Search.firstQuarterBelow_ge preparation.residualScale current residualTarget, ?_⟩
    intro later order
    have small := (preparation.residual later).trans_lt
      ((Geometric.Basic.quarterRadius_antitone preparation.residualScale_nonnegative order).trans_lt smallBudget)
    have outsideSmall := small.trans_le (Fraction.Order.Basic.min_le_left _ _)
    have inside : (RootRadius.Box.largeSquareBox polynomial).Contains
        (preparation.source.sample later) := by
      by_cases contains : (RootRadius.Box.largeSquareBox polynomial).Contains
          (preparation.source.sample later)
      · exact contains
      · exact (not_lt_of_ge (Residual.Global.Bounds.outsideResidualThreshold_le input.degreeAtLeastTwo _ contains)
          outsideSmall).elim
    let localized := Global.Assignment.assignInsideUsing input preparation.boxes preparation.support
      (preparation.source.sample later) inside epsilonPositive (small.trans_le (Fraction.Order.Basic.min_le_right _ _))
    exact preparation.nearby _ targetPositive radiusSmall localized

/-- The literal dyadic radius used by an original finite localization request. -/
def localizationRadius (target : Fraction.Rational) : Fraction.Rational :=
  Dyadic.Geometric.dyadicSquareRadius (target / 128)

/-- The original localization radius is positive at every rational target. -/
theorem localizationRadius_positive (target : Fraction.Rational) : 0 < localizationRadius target :=
  Dyadic.Geometric.dyadicSquareRadius_positive (target / 128)

/-- The original dyadic localization radius pays its precise one-hundred-twenty-eighth allocation. -/
theorem localizationRadius_small {target : Fraction.Rational} (positive : 0 < target) :
    localizationRadius target ^ 2 < target / 128 :=
  Dyadic.Geometric.dyadicSquareRadius_sq_lt
    (Fraction.Order.Field.div_pos_direct positive
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))

/-- A retained coverage stage has the original inside-square and strict residual bounds. -/
private theorem coverage_sample (preparation : Preparation input original)
    (current : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (later : Nat) (order : (preparation.coverage.prepare current target positive).index ≤ later) :
    (RootRadius.Box.largeSquareBox polynomial).Contains
      (preparation.source.sample later) ∧
      normSq (polynomial.eval (preparation.source.sample later)) <
        Global.Assignment.insideResidualTarget input (localizationRadius target) := by
  let residualTarget := min (Residual.Global.Bounds.outsideResidualThreshold polynomial)
    (Global.Assignment.insideResidualTarget input (localizationRadius target))
  have residualTargetPositive : 0 < residualTarget := Fraction.Order.Basic.lt_min
    (Residual.Global.Bounds.outsideResidualThreshold_pos input.degreePositive)
    (Global.Assignment.insideResidualTarget_pos input (localizationRadius_positive target))
  have smallBudget := Geometric.Search.firstQuarterBelow_accurate preparation.residualScale
    preparation.residualScale_nonnegative current residualTarget residualTargetPositive
  have originalOrder : Geometric.Search.firstQuarterBelow preparation.residualScale current residualTarget ≤ later :=
    order
  have small := (preparation.residual later).trans_lt
    ((Geometric.Basic.quarterRadius_antitone preparation.residualScale_nonnegative originalOrder).trans_lt smallBudget)
  have outsideSmall := small.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have inside : (RootRadius.Box.largeSquareBox polynomial).Contains
      (preparation.source.sample later) := by
    by_cases contains : (RootRadius.Box.largeSquareBox polynomial).Contains
        (preparation.source.sample later)
    · exact contains
    · exact (not_lt_of_ge (Residual.Global.Bounds.outsideResidualThreshold_le input.degreeAtLeastTwo _ contains)
        outsideSmall).elim
  exact ⟨inside, small.trans_le (Fraction.Order.Basic.min_le_right _ _)⟩

/-- The actual retained coverage request's source sample lies in the original isolation square. -/
theorem request_inside (preparation : Preparation input original)
    {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target) :
    (RootRadius.Box.largeSquareBox polynomial).Contains
      (preparation.source.sample request.index) := by
  have order : (preparation.coverage.prepare current target request.positive).index ≤ request.index := by
    rewrite [← request.cover_eq]
    exact request.index_ge
  exact (coverage_sample preparation current target request.positive request.index order).1

/-- The actual retained coverage sample meets its original strict anchored-seed residual request. -/
theorem request_residualSmall (preparation : Preparation input original)
    {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target) :
    normSq (polynomial.eval (preparation.source.sample request.index)) <
      Global.Assignment.insideResidualTarget input (localizationRadius target) := by
  have order : (preparation.coverage.prepare current target request.positive).index ≤ request.index := by
    rewrite [← request.cover_eq]
    exact request.index_ge
  exact (coverage_sample preparation current target request.positive request.index order).2

/-- Localizing a retained coverage request is its exact original inside assignment and nearby record.

The equality exposes the original request's mathematical operands without
executing its localized seed, state, owner selection or candidate payment.
-/
theorem request_locate_eq (preparation : Preparation input original)
    {current : Nat} {target : Fraction.Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target) :
    request.locate = Assignment.nearby input preparation.boxes.isolation preparation.roots
      (preparation.source.sample request.index) request.positive (localizationRadius_small request.positive)
      (Global.Assignment.assignInsideUsing input preparation.boxes preparation.support
        (preparation.source.sample request.index) (preparation.request_inside request)
        (localizationRadius_positive target) (preparation.request_residualSmall request)) := by
  rcases request with ⟨positive, cover, coverEq, index, indexEq⟩
  cases coverEq
  cases indexEq
  rfl

set_option genInjectivity false in
/-- A stable original root index selected from the retained source residual program and same cached root family. -/
structure Selection (preparation : Preparation input original) where
  /-- The actual source anchor and localized original candidate used for stable selection. -/
  anchor : Sequence.Selection.Anchor preparation.source.toApproximation preparation.separated

constructive_injectivity Selection

/-- Compute the original fixed root selection without a supplied result branch or successful search. -/
def select (preparation : Preparation input original) : Selection preparation :=
  ⟨Sequence.Selection.Anchor.ofCoverage preparation.source.toApproximation preparation.separated preparation.coverage⟩

/-- Read the whole original selection without exposing its default construction body. -/
private theorem select_readback (preparation : Preparation input original) :
    preparation.select = ⟨Sequence.Selection.Anchor.ofCoverage preparation.source.toApproximation
      preparation.separated preparation.coverage⟩ := rfl

/-- The original selection retains the complete anchor computed from its original coverage. -/
theorem select_eq (preparation : Preparation input original) :
    preparation.select = ⟨Sequence.Selection.Anchor.ofCoverage preparation.source.toApproximation
      preparation.separated preparation.coverage⟩ := select_readback preparation

/-- Read the retained original isolated root at the same fixed bounded selection index. -/
@[expose] def Selection.root {preparation : Preparation input original} (selection : Selection preparation) :
    CertifiedName (preparation.boxes.isolation.tracks.get selection.anchor.nearby.owner) :=
  preparation.roots.get selection.anchor.nearby.owner

/-- The original source approximation agrees with the fixed selected original root for every pair of starts. -/
def Selection.equivalent {preparation : Preparation input original} (selection : Selection preparation) :
    Equivalence.Equivalent original.toApproximation selection.root.approximation := by
  have comparison := selection.anchor.equivalent preparation.coverage
  have identity := congrArg
    (fun source : GeometricApproximation => Equivalence.Equivalent source.toApproximation selection.root.approximation)
    preparation.source_eq
  exact identity.mp comparison

/-- Compare the selected original channels from one authenticated nearby payment.

The complete comparison reads the original retained anchor and request, then
uses the preparation's actual source identity to retain the original source
channel without rebuilding its coverage localization.
-/
def Selection.compareFromNearby {preparation : Preparation input original} (selection : Selection preparation)
    (sourceStart candidateStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (request : Sequence.Selection.Coverage.Request preparation.coverage
      (Nat.max sourceStart selection.anchor.index) (min (preparation.separated.gap / 16) (target / 8)))
    (nearby : { value : Sequence.Selection.Nearby preparation.candidates
      (preparation.source.sample request.index) (min (preparation.separated.gap / 16) (target / 8)) //
      value = request.locate }) :
    Equivalence.Comparison original.toApproximation selection.root.approximation sourceStart candidateStart target := by
  let comparison := selection.anchor.compareFromNearby preparation.coverage
    sourceStart candidateStart target positive request nearby
  have identity := congrArg (fun source : GeometricApproximation =>
    Equivalence.Comparison source.toApproximation selection.root.approximation sourceStart candidateStart target)
    preparation.source_eq
  exact identity.mp comparison

/-- Transporting a complete operational comparison reads the same original comparison record. -/
private theorem comparison_transport {first second : GeometricApproximation}
    (same : first = second) {candidate : Sequence.ApproximationData}
    (equivalent : Equivalence.Equivalent first.toApproximation candidate)
    (sourceStart candidateStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    (congrArg (fun source : GeometricApproximation =>
      Equivalence.Comparison source.toApproximation candidate sourceStart candidateStart target) same).mp
        (equivalent.compare sourceStart candidateStart target positive) =
      ((congrArg (fun source : GeometricApproximation =>
        Equivalence.Equivalent source.toApproximation candidate) same).mp equivalent).compare
          sourceStart candidateStart target positive := by
  cases same
  rfl

/-- Supplied nearby execution retains the complete original selected-channel comparison.

Both independent starts, the exact positive target and the original source
identity are retained in this whole-result equality.
-/
theorem Selection.compareFromNearby_eq {preparation : Preparation input original} (selection : Selection preparation)
    (sourceStart candidateStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (request : Sequence.Selection.Coverage.Request preparation.coverage
      (Nat.max sourceStart selection.anchor.index) (min (preparation.separated.gap / 16) (target / 8)))
    (nearby : { value : Sequence.Selection.Nearby preparation.candidates
      (preparation.source.sample request.index) (min (preparation.separated.gap / 16) (target / 8)) //
      value = request.locate }) :
    selection.compareFromNearby sourceStart candidateStart target positive request nearby =
      selection.equivalent.compare sourceStart candidateStart target positive := by
  unfold Selection.compareFromNearby
  rewrite [selection.anchor.compareFromNearby_eq preparation.coverage
    sourceStart candidateStart target positive request nearby]
  exact comparison_transport preparation.source_eq (selection.anchor.equivalent preparation.coverage)
    sourceStart candidateStart target positive

/-- Compare an original isolated-root channel with the same selected original cached root channel. -/
def Selection.original_equivalent {ambient : Box} {track : WindingOneTrack polynomial ambient}
    (root : CertifiedName track) {preparation : Preparation input root.geometric}
    (selection : Selection preparation) :
    Equivalence.NamedEquivalent root.value.name selection.root.value.name := by
  rewrite [selection.root.value_approximation]
  exact root.geometric_agrees.trans selection.equivalent.toNamed

end Preparation

end Purelib.Riemann.RootContinuation.CoherentRoot.Localization

end
