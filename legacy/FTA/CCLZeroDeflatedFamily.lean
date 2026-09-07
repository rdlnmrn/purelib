import FTA.CCLActiveMetricFamily
import FTA.DeflatedWinding

/-!
# The nonzero CCL family after constructive zero deflation

When a squarefree polynomial has zero as a root, that root is returned as an
exact distinguished terminal.  The remaining factor has nonzero constant
term, one lower degree, and an explicit transformed squarefree certificate.
This module isolates that factor and starts every one of its active CCL
machines only after a finite refinement has excluded the terminal origin.
-/

namespace FTA
namespace CCLZeroDeflatedFamily

open CCL
open FTA.AxisSafeCuts
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLActiveObservedEnvelopeProgress
open FTA.CCLDenominator
open FTA.CCLFiniteTaggedEnvelope
open FTA.CCLGeometry
open FTA.GaussianZeroDeflation
open FTA.GlobalWinding
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- All finite input data for the positive-degree quotient branch.  The
elimination certificate is for the quotient actually sent to exact
isolation, rather than for the already-separated linear zero factor. -/
structure Input (p : GaussianPolynomial) where
  squarefree : GaussianSquarefreeCertificate p
  degree : 1 < p.natDegree
  zero : p.eval 0 = 0
  eliminationDegree : ℕ
  elimination : AxisEliminationCertificate (quotient p) eliminationDegree

namespace Input

theorem originalNonzero {p : GaussianPolynomial} (input : Input p) :
    p.isZero = false :=
  isZero_false_of_natDegree_pos (Nat.zero_lt_one.trans input.degree)

theorem quotientNonzero {p : GaussianPolynomial} (input : Input p) :
    (quotient p).isZero = false :=
  quotient_isZero_false input.originalNonzero input.zero

theorem quotientDegreePositive {p : GaussianPolynomial} (input : Input p) :
    0 < (quotient p).natDegree :=
  quotient_natDegree_pos input.originalNonzero input.zero input.degree

theorem quotientSparseDegreeNonzero {p : GaussianPolynomial} (input : Input p) :
    (quotient p).toPolynomial.natDegree ≠ 0 := by
  rw [FTA.ComputablePolynomial.DensePolynomial.natDegree_toPolynomial
    input.quotientNonzero]
  exact Nat.ne_of_gt input.quotientDegreePositive

def quotientSquarefree {p : GaussianPolynomial} (input : Input p) :
    GaussianSquarefreeCertificate (quotient p) :=
  quotientSquarefreeCertificate input.squarefree input.originalNonzero
    input.zero

theorem quotientZeroNonzero {p : GaussianPolynomial} (input : Input p) :
    (quotient p).eval 0 ≠ 0 :=
  quotient_eval_zero_ne_zero input.squarefree input.originalNonzero input.zero

/-- Exact isolation of all nonzero roots, now labelled by the quotient. -/
def output {p : GaussianPolynomial} (input : Input p) :
    ExactIsolation.Output (quotient p) (largeSquareBox (quotient p))
      (quotient p).natDegree :=
  ExactIsolation.isolateLargeSquare input.quotientSquarefree
    input.quotientDegreePositive input.elimination

theorem output_count_add_one {p : GaussianPolynomial} (input : Input p) :
    (input.output.tracks.length + 1) = p.natDegree := by
  rw [input.output.tracks_length]
  exact quotient_natDegree_add_one input.originalNonzero input.zero

/-- One coefficient-bounded refinement that excludes the distinguished zero
terminal from a quotient track. -/
def zeroFreeNumericalAt
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    WindingOneState (quotient p) (largeSquareBox (quotient p)) :=
  refineAwayFromNonroot (input.output.trackAt index)
    (input.output.trackAt index).initial 0 input.quotientZeroNonzero

theorem zeroFreeNumericalAt_refines
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    (input.zeroFreeNumericalAt index).box.Refines
      (input.output.trackAt index).initial.box :=
  refineAwayFromNonroot_refines (input.output.trackAt index)
    (input.output.trackAt index).initial 0 input.quotientZeroNonzero

theorem zeroFreeNumericalAt_excludes_zero
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    ¬(input.zeroFreeNumericalAt index).box.Contains 0 :=
  refineAwayFromNonroot_excludes (input.output.trackAt index)
    (input.output.trackAt index).initial 0 input.quotientZeroNonzero

/-- Empty-word denominator separation seeded at the zero-free refinement. -/
def zeroFreeSeparationAt
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    CCLDenominator.SeparationOutput (quotient p)
      (largeSquareBox (quotient p)) (input.zeroFreeNumericalAt index)
      (adjugate (RawParser.parse []).matrix) :=
  CCLDenominator.separateConstantDenominator
    (input.zeroFreeNumericalAt index)
    (adjugate (RawParser.parse []).matrix) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate]) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate])

/-- Active empty-word state whose numerical box is already separated from
the exact zero terminal. -/
def zeroFreeStateAt
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    State (quotient p) (largeSquareBox (quotient p)) :=
  CCLActiveMetricTrack.ofInitialSeparation
    (input.zeroFreeSeparationAt index)

@[simp] theorem zeroFreeStateAt_word
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    (input.zeroFreeStateAt index).core.word = [] := by
  simp [zeroFreeStateAt, CCLActiveMetricTrack.ofInitialSeparation]

theorem zeroFreeStateAt_box
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    (input.zeroFreeStateAt index).core.numerical.box =
      (input.zeroFreeNumericalAt index).box := by
  simp [zeroFreeStateAt, zeroFreeSeparationAt,
    CCLActiveMetricTrack.ofInitialSeparation,
    CCLDenominator.separateConstantDenominator]

theorem zeroFreeStateAt_excludes_zero
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    ¬(input.zeroFreeStateAt index).core.numerical.box.Contains 0 := by
  rw [input.zeroFreeStateAt_box index]
  exact input.zeroFreeNumericalAt_excludes_zero index

/-- The zero-free state is a legitimate refinement of the exact-isolation
family state used by the common pairwise-gap theorems. -/
theorem zeroFreeStateAt_refines_initial
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) :
    StateRefines (input.zeroFreeStateAt index)
      (CCLActiveMetricFamily.initialStateAt input.output index) := by
  constructor
  · rw [input.zeroFreeStateAt_box index,
      CCLActiveMetricFamily.initialStateAt_box]
    exact input.zeroFreeNumericalAt_refines index
  · rw [input.zeroFreeStateAt_word,
      CCLActiveMetricFamily.initialStateAt_word_nil]

/-- Existing active machine specialized to a quotient track.  Its global
nonzero-at-origin premise is now supplied by the deflation theorem. -/
def machineAt
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) (clearOwnerLabel : Bool) :
    Machine (quotient p) (denseLargeSquareRadius (quotient p))
      (denseLargeSquareRadius_pos (quotient p)).le :=
  CCLActiveMetricFamily.machineAt input.output index clearOwnerLabel
    input.quotientSquarefree input.quotientSparseDegreeNonzero
      input.quotientZeroNonzero input.elimination

/-- Result of a finite CCL request on one nonzero factor track, relabelled
with the corresponding exact root statement for the original polynomial. -/
inductive RequestResult
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) (target : ℚ) where
  | terminal (point : QI) (quotientRoot : (quotient p).eval point = 0)
      (root : p.eval point = 0) (nonzero : point ≠ 0)
      (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : (input.zeroFreeStateAt index).core.numerical.box.Contains
        point) :
      RequestResult input index target
  | nonterminal
      (state : State (quotient p) (largeSquareBox (quotient p)))
      (refines : StateRefines state (input.zeroFreeStateAt index))
      (envelope : FiniteTaggedEnvelope)
      (box_eq : envelope.box = state.core.numerical.box)
      (word_eq : envelope.tag.word = state.core.word)
      (boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2)
      (accurate : envelope.errorSq ≤ 2 * (target ^ 2 + target))
      (excludesZero : ¬state.core.numerical.box.Contains 0) :
      RequestResult input index target

/-- Total positive request on one deflated nonzero track.  The apparent zero
result of the underlying generic controller contradicts `q(0) ≠ 0`; an exact
nonzero quotient root is transported pointwise to an original root. -/
def requestAt
    {p : GaussianPolynomial} (input : Input p)
    (index : Fin (quotient p).natDegree) (clearOwnerLabel : Bool)
    (target : ℚ) (targetPositive : 0 < target) :
    RequestResult input index target := by
  let run := requestFinite (input.machineAt index clearOwnerLabel)
    (input.zeroFreeStateAt index) target targetPositive
  match run with
  | .zero root => exact (input.quotientZeroNonzero root).elim
  | .terminal point quotientRoot nonzero completeWord complete contains =>
      exact .terminal point quotientRoot
        (quotient_root_is_root input.originalNonzero input.zero quotientRoot)
          nonzero completeWord complete contains
  | .nonterminal state refines envelope boxEq wordEq boxAccurate accurate =>
      exact .nonterminal state refines envelope boxEq wordEq boxAccurate
        accurate (by
          intro contains
          exact input.zeroFreeStateAt_excludes_zero index
            (refines.box.contains contains))

end Input

end CCLZeroDeflatedFamily
end FTA
