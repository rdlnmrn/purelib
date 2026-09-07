import FTA.CCLCompletedBlockObservation
import FTA.CCLActiveEventGrid

/-!
# Persistent finite chains of independently sampled CCL blocks

The active root controller can recompute each completed-block witness in any
later winding-box refinement.  This file stores those providers in decoder
order and materializes a finite approximate contraction trace on demand.
-/

namespace FTA
namespace CCLPersistentBlockObservations

open CCL
open FTA.CCLActiveEventGrid
open FTA.CCLApproximateBlockContraction
open FTA.CCLCompletedBlockContraction
open FTA.CCLCompletedBlockObservation
open FTA.CCLProjectiveMatrixBounds
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

namespace DecoderBlock

/-- Accumulate a decoder block list from an arbitrary outer matrix. -/
def matrixProduct : Mat2 QI → List DecoderBlock → Mat2 QI
  | outer, [] => outer
  | outer, block :: blocks =>
      matrixProduct (Mat2.mul outer block.matrix) blocks

@[simp] theorem matrixProduct_nil (outer : Mat2 QI) :
    matrixProduct outer [] = outer := rfl

@[simp] theorem matrixProduct_cons
    (outer : Mat2 QI) (block : DecoderBlock) (blocks : List DecoderBlock) :
    matrixProduct outer (block :: blocks) =
      matrixProduct (Mat2.mul outer block.matrix) blocks := rfl

theorem matrixProduct_append (outer : Mat2 QI)
    (first second : List DecoderBlock) :
    matrixProduct outer (first ++ second) =
      matrixProduct (matrixProduct outer first) second := by
  induction first generalizing outer with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      exact inductionHypothesis (Mat2.mul outer block.matrix)

theorem act_matrixProduct (outer : Mat2 QI) (blocks : List DecoderBlock)
    (point : Proj QI) :
    Mat2.act (matrixProduct outer blocks) point =
      Mat2.act outer (DecoderBlock.decode blocks point) := by
  induction blocks generalizing outer with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      rw [matrixProduct_cons, inductionHypothesis, DecoderBlock.decode,
        Mat2.act_mul]

/-- The accumulated observation-chain matrix is exactly the matrix retained
by the raw parser. -/
theorem matrixProduct_parserBlocks (word : Prefix.Word) :
    matrixProduct RawParser.identityMatrix (parserBlocks word) =
      (RawParser.parse word).matrix := by
  have action (point : Proj QI) :
      Mat2.act (matrixProduct RawParser.identityMatrix (parserBlocks word))
          point =
        Mat2.act (RawParser.parse word).matrix point := by
    calc
      Mat2.act (matrixProduct RawParser.identityMatrix (parserBlocks word))
          point =
        Mat2.act RawParser.identityMatrix
          (DecoderBlock.decode (parserBlocks word) point) :=
        act_matrixProduct RawParser.identityMatrix (parserBlocks word) point
      _ = DecoderBlock.decode (parserBlocks word) point := by
        ext <;> simp [Mat2.act, RawParser.identityMatrix]
      _ = Mat2.act (RawParser.parse word).matrix point :=
        decoderBlocks_parse_eq_act word point
  apply Mat2.ext
  · have equality := congrArg Proj.p (action Proj.omega)
    simpa [Mat2.act, Proj.omega] using equality
  · have equality := congrArg Proj.p (action (Proj.affine 0))
    simpa [Mat2.act, Proj.affine] using equality
  · have equality := congrArg Proj.q (action Proj.omega)
    simpa [Mat2.act, Proj.omega] using equality
  · have equality := congrArg Proj.q (action (Proj.affine 0))
    simpa [Mat2.act, Proj.affine] using equality

end DecoderBlock

/-- Samples for a block list in outer-to-inner decoder order.  Each sample is
allowed its own rational point of the same displayed winding box. -/
inductive SampleChain (box : RatBox) :
    (outer : Mat2 QI) → List DecoderBlock → Type where
  | nil (outer : Mat2 QI) : SampleChain box outer []
  | cons {outer : Mat2 QI} {block : DecoderBlock}
      {blocks : List DecoderBlock}
      (head : BlockObservationSample outer block box)
      (tail : SampleChain box (Mat2.mul outer block.matrix) blocks) :
      SampleChain box outer (block :: blocks)

namespace SampleChain

/-- Outer projective output displayed by a sampled chain. -/
def front
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) : Proj QI :=
  match chain with
  | .nil _ => Proj.omega
  | .cons head _ => head.output

/-- Rational box point used by the outermost observation of a nonempty
sampled block list. -/
def headPoint
    {box : RatBox} {outer : Mat2 QI} {block : DecoderBlock}
    {blocks : List DecoderBlock}
    (chain : SampleChain box outer (block :: blocks)) : QI :=
  match chain with
  | .cons head _ => head.point

theorem headPoint_inside
    {box : RatBox} {outer : Mat2 QI} {block : DecoderBlock}
    {blocks : List DecoderBlock}
    (chain : SampleChain box outer (block :: blocks)) :
    box.Contains chain.headPoint := by
  cases chain with
  | cons head tail => exact head.inside

/-- With identity outer decoder, the envelope center is projectively exactly
the rational point of its outermost block observation. -/
theorem front_chordalSq_affine_headPoint_eq_zero
    {box : RatBox} {block : DecoderBlock} {blocks : List DecoderBlock}
    (chain : SampleChain box RawParser.identityMatrix (block :: blocks)) :
    chordalSq chain.front (Proj.affine chain.headPoint) = 0 := by
  cases chain with
  | cons head tail =>
      have equality := head.output_chordalSq_eq_inverse
        (Proj.affine head.point)
      have identityAction :
          Mat2.act (CCLGeometry.adjugate RawParser.identityMatrix)
              (Proj.affine head.point) = Proj.affine head.point := by
        ext <;>
          simp [Mat2.act, CCLGeometry.adjugate, RawParser.identityMatrix,
            Proj.affine]
      rw [identityAction,
        chordalSq_eq_zero_of_equivalent
          (Proj.Equivalent.refl (Proj.affine head.point))] at equality
      exact equality

/-- Every mismatch between consecutive observations is below one common
rational squared-chordal error. -/
def LinksBound
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) (epsilon : ℚ) : Prop :=
  match chain with
  | .nil _ => True
  | .cons _ (.nil _) => True
  | .cons head (.cons next rest) =>
      chordalSq head.tail.point
          next.output ≤ epsilon ∧
        LinksBound (.cons next rest) epsilon

/-- One positive box request simultaneously stabilizes every consecutive
inverse decoder in a finite block list. -/
def stabilityRequest : Mat2 QI → List DecoderBlock → ℚ → ℚ
  | _, [], _ => 1
  | _, [_], _ => 1
  | outer, first :: second :: blocks, epsilon =>
      min
        (inverseTailBoxRequest (Mat2.mul outer first.matrix) epsilon)
        (stabilityRequest (Mat2.mul outer first.matrix)
          (second :: blocks) epsilon)

theorem stabilityRequest_pos
    (outer : Mat2 QI) (blocks : List DecoderBlock) {epsilon : ℚ}
    (outerDeterminantNonzero : outer.det ≠ 0)
    (epsilonPositive : 0 < epsilon) :
    0 < stabilityRequest outer blocks epsilon := by
  induction blocks using List.twoStepInduction generalizing outer with
  | nil => simp [stabilityRequest]
  | singleton block => simp [stabilityRequest]
  | cons_cons first second blocks _ inductionHypothesis =>
      simp only [stabilityRequest, lt_min_iff]
      constructor
      · apply inverseTailBoxRequest_pos
        exact epsilonPositive
      · apply inductionHypothesis second
        · rw [RawParser.det_mul]
          exact mul_ne_zero outerDeterminantNonzero (by
            change (RawParser.blockMatrix first.kind first.exponent
              first.sector).det ≠ 0
            exact RawParser.blockMatrix_det_ne first.kind first.exponent
              first.sector)

/-- A box satisfying the joint request gives all of its materialized
observation links the requested error. -/
theorem linksBound_of_boxBound
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks)
    (outerDeterminantNonzero : outer.det ≠ 0)
    {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (boxBound : box.diagonalSq ≤
      stabilityRequest outer blocks epsilon ^ 2) :
    chain.LinksBound epsilon := by
  induction chain with
  | nil matrix => trivial
  | @cons matrix first blocks head tail inductionHypothesis =>
      cases tail with
      | nil _ => trivial
      | @cons _ second rest next remaining =>
          have firstRequestPositive :
              0 < inverseTailBoxRequest
                (Mat2.mul matrix first.matrix) epsilon :=
            inverseTailBoxRequest_pos _ epsilonPositive
          have tailMatrixDeterminantNonzero :
              (Mat2.mul matrix first.matrix).det ≠ 0 := by
            rw [RawParser.det_mul]
            exact mul_ne_zero outerDeterminantNonzero (by
              change (RawParser.blockMatrix first.kind first.exponent
                first.sector).det ≠ 0
              exact RawParser.blockMatrix_det_ne first.kind first.exponent
                first.sector)
          have tailRequestPositive :
              0 < stabilityRequest (Mat2.mul matrix first.matrix)
                (second :: rest) epsilon :=
            stabilityRequest_pos _ _ tailMatrixDeterminantNonzero
              epsilonPositive
          have jointNonnegative :
              0 ≤ stabilityRequest matrix (first :: second :: rest)
                epsilon :=
            (stabilityRequest_pos matrix (first :: second :: rest)
              outerDeterminantNonzero epsilonPositive).le
          have firstRequestBound :
              stabilityRequest matrix (first :: second :: rest) epsilon ≤
                inverseTailBoxRequest
                  (Mat2.mul matrix first.matrix) epsilon := by
            exact min_le_left _ _
          have tailRequestBound :
              stabilityRequest matrix (first :: second :: rest) epsilon ≤
                stabilityRequest (Mat2.mul matrix first.matrix)
                  (second :: rest) epsilon := by
            exact min_le_right _ _
          have firstSquareBound :
              stabilityRequest matrix (first :: second :: rest) epsilon ^ 2 ≤
                inverseTailBoxRequest
                  (Mat2.mul matrix first.matrix) epsilon ^ 2 := by
            nlinarith
          have tailSquareBound :
              stabilityRequest matrix (first :: second :: rest) epsilon ^ 2 ≤
                stabilityRequest (Mat2.mul matrix first.matrix)
                  (second :: rest) epsilon ^ 2 := by
            nlinarith
          constructor
          · apply head.consecutive_link_le_of_request next
              outerDeterminantNonzero epsilon epsilonPositive
            exact boxBound.trans firstSquareBound
          · apply inductionHypothesis tailMatrixDeterminantNonzero
            exact boxBound.trans tailSquareBound

/-- Concatenate two dependently indexed observation chains. -/
def append
    {box : RatBox} {outer : Mat2 QI} {first second : List DecoderBlock}
    (left : SampleChain box outer first)
    (right : SampleChain box (DecoderBlock.matrixProduct outer first) second) :
    SampleChain box outer (first ++ second) :=
  match first, left with
  | [], .nil _ => right
  | _ :: _, .cons head tail => .cons head (append tail right)

/-- One final observed block. -/
def singleton
    {box : RatBox} {outer : Mat2 QI} {block : DecoderBlock}
    (sample : BlockObservationSample outer block box) :
    SampleChain box outer [block] :=
  .cons sample (.nil (Mat2.mul outer block.matrix))

/-- Data produced when a sampled chain is turned into the perturbed trace
consumed by the quantitative contraction theorem. -/
structure BuiltTrace (blocks : List DecoderBlock) where
  output : Proj QI
  terminal : Proj QI
  trace : ApproximateTrace blocks output terminal
  terminalValid : terminal.HasNonzeroCoordinate
  budget : ℚ
  traceErrorBudget : trace.errorBudget = budget

/-- Materialize the approximate trace.  At the innermost observed block its
own compatible tail is used as the terminal coordinate, so the final link
error is exactly zero rather than an arbitrary unit fallback. -/
def buildTrace
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) : BuiltTrace blocks :=
  match chain with
  | .nil _ =>
      { output := Proj.omega
        terminal := Proj.omega
        trace := .nil Proj.omega
        terminalValid := Proj.omega_hasNonzeroCoordinate
        budget := 0
        traceErrorBudget := by simp [ApproximateTrace.errorBudget] }
  | .cons head (.nil _) =>
      { output := head.output
        terminal := head.tail.point
        trace := .cons head.tail (.nil head.tail.point) 0 (by norm_num)
          (chordalSq_eq_zero_of_equivalent
            (Proj.Equivalent.refl head.tail.point)).le
        terminalValid := head.tail.point_hasNonzeroCoordinate
        budget := 0
        traceErrorBudget := by simp [ApproximateTrace.errorBudget] }
  | .cons head (.cons nextHead nextTail) =>
      let innerChain := SampleChain.cons nextHead nextTail
      let innerTrace := buildTrace innerChain
      { output := head.output
        terminal := innerTrace.terminal
        trace := .cons head.tail innerTrace.trace
          (chordalSq head.tail.point innerTrace.output)
          (chordalSq_nonneg _ _)
          le_rfl
        terminalValid := innerTrace.terminalValid
        budget := chordalSq head.tail.point innerTrace.output +
          (3 / 4 : ℚ) * innerTrace.budget
        traceErrorBudget := by
          rw [ApproximateTrace.errorBudget_cons,
            innerTrace.traceErrorBudget] }

/-- A materialized approximate trace together with the proved discounted
error bound supplied by one common per-link request. -/
structure BoundedTrace (blocks : List DecoderBlock) (epsilon : ℚ)
    (expectedOutput : Proj QI)
    extends BuiltTrace blocks where
  output_eq : output = expectedOutput
  budget_le : budget ≤ 4 * epsilon

/-- Build the trace and its budget proof together, avoiding any later choice
or normalization of the independently sampled witnesses. -/
def buildBoundedTrace
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) (epsilon : ℚ)
    (epsilonNonnegative : 0 ≤ epsilon)
    (links : chain.LinksBound epsilon) :
    BoundedTrace blocks epsilon chain.front :=
  match chain with
  | .nil _ =>
      { output := Proj.omega
        terminal := Proj.omega
        trace := .nil Proj.omega
        terminalValid := Proj.omega_hasNonzeroCoordinate
        budget := 0
        traceErrorBudget := by simp [ApproximateTrace.errorBudget]
        output_eq := rfl
        budget_le := by linarith }
  | .cons head (.nil _) =>
      { output := head.output
        terminal := head.tail.point
        trace := .cons head.tail (.nil head.tail.point) 0 (by norm_num)
          (chordalSq_eq_zero_of_equivalent
            (Proj.Equivalent.refl head.tail.point)).le
        terminalValid := head.tail.point_hasNonzeroCoordinate
        budget := 0
        traceErrorBudget := by simp [ApproximateTrace.errorBudget]
        output_eq := rfl
        budget_le := by linarith }
  | .cons head (.cons nextHead nextTail) =>
      let innerChain := SampleChain.cons nextHead nextTail
      let innerTrace := buildBoundedTrace innerChain epsilon
        epsilonNonnegative links.2
      { output := head.output
        terminal := innerTrace.terminal
        trace := .cons head.tail innerTrace.trace
          (chordalSq head.tail.point innerTrace.output)
          (chordalSq_nonneg _ _)
          le_rfl
        terminalValid := innerTrace.terminalValid
        budget := chordalSq head.tail.point innerTrace.output +
          (3 / 4 : ℚ) * innerTrace.budget
        traceErrorBudget := by
          rw [ApproximateTrace.errorBudget_cons,
            innerTrace.traceErrorBudget]
        output_eq := rfl
        budget_le := by
          have headLink :
              chordalSq head.tail.point innerTrace.output ≤ epsilon := by
            rw [innerTrace.output_eq]
            simpa only [front] using links.1
          linarith [innerTrace.budget_le] }

/-- Two independently materialized chains in the same sufficiently small box
have outputs bounded by geometric block contraction plus explicit finite
sampling error. -/
theorem buildBoundedTrace_pair_chordalSq_le
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (left right : SampleChain box outer blocks)
    {epsilon : ℚ} (epsilonNonnegative : 0 ≤ epsilon)
    (leftLinks : left.LinksBound epsilon)
    (rightLinks : right.LinksBound epsilon) :
    chordalSq
        (left.buildBoundedTrace epsilon epsilonNonnegative leftLinks).output
        (right.buildBoundedTrace epsilon epsilonNonnegative rightLinks).output ≤
      (3 / 4 : ℚ) ^ blocks.length + 32 * epsilon := by
  let leftTrace := left.buildBoundedTrace epsilon epsilonNonnegative leftLinks
  let rightTrace := right.buildBoundedTrace epsilon epsilonNonnegative rightLinks
  have contraction :=
    ApproximateTrace.chordalSq_le_three_quarters_pow_add_error_of_valid
      leftTrace.trace rightTrace.trace leftTrace.terminalValid
        rightTrace.terminalValid
  have leftBudget : leftTrace.trace.errorBudget ≤ 4 * epsilon := by
    rw [leftTrace.traceErrorBudget]
    exact leftTrace.budget_le
  have rightBudget : rightTrace.trace.errorBudget ≤ 4 * epsilon := by
    rw [rightTrace.traceErrorBudget]
    exact rightTrace.budget_le
  change chordalSq leftTrace.output rightTrace.output ≤
    (3 / 4 : ℚ) ^ blocks.length + 32 * epsilon
  linarith

theorem buildTrace_output_eq_front
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) :
    chain.buildTrace.output = chain.front := by
  cases chain with
  | nil matrix => rfl
  | cons head tail =>
      cases tail <;> rfl

/-- The displayed output of every finite sampled chain is a genuine
projective coordinate. -/
theorem front_hasNonzeroCoordinate
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    (chain : SampleChain box outer blocks) :
    chain.front.HasNonzeroCoordinate := by
  let built := chain.buildTrace
  have valid := built.trace.output_hasNonzeroCoordinate built.terminalValid
  rw [chain.buildTrace_output_eq_front] at valid
  exact valid

/-- One materialized trace used as the center of a finite, word-tagged
projective envelope.  The tag is kept outside this generic structure: the
center is numerical observation data and is not identified with the formal
canonical truncation. -/
structure StableEnvelope
    (box : RatBox) (outer : Mat2 QI) (blocks : List DecoderBlock)
    (epsilon : ℚ) where
  anchor : SampleChain box outer blocks
  epsilonNonnegative : 0 ≤ epsilon
  anchorLinks : anchor.LinksBound epsilon

namespace StableEnvelope

/-- Exact squared-chordal radius supplied by completed-block contraction and
the common per-link observation error. -/
def radiusSq
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    {epsilon : ℚ} (_envelope : StableEnvelope box outer blocks epsilon) : ℚ :=
  (3 / 4 : ℚ) ^ blocks.length + 32 * epsilon

theorem radiusSq_nonneg
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    {epsilon : ℚ} (envelope : StableEnvelope box outer blocks epsilon) :
    0 ≤ envelope.radiusSq := by
  exact add_nonneg (pow_nonneg (by norm_num) blocks.length)
    (mul_nonneg (by norm_num) envelope.epsilonNonnegative)

/-- Membership means proximity to the chosen materialized observation trace,
not proximity to the formal canonical boundary coordinate. -/
def Contains
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    {epsilon : ℚ} (envelope : StableEnvelope box outer blocks epsilon)
    (candidate : SampleChain box outer blocks) : Prop :=
  chordalSq envelope.anchor.front candidate.front ≤ envelope.radiusSq

/-- Every independently sampled trace satisfying the same link request lies
in the finite envelope. -/
theorem contains_of_links
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    {epsilon : ℚ} (envelope : StableEnvelope box outer blocks epsilon)
    (candidate : SampleChain box outer blocks)
    (candidateLinks : candidate.LinksBound epsilon) :
    envelope.Contains candidate := by
  have bound := buildBoundedTrace_pair_chordalSq_le envelope.anchor candidate
    envelope.epsilonNonnegative envelope.anchorLinks candidateLinks
  rw [(envelope.anchor.buildBoundedTrace epsilon
      envelope.epsilonNonnegative envelope.anchorLinks).output_eq,
    (candidate.buildBoundedTrace epsilon
      envelope.epsilonNonnegative candidateLinks).output_eq] at bound
  exact bound

end StableEnvelope

end SampleChain

/-- A provider that reconstructs the whole finite observation chain in every
later refinement of one winding state. -/
structure PersistentObservationChain
    {p : GaussianPolynomial} {ambient : RatBox}
    (outer : Mat2 QI) (blocks : List DecoderBlock)
    (current : WindingOneState p ambient) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines current.box → SampleChain next.box outer blocks

namespace PersistentObservationChain

/-- Transport only the finite block-list index. -/
def castBlocks
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer : Mat2 QI} {first second : List DecoderBlock}
    {current : WindingOneState p ambient}
    (history : PersistentObservationChain outer first current)
    (blocksEq : first = second) :
    PersistentObservationChain outer second current := by
  rw [← blocksEq]
  exact history

/-- Empty observation history at any decoder matrix. -/
def nil
    {p : GaussianPolynomial} {ambient : RatBox}
    (outer : Mat2 QI) (current : WindingOneState p ambient) :
    PersistentObservationChain outer [] current where
  sample _next _nextRefines := .nil outer

/-- Restrict all providers to a smaller current winding box. -/
def refine
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer : Mat2 QI} {blocks : List DecoderBlock}
    {current next : WindingOneState p ambient}
    (history : PersistentObservationChain outer blocks current)
    (nextRefines : next.box.Refines current.box) :
    PersistentObservationChain outer blocks next where
  sample later laterRefines :=
    history.sample later (laterRefines.trans nextRefines)

/-- Append independently persistent inner observations. -/
def append
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer : Mat2 QI} {first second : List DecoderBlock}
    {current : WindingOneState p ambient}
    (left : PersistentObservationChain outer first current)
    (right : PersistentObservationChain
      (DecoderBlock.matrixProduct outer first) second current) :
    PersistentObservationChain outer (first ++ second) current where
  sample next nextRefines :=
    (left.sample next nextRefines).append (right.sample next nextRefines)

/-- Specialization of `append` to one newly completed final block. -/
def appendSingleton
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer : Mat2 QI} {blocks : List DecoderBlock}
    {current : WindingOneState p ambient} {block : DecoderBlock}
    (history : PersistentObservationChain outer blocks current)
    (provider : (next : WindingOneState p ambient) →
      next.box.Refines current.box →
        BlockObservationSample
          (DecoderBlock.matrixProduct outer blocks) block next.box) :
    PersistentObservationChain outer (blocks ++ [block]) current :=
  history.append
    { sample := fun next nextRefines =>
        SampleChain.singleton (provider next nextRefines) }

/-- Materialize the persistent providers as a certified finite projective
envelope once the winding box meets their joint rational stability request. -/
def stableEnvelope
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer : Mat2 QI} {blocks : List DecoderBlock}
    {current next : WindingOneState p ambient}
    (history : PersistentObservationChain outer blocks current)
    (nextRefines : next.box.Refines current.box)
    (outerDeterminantNonzero : outer.det ≠ 0)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (boxBound : next.box.diagonalSq ≤
      SampleChain.stabilityRequest outer blocks epsilon ^ 2) :
    SampleChain.StableEnvelope next.box outer blocks epsilon where
  anchor := history.sample next nextRefines
  epsilonNonnegative := epsilonPositive.le
  anchorLinks := SampleChain.linksBound_of_boxBound
    (history.sample next nextRefines) outerDeterminantNonzero epsilonPositive
      boxBound

end PersistentObservationChain

end CCLPersistentBlockObservations
end FTA
