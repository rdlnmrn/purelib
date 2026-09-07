import FTA.CCLDenominator
import FTA.CCLFormulaPullback

/-!
# Finite exclusion of isolated CCL terminal inputs

After two sector bits, failure of the uniquely compatible third child can
occur at one zero-residual affine tail.  Its decoder image is an isolated
rational point, not a nondegenerate generalized circle.  This module
computes both possible terminal images, returns an exact polynomial root when
one is a root, and otherwise refines the winding-one track until both are
outside the retained box.
-/

namespace FTA
namespace CCLTerminalSeparation

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.CCLDenominator
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Candidate zero-residual affine tail for a proposed third sector bit.
Other parser phases have no isolated terminal candidate. -/
def terminalBeforeForBit? (state : RawParser.State) (bit : Bool) : Option QI :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      some (terminalBefore kind exponent
        (RawParser.sectorOfBits first second bit))
  | _ => none

/-- Decoder image of one candidate terminal tail, provided that image is
affine.  A decoder-pole candidate is omitted because it has no rational input
coordinate and was already handled by denominator separation. -/
def terminalInputForBit? (state : RawParser.State) (bit : Bool) : Option QI :=
  match terminalBeforeForBit? state bit with
  | none => none
  | some before =>
      if state.matrix.c * before + state.matrix.d = 0 then none
      else some (RatBox.homographic state.matrix before)

theorem terminalInputForBit_eq_some
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second bit : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (denominator :
      state.matrix.c * terminalBefore kind exponent
          (RawParser.sectorOfBits first second bit) + state.matrix.d ≠ 0) :
    terminalInputForBit? state bit = some
      (RatBox.homographic state.matrix
        (terminalBefore kind exponent
          (RawParser.sectorOfBits first second bit))) := by
  rw [terminalInputForBit?, terminalBeforeForBit?, phase]
  simp only
  rw [if_neg denominator]

/-- The local affine numerator of a completed-sector residual is genuinely
nonconstant. -/
theorem residualAffineCoefficient_ne
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    let matrix := normalizedMatrix kind exponent RawParser.identityMatrix
    matrix.a - sector.rep * matrix.c ≠ 0 := by
  dsimp only
  cases kind with
  | initialHigh =>
      simpa [normalizedMatrix, normalizationMatrix, RawParser.identityMatrix,
        Mat2.mul, Mat2.scale] using
          inv_ne_zero (RawParser.natPow_gamma_ne exponent)
  | initialLow =>
      simpa [normalizedMatrix, normalizationMatrix, RawParser.identityMatrix,
        Mat2.mul, Mat2.scale] using RawParser.natPow_gamma_ne exponent
  | loop =>
      simpa [normalizedMatrix, normalizationMatrix, RawParser.identityMatrix,
        Mat2.mul, Mat2.scale] using
          inv_ne_zero (RawParser.natPow_gamma_ne exponent)

/-- An affine terminal image is the unique zero of the corresponding
pulled-back squared residual numerator.  The theorem retains the explicit
nonzero linear coefficient needed for quantitative distance estimates. -/
theorem terminalInputForBit_affineResidual
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second bit : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (determinantNonzero : determinant state.matrix ≠ 0)
    {point : QI} (terminal : terminalInputForBit? state bit = some point) :
    let sector := RawParser.sectorOfBits first second bit
    let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
    let u := normalized.a - sector.rep * normalized.c
    let v := normalized.b - sector.rep * normalized.d
    let inverse := adjugate state.matrix
    let transformedU := u * inverse.a + v * inverse.c
    let transformedV := u * inverse.b + v * inverse.d
    transformedU ≠ 0 ∧
      transformedU * point + transformedV = 0 ∧
      pullbackForm inverse (residualForm kind exponent sector) =
        affineNormForm transformedU transformedV := by
  let sector := RawParser.sectorOfBits first second bit
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let u := normalized.a - sector.rep * normalized.c
  let v := normalized.b - sector.rep * normalized.d
  let inverse := adjugate state.matrix
  let transformedU := u * inverse.a + v * inverse.c
  let transformedV := u * inverse.b + v * inverse.d
  have terminalExpanded :
      (if state.matrix.c * terminalBefore kind exponent sector +
          state.matrix.d = 0 then none
        else some (RatBox.homographic state.matrix
          (terminalBefore kind exponent sector))) = some point := by
    simpa only [terminalInputForBit?, terminalBeforeForBit?, phase, sector]
      using terminal
  have forwardDenominator :
      state.matrix.c * terminalBefore kind exponent sector +
        state.matrix.d ≠ 0 := by
    intro zero
    rw [if_pos zero] at terminalExpanded
    contradiction
  rw [if_neg forwardDenominator] at terminalExpanded
  have pointEq : RatBox.homographic state.matrix
      (terminalBefore kind exponent sector) = point :=
    Option.some.inj terminalExpanded
  have inverseDenominator :
      inverse.c * point + inverse.d ≠ 0 := by
    rw [← pointEq]
    exact adjugate_denominator_homographic_ne state.matrix
      (terminalBefore kind exponent sector) determinantNonzero
        forwardDenominator
  have inversePoint : RatBox.homographic inverse point =
      terminalBefore kind exponent sector := by
    rw [← pointEq]
    exact homographic_adjugate_forward_inverse state.matrix
      (terminalBefore kind exponent sector) determinantNonzero
        forwardDenominator
  have residualZero :
      (residualForm kind exponent sector).eval
        (terminalBefore kind exponent sector) = 0 := by
    rw [eval_residualForm, normalizedValue_terminalBefore, sub_self,
      normSq_zero]
  have pulledZero :
      (pullbackForm inverse (residualForm kind exponent sector)).eval point =
        0 := by
    rw [eval_pullbackForm inverse (residualForm kind exponent sector) point
      inverseDenominator, inversePoint, residualZero]
    simp
  have residualShape : residualForm kind exponent sector =
      affineNormForm u v := by
    rfl
  have pullbackShape :
      pullbackForm inverse (residualForm kind exponent sector) =
        affineNormForm transformedU transformedV := by
    rw [residualShape, pullbackForm_affineNorm]
  have numeratorZero : transformedU * point + transformedV = 0 := by
    rw [pullbackShape, eval_affineNormForm] at pulledZero
    exact normSq_eq_zero.mp pulledZero
  have inverseDeterminantNonzero : determinant inverse ≠ 0 := by
    intro zero
    apply determinantNonzero
    dsimp only [inverse, determinant, adjugate] at zero
    simp only [neg_mul, mul_neg, neg_neg] at zero
    change state.matrix.d * state.matrix.a -
      state.matrix.b * state.matrix.c = 0 at zero
    rw [GaussianRat.mul_comm state.matrix.d state.matrix.a] at zero
    exact zero
  have localCoefficientNonzero : u ≠ 0 := by
    simpa only [u, normalized] using
      residualAffineCoefficient_ne kind exponent sector
  exact ⟨pullbackAffineCoefficient_ne_of_root inverse u v point
      inverseDeterminantNonzero localCoefficientNonzero numeratorZero,
    numeratorZero, pullbackShape⟩

/-- If the completed-sector terminal has no affine input image, the
pulled-back residual numerator is a nonzero constant.  This is the projective
counterpart of `terminalInputForBit_affineResidual`. -/
theorem terminalInputForBit_none_affineResidual
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second bit : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (determinantNonzero : determinant state.matrix ≠ 0)
    (terminal : terminalInputForBit? state bit = none) :
    let sector := RawParser.sectorOfBits first second bit
    let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
    let u := normalized.a - sector.rep * normalized.c
    let v := normalized.b - sector.rep * normalized.d
    let inverse := adjugate state.matrix
    let transformedU := u * inverse.a + v * inverse.c
    let transformedV := u * inverse.b + v * inverse.d
    transformedU = 0 ∧ transformedV ≠ 0 ∧
      pullbackForm inverse (residualForm kind exponent sector) =
        affineNormForm 0 transformedV := by
  let sector := RawParser.sectorOfBits first second bit
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let u := normalized.a - sector.rep * normalized.c
  let v := normalized.b - sector.rep * normalized.d
  let inverse := adjugate state.matrix
  let transformedU := u * inverse.a + v * inverse.c
  let transformedV := u * inverse.b + v * inverse.d
  have terminalExpanded :
      (if state.matrix.c * terminalBefore kind exponent sector +
          state.matrix.d = 0 then none
        else some (RatBox.homographic state.matrix
          (terminalBefore kind exponent sector))) = none := by
    simpa only [terminalInputForBit?, terminalBeforeForBit?, phase, sector]
      using terminal
  have forwardDenominatorZero :
      state.matrix.c * terminalBefore kind exponent sector +
        state.matrix.d = 0 := by
    by_contra nonzero
    rw [if_neg nonzero] at terminalExpanded
    contradiction
  have localNumeratorZero :
      u * terminalBefore kind exponent sector + v = 0 := by
    have residualZero :
        (residualForm kind exponent sector).eval
          (terminalBefore kind exponent sector) = 0 := by
      rw [eval_residualForm, normalizedValue_terminalBefore, sub_self,
        normSq_zero]
    change (affineNormForm u v).eval
      (terminalBefore kind exponent sector) = 0 at residualZero
    rw [eval_affineNormForm] at residualZero
    exact normSq_eq_zero.mp residualZero
  have transformedUZero : transformedU = 0 := by
    have crossZero :
        u * (state.matrix.c * terminalBefore kind exponent sector +
            state.matrix.d) -
          state.matrix.c *
            (u * terminalBefore kind exponent sector + v) = 0 := by
      rw [forwardDenominatorZero, localNumeratorZero]
      simp
    calc
      transformedU =
          u * (state.matrix.c * terminalBefore kind exponent sector +
              state.matrix.d) -
            state.matrix.c *
              (u * terminalBefore kind exponent sector + v) := by
        dsimp only [transformedU, inverse, adjugate]
        apply GaussianRat.ext <;>
          simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, neg_re,
            neg_im] <;>
          ring
      _ = 0 := crossZero
  have inverseDeterminantNonzero : determinant inverse ≠ 0 := by
    intro zero
    apply determinantNonzero
    dsimp only [inverse, determinant, adjugate] at zero
    simp only [neg_mul, mul_neg, neg_neg] at zero
    change state.matrix.d * state.matrix.a -
      state.matrix.b * state.matrix.c = 0 at zero
    rw [GaussianRat.mul_comm state.matrix.d state.matrix.a] at zero
    exact zero
  have localCoefficientNonzero : u ≠ 0 := by
    simpa only [u, normalized] using
      residualAffineCoefficient_ne kind exponent sector
  have transformedVNonzero : transformedV ≠ 0 := by
    rcases pullbackAffinePair_ne inverse u v inverseDeterminantNonzero
        localCoefficientNonzero with left | right
    · exact (left transformedUZero).elim
    · exact right
  have pullbackShape :
      pullbackForm inverse (residualForm kind exponent sector) =
        affineNormForm transformedU transformedV := by
    change pullbackForm inverse (affineNormForm u v) = _
    exact pullbackForm_affineNorm inverse u v
  refine ⟨transformedUZero, transformedVNonzero, ?_⟩
  simpa only [transformedUZero] using pullbackShape

/-- Failure of both pulled-back children at a currently valid affine input
identifies that input with one of the two computable terminal images. -/
theorem exists_terminalInputForBit_eq_some_of_no_children
    (state : RawParser.State) (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0)
    (current : state.Holds
      (RatBox.homographic (adjugate state.matrix) input))
    (none : ∀ bit, ¬(inputAdvanceFormula state bit).Holds input) :
    ∃ bit, terminalInputForBit? state bit = some input := by
  have terminal := terminalSectorAt_of_no_inputAdvanceFormula state input
    inverseDenominator current none
  rcases terminal with
    ⟨kind, exponent, first, second, third, phase, _full, residualZero⟩
  let sector := RawParser.sectorOfBits first second third
  let inverseTail := RatBox.homographic (adjugate state.matrix) input
  have inverseTailEq : inverseTail = terminalBefore kind exponent sector :=
    eq_terminalBefore_of_normalizedValue_eq kind exponent sector inverseTail
      (by simpa only [inverseTail, sector] using residualZero)
  have terminalDenominator :
      state.matrix.c * terminalBefore kind exponent sector +
          state.matrix.d ≠ 0 := by
    rw [← inverseTailEq]
    exact denominator_inverse_tail_ne state.matrix input determinantNonzero
      inverseDenominator
  have decoded : RatBox.homographic state.matrix
      (terminalBefore kind exponent sector) = input := by
    rw [← inverseTailEq]
    exact homographic_adjugate_inverse state.matrix input determinantNonzero
      inverseDenominator
  refine ⟨third, ?_⟩
  rw [terminalInputForBit_eq_some state kind exponent first second third phase
    (by simpa only [sector] using terminalDenominator)]
  rw [show RatBox.homographic state.matrix
      (terminalBefore kind exponent
        (RawParser.sectorOfBits first second third)) = input by
    simpa only [sector] using decoded]

/-- A nested winding-one state excluding every affine terminal candidate in
the displayed finite bit list. -/
structure SeparationOutput
    (p : GaussianPolynomial) (ambient : RatBox)
    (state : RawParser.State) (current : WindingOneState p ambient)
    (bits : List Bool) where
  numerical : WindingOneState p ambient
  refines : numerical.box.Refines current.box
  excludes : ∀ bit ∈ bits, ∀ {point : QI},
    terminalInputForBit? state bit = some point →
      ¬numerical.box.Contains point

/-- Exact root-or-separated result of the finite terminal candidate scan. -/
inductive Decision
    (p : GaussianPolynomial) (ambient : RatBox)
    (state : RawParser.State) (current : WindingOneState p ambient)
    (bits : List Bool) where
  | terminal (point : QI) (root : p.eval point = 0)
      (contains : current.box.Contains point)
  | separated (output : SeparationOutput p ambient state current bits)

/-- Scan a finite list of candidate bits.  Every nonroot image costs one
explicit `refineAwayFromNonroot` call; omitted projective candidates cost
nothing. -/
def separateList
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) (state : RawParser.State)
    (current : WindingOneState p ambient) (bits : List Bool) :
    Decision p ambient state current bits :=
  match bits with
  | [] =>
      .separated
        { numerical := current
          refines := RatBox.refines_refl current.box
          excludes := by simp }
  | bit :: rest =>
      match candidateEq : terminalInputForBit? state bit with
      | none =>
          match separateList track state current rest with
          | .terminal point root contains => .terminal point root contains
          | .separated output =>
              .separated
                { numerical := output.numerical
                  refines := output.refines
                  excludes := by
                    intro other member point pointEq
                    rcases List.mem_cons.mp member with rfl | restMember
                    · rw [candidateEq] at pointEq
                      contradiction
                    · exact output.excludes other restMember pointEq }
      | some point =>
          if root : p.eval point = 0 then
            if contains : current.box.Contains point then
              .terminal point root contains
            else
              match separateList track state current rest with
              | .terminal terminalPoint terminalRoot terminalContains =>
                  .terminal terminalPoint terminalRoot terminalContains
              | .separated output =>
                  .separated
                    { numerical := output.numerical
                      refines := output.refines
                      excludes := by
                        intro other member otherPoint otherPointEq
                        rcases List.mem_cons.mp member with rfl | restMember
                        · have pointEquality : otherPoint = point := by
                            rw [candidateEq] at otherPointEq
                            exact Option.some.inj otherPointEq.symm
                          subst otherPoint
                          exact fun inside =>
                            contains (output.refines.contains inside)
                        · exact output.excludes other restMember otherPointEq }
          else
            let next := refineAwayFromNonroot track current point root
            match separateList track state next rest with
            | .terminal terminalPoint terminalRoot terminalContains =>
                .terminal terminalPoint terminalRoot
                  ((refineAwayFromNonroot_refines track current point root).contains
                    terminalContains)
            | .separated output =>
                .separated
                  { numerical := output.numerical
                    refines := output.refines.trans
                      (refineAwayFromNonroot_refines track current point root)
                    excludes := by
                      intro other member otherPoint otherPointEq
                      rcases List.mem_cons.mp member with rfl | restMember
                      · have pointEquality : otherPoint = point := by
                          rw [candidateEq] at otherPointEq
                          exact Option.some.inj otherPointEq.symm
                        subst otherPoint
                        intro contains
                        exact refineAwayFromNonroot_excludes track current
                          point root (output.refines.contains contains)
                      · exact output.excludes other restMember otherPointEq }
termination_by bits.length

/-- Scan exactly the two Boolean third-bit candidates. -/
def separate
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) (state : RawParser.State)
    (current : WindingOneState p ambient) :
    Decision p ambient state current [false, true] :=
  separateList track state current [false, true]

/-- The two-candidate output excludes any input at which the current formula
holds but both child formulas fail. -/
theorem SeparationOutput.excludes_no_children
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : RawParser.State} {current : WindingOneState p ambient}
    (output : SeparationOutput p ambient state current [false, true])
    (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0)
    (currentHolds : state.Holds
      (RatBox.homographic (adjugate state.matrix) input))
    (none : ∀ bit, ¬(inputAdvanceFormula state bit).Holds input) :
    ¬output.numerical.box.Contains input := by
  rcases exists_terminalInputForBit_eq_some_of_no_children state input
      determinantNonzero inverseDenominator currentHolds none with
    ⟨bit, terminalInput⟩
  apply output.excludes bit (by cases bit <;> simp) terminalInput

/-- Terminal separation excludes the zero-residual completed-sector tail
itself, independently of the parser's retained history.  This weaker form is
the one needed by the active-phase persistence invariant. -/
theorem SeparationOutput.excludes_terminalSectorAt
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : RawParser.State} {current : WindingOneState p ambient}
    (output : SeparationOutput p ambient state current [false, true])
    (input : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (inside : output.numerical.box.Contains input) :
    ¬CCL.EncoderParserBridge.TerminalSectorAt state
      (RatBox.homographic (adjugate state.matrix) input) := by
  intro terminal
  rcases terminal with
    ⟨kind, exponent, first, second, third, phase, _full, residualZero⟩
  let sector := RawParser.sectorOfBits first second third
  let before := RatBox.homographic (adjugate state.matrix) input
  have beforeEq : before = terminalBefore kind exponent sector := by
    apply eq_terminalBefore_of_normalizedValue_eq kind exponent sector before
    simpa only [before, sector] using residualZero
  have forwardDenominator :
      RawParserSemantics.denominator state.matrix before ≠ 0 :=
    denominator_inverse_tail_ne state.matrix input determinantNonzero
      inverseDenominator
  have decoded : RatBox.homographic state.matrix before = input :=
    homographic_adjugate_inverse state.matrix input determinantNonzero
      inverseDenominator
  have terminalDenominator :
      state.matrix.c * terminalBefore kind exponent sector +
        state.matrix.d ≠ 0 := by
    simpa only [RawParserSemantics.denominator, ← beforeEq] using
      forwardDenominator
  have terminalInput := terminalInputForBit_eq_some state kind exponent first
    second third phase (by simpa only [sector] using terminalDenominator)
  have terminalPoint :
      RatBox.homographic state.matrix
        (terminalBefore kind exponent sector) = input := by
    rw [← beforeEq]
    exact decoded
  rw [show RawParser.sectorOfBits first second third = sector by rfl,
    terminalPoint] at terminalInput
  exact output.excludes third (by cases third <;> simp) terminalInput inside

end CCLTerminalSeparation
end FTA
