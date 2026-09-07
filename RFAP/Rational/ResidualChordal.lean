import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.CoprimeBounds
import RFAP.Geometry.ResidualChordal

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace RFAP.RationalResidualChordal

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds

/-- Squared norm of the displayed quotient value.  Its quantitative theorems
carry a proof that the displayed denominator value is nonzero. -/
def quotientResidualSq
    (source opposite : GaussianPolynomial) (sample : Gaussian) : Coordinate :=
  normSq (source.eval sample / opposite.eval sample)

theorem quotientResidualSq_nonneg
    (source opposite : GaussianPolynomial) (sample : Gaussian) :
    0 ≤ quotientResidualSq source opposite sample :=
  normSq_nonneg _

/-- Square-root-free reciprocal estimate for positive constructive fractions. -/
theorem reciprocalQuotientLower
    {sourceNorm oppositeNorm epsilon : Coordinate}
    (sourcePositive : 0 < sourceNorm)
    (epsilonPositive : 0 < epsilon)
    (sourceStrict : sourceNorm < epsilon ^ 2 * oppositeNorm) :
    1 / epsilon ^ 2 ≤ oppositeNorm / sourceNorm := by
  have epsilonSquarePositive :=
    RFAP.ConstructiveFraction.pow_pos_direct epsilonPositive 2
  have multiplied : sourceNorm < oppositeNorm * epsilon ^ 2 := by
    rw [RFAP.ConstructiveFraction.mul_comm oppositeNorm (epsilon ^ 2)]
    exact sourceStrict
  have divided : sourceNorm / epsilon ^ 2 < oppositeNorm :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos epsilonSquarePositive).2
      multiplied
  apply (RFAP.ConstructiveFraction.le_div_iff_pos sourcePositive).2
  have rearranged : (1 / epsilon ^ 2) * sourceNorm =
      sourceNorm / epsilon ^ 2 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [RFAP.ConstructiveFraction.one_mul,
      RFAP.ConstructiveFraction.mul_comm]
  rw [rearranged]
  exact divided.le

/-- Finite data selecting one source RAT and the Bezout protection against
the coprime opposite polynomial.  At a zero site the source is the reduced
numerator; at a pole site it is the reduced denominator. -/
structure LocalQuotientContext
    (source opposite : GaussianPolynomial) (ambient : Box) where
  sourceDegreePositive : 0 < source.natDegree
  coprime : CoprimeCertificate source opposite
  track : WindingOneTrack source ambient
  current : WindingOneState source ambient

namespace LocalQuotientContext

variable {source opposite : GaussianPolynomial} {ambient : Box}

/-- The coefficient-computed protectedState source state. -/
def protectedState (context : LocalQuotientContext source opposite ambient) :
    WindingOneState source ambient :=
  RFAP.CoprimeBounds.protectedState context.coprime
    context.track context.current

/-- Uniform positive lower quadrance for the opposite polynomial. -/
def oppositeMargin
    (context : LocalQuotientContext source opposite ambient) : Coordinate :=
  RFAP.CoprimeBounds.rightMargin context.coprime ambient

theorem oppositeMargin_pos
    (context : LocalQuotientContext source opposite ambient) :
    0 < context.oppositeMargin :=
  RFAP.CoprimeBounds.rightMargin_pos context.coprime ambient

/-- Uniform finite upper quadrance for the opposite polynomial on the source
ambient box. -/
def oppositeMajorant
    (_context : LocalQuotientContext source opposite ambient) : Coordinate :=
  denseEvalNormMajorant opposite ambient

theorem oppositeMajorant_pos
    (context : LocalQuotientContext source opposite ambient) :
    0 < context.oppositeMajorant :=
  denseEvalNormMajorant_pos opposite ambient

theorem oppositeLower
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian} (inside : state.box.Contains sample) :
    context.oppositeMargin ≤ normSq (opposite.eval sample) := by
  exact RFAP.CoprimeBounds.protectedState_right_lower
    context.sourceDegreePositive context.coprime context.track context.current
    (refinesProtected.contains inside)

theorem oppositeNonzero
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian} (inside : state.box.Contains sample) :
    opposite.eval sample ≠ 0 := by
  intro evaluationZero
  have lower := context.oppositeLower refinesProtected inside
  rw [evaluationZero, normSq_zero] at lower
  exact (not_lt_of_ge lower context.oppositeMargin_pos).elim

theorem oppositeUpper
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    {sample : Gaussian} (inside : state.box.Contains sample) :
    normSq (opposite.eval sample) ≤ context.oppositeMajorant :=
  normSq_eval_le_denseEvalNormMajorant opposite
    (state.refinesAmbient.contains inside)

/-- Forward RFAP estimate at a zero site.  With source/opposite swapped it is
the shrinking reciprocal-residual estimate at a pole site. -/
theorem quotientResidualSq_le_diagonal
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian} (inside : state.box.Contains sample) :
    quotientResidualSq source opposite sample ≤
      (4 * denseLipschitzBound source ambient * state.box.diagonalSq) /
        context.oppositeMargin := by
  have oppositeNonzero := context.oppositeNonzero refinesProtected inside
  have lower := context.oppositeLower refinesProtected inside
  have sourceBound :=
    RFAP.CoprimeBounds.normSq_eval_le_four_lipschitz_diagonal
      context.sourceDegreePositive state inside
  have inverseOrder :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
      context.oppositeMargin_pos lower
  rw [quotientResidualSq, normSq_div _ _ oppositeNonzero,
    RFAP.ExplicitField.div_eq_mul_inv]
  exact
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inverseOrder
      (normSq_nonneg (source.eval sample))).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct sourceBound
      (RFAP.ConstructiveFraction.inv_pos_direct
        context.oppositeMargin_pos).le)

/-- The quotient residual target obtained by dividing the polynomial target
by the explicit opposite-polynomial majorant. -/
def quotientResidualTarget
    (context : LocalQuotientContext source opposite ambient)
    (squarefree : SquarefreeCertificate source)
    (state : WindingOneState source ambient)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  RFAP.ResidualChordal.residualTarget squarefree state sample
      epsilon /
    context.oppositeMajorant

theorem quotientResidualTarget_pos
    (context : LocalQuotientContext source opposite ambient)
    (squarefree : SquarefreeCertificate source)
    (state : WindingOneState source ambient)
    (sample : Gaussian) (strict : state.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < context.quotientResidualTarget squarefree state sample epsilon := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ResidualChordal.residualTarget_pos squarefree state sample
      strict epsilonPositive)
    context.oppositeMajorant_pos

theorem quotientResidualSq_mul_oppositeNorm
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian} (inside : state.box.Contains sample) :
    quotientResidualSq source opposite sample *
        normSq (opposite.eval sample) = normSq (source.eval sample) := by
  have oppositeNonzero := context.oppositeNonzero refinesProtected inside
  have valueIdentity :
      (source.eval sample / opposite.eval sample) * opposite.eval sample =
        source.eval sample :=
    RFAP.ExplicitField.div_mul_cancel _ oppositeNonzero
  have normIdentity := congrArg normSq valueIdentity
  rw [normSq_mul] at normIdentity
  exact normIdentity

theorem sourceResidual_le_quotientResidualSq_mul_majorant
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    {sample : Gaussian} (inside : state.box.Contains sample) :
    normSq (source.eval sample) ≤
      quotientResidualSq source opposite sample * context.oppositeMajorant := by
  have identity := context.quotientResidualSq_mul_oppositeNorm
    refinesProtected inside
  have upper := context.oppositeUpper inside
  calc
    normSq (source.eval sample) =
        quotientResidualSq source opposite sample *
          normSq (opposite.eval sample) := identity.symm
    _ ≤ quotientResidualSq source opposite sample * context.oppositeMajorant :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct upper
        (quotientResidualSq_nonneg source opposite sample)

theorem quotientResidualSq_mul_majorant_lt
    (context : LocalQuotientContext source opposite ambient)
    {target : Coordinate} {sample : Gaussian}
    (small : quotientResidualSq source opposite sample <
      target / context.oppositeMajorant) :
    quotientResidualSq source opposite sample * context.oppositeMajorant <
      target :=
  (RFAP.ConstructiveFraction.lt_div_iff_pos
    context.oppositeMajorant_pos).mp small

theorem sourceResidual_lt_of_quotientResidual_lt
    (context : LocalQuotientContext source opposite ambient)
    {state : WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (squarefree : SquarefreeCertificate source)
    (sample : Gaussian) (inside : state.box.Contains sample)
    {epsilon : Coordinate}
    (small : quotientResidualSq source opposite sample <
      context.quotientResidualTarget squarefree state sample epsilon) :
    normSq (source.eval sample) <
      RFAP.ResidualChordal.residualTarget squarefree state sample
        epsilon := by
  let target := RFAP.ResidualChordal.residualTarget squarefree state
    sample epsilon
  have upper := context.sourceResidual_le_quotientResidualSq_mul_majorant
    refinesProtected inside
  have scaled : quotientResidualSq source opposite sample *
      context.oppositeMajorant < target := by
    apply context.quotientResidualSq_mul_majorant_lt
    simpa only [target, quotientResidualTarget] using small
  calc
    normSq (source.eval sample) ≤
        quotientResidualSq source opposite sample * context.oppositeMajorant :=
      upper
    _ < target := scaled

/-- Converse RFAP estimate at a zero site, or at a pole site after swapping
the pair.  Small quotient residual constructs either the exact displayed
source zero or a nearby winding-one box and its `18 * epsilon^2` chordal
track. -/
def observeOfSmallQuotientResidual
    (context : LocalQuotientContext source opposite ambient)
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination : AxisEliminationCertificate source degreeBound)
    (state : WindingOneState source ambient)
    (refinesProtected : state.box.Refines context.protectedState.box)
    (sample : Gaussian) (strict : state.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (small : quotientResidualSq source opposite sample <
      context.quotientResidualTarget squarefree state sample epsilon) :
    RFAP.ResidualChordal.ResidualChordalObservation
      squarefree elimination state sample epsilon :=
  RFAP.ResidualChordal.observeOfResidual degreeAtLeastTwo
    squarefree elimination state sample strict epsilonPositive
      (context.sourceResidual_lt_of_quotientResidual_lt refinesProtected
        squarefree sample strict.contains small)

/-! ## Constructed epsilon residual states and pole blow-up -/

/-- Refine the protectedState source RAT far enough that its quotient residual is
strictly below `epsilon^2` everywhere in the returned box. -/
def epsilonResidualState
    (context : LocalQuotientContext source opposite ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    WindingOneState source ambient :=
  RFAP.CoprimeBounds.uniformlySmallState context.track
    context.protectedState (context.oppositeMargin * epsilon ^ 2)
    (RFAP.ConstructiveFraction.mul_pos_direct context.oppositeMargin_pos
      (RFAP.ConstructiveFraction.pow_pos_direct epsilonPositive 2))

theorem epsilonResidualState_refines
    (context : LocalQuotientContext source opposite ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (context.epsilonResidualState epsilon epsilonPositive).box.Refines
      context.protectedState.box := by
  exact context.track.nested context.protectedState _ _

theorem epsilonResidualState_quotientResidualSq_lt
    (context : LocalQuotientContext source opposite ambient)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    {sample : Gaussian}
    (inside : (context.epsilonResidualState epsilon epsilonPositive).box.Contains
      sample) :
    quotientResidualSq source opposite sample < epsilon ^ 2 := by
  let state := context.epsilonResidualState epsilon epsilonPositive
  let margin := context.oppositeMargin
  have sourceSmall : normSq (source.eval sample) < margin * epsilon ^ 2 :=
    RFAP.CoprimeBounds.uniformlySmallState_residual_lt
      context.sourceDegreePositive context.track context.protectedState
      (RFAP.ConstructiveFraction.mul_pos_direct context.oppositeMargin_pos
        (RFAP.ConstructiveFraction.pow_pos_direct epsilonPositive 2)) inside
  have refines := context.epsilonResidualState_refines epsilon epsilonPositive
  have oppositeNonzero := context.oppositeNonzero refines inside
  have lower := context.oppositeLower refines inside
  have identity := context.quotientResidualSq_mul_oppositeNorm refines inside
  have scaledLower : margin * epsilon ^ 2 ≤
      normSq (opposite.eval sample) * epsilon ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct lower
      (RFAP.ConstructiveFraction.pow_pos_direct epsilonPositive 2).le
  have productStrict :
      quotientResidualSq source opposite sample *
          normSq (opposite.eval sample) <
        epsilon ^ 2 * normSq (opposite.eval sample) := by
    calc
      quotientResidualSq source opposite sample *
          normSq (opposite.eval sample) = normSq (source.eval sample) :=
        identity
      _ < margin * epsilon ^ 2 := sourceSmall
      _ ≤ normSq (opposite.eval sample) * epsilon ^ 2 := scaledLower
      _ = epsilon ^ 2 * normSq (opposite.eval sample) := by ring1
  exact RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct productStrict
    (normSq_pos oppositeNonzero)

/-- At a pole context (source = denominator, opposite = numerator), a
non-exact displayed pole sample has quotient quadrance at least
`1 / epsilon^2`; an exact source zero is reported separately by decidable
evaluation. -/
theorem oppositeQuotientSq_ge_inv_epsilonSq
    (context : LocalQuotientContext source opposite ambient)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    {sample : Gaussian}
    (inside : (context.epsilonResidualState epsilon epsilonPositive).box.Contains
      sample)
    (sourceNonzero : source.eval sample ≠ 0) :
    1 / epsilon ^ 2 ≤ normSq (opposite.eval sample / source.eval sample) := by
  have refines := context.epsilonResidualState_refines epsilon epsilonPositive
  have oppositeNonzero := context.oppositeNonzero refines inside
  have reciprocalSmall :=
    context.epsilonResidualState_quotientResidualSq_lt epsilonPositive inside
  have identity := context.quotientResidualSq_mul_oppositeNorm refines inside
  have sourceStrict : normSq (source.eval sample) <
      epsilon ^ 2 * normSq (opposite.eval sample) := by
    calc
      normSq (source.eval sample) =
          quotientResidualSq source opposite sample *
            normSq (opposite.eval sample) := identity.symm
      _ < epsilon ^ 2 * normSq (opposite.eval sample) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct reciprocalSmall
          (normSq_pos oppositeNonzero)
  rw [normSq_div _ _ sourceNonzero]
  change 1 / epsilon ^ 2 ≤
    normSq (opposite.eval sample) / normSq (source.eval sample)
  exact reciprocalQuotientLower (normSq_pos sourceNonzero) epsilonPositive
    sourceStrict

end LocalQuotientContext

end RFAP.RationalResidualChordal
