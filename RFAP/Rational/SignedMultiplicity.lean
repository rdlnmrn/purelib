import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.CoprimeBounds
import RFAP.Winding.Multiplicity
import RFAP.Rational.Winding

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace RFAP.SignedMultiplicity

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev PositiveEntry := RFAP.Multiplicity.PositiveEntry
abbrev PositiveContext :=
  RFAP.MultiplicityWinding.PositiveContext
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.Winding

/-! ## Pairwise separation witnesses for exact and track sites -/

/-- Two displayed exact roots of coprime factors are distinct. -/
theorem exactPoints_ne
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (leftRoot : p.eval left = 0) (rightRoot : q.eval right = 0) :
    left ≠ right := by
  intro equal
  subst right
  rcases coprime.eval_ne_zero left with leftNonzero | rightNonzero
  · exact leftNonzero leftRoot
  · exact rightNonzero rightRoot

/-- A finite refined track box that excludes one displayed exact root of a
coprime factor. -/
structure ExactTrackSeparation
    {trackPolynomial exactPolynomial : GaussianPolynomial}
    {ambient : Box}
    (track : WindingOneTrack trackPolynomial ambient)
    (current : WindingOneState trackPolynomial ambient)
    (point : RFAP.ConstructiveGaussian.Gaussian) where
  state : WindingOneState trackPolynomial ambient
  excludes : ¬state.box.Contains point

def separateExactFromTrack
    {trackPolynomial exactPolynomial : GaussianPolynomial}
    {ambient : Box}
    (trackDegreePositive : 0 < trackPolynomial.natDegree)
    (coprime : CoprimeCertificate trackPolynomial exactPolynomial)
    (track : WindingOneTrack trackPolynomial ambient)
    (current : WindingOneState trackPolynomial ambient)
    (point : RFAP.ConstructiveGaussian.Gaussian)
    (exactRoot : exactPolynomial.eval point = 0) :
    ExactTrackSeparation (exactPolynomial := exactPolynomial)
      track current point := by
  let state := RFAP.CoprimeBounds.protectedState
    coprime track current
  refine ⟨state, ?_⟩
  intro inside
  have lower := RFAP.CoprimeBounds.protectedState_right_lower
    trackDegreePositive coprime track current inside
  rw [exactRoot, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at lower
  exact (not_lt_of_ge lower
    (RFAP.CoprimeBounds.rightMargin_pos coprime ambient)).elim

/-- Explicit pair-dependent refinements witnessing separation of two
coprime shrinking tracks.  These finite witnesses establish distinct sites;
all later refinements preserve the separation. -/
structure TrackPairSeparation
    {p q : GaussianPolynomial} {pAmbient qAmbient : Box}
    (pTrack : WindingOneTrack p pAmbient)
    (pCurrent : WindingOneState p pAmbient)
    (qTrack : WindingOneTrack q qAmbient)
    (qCurrent : WindingOneState q qAmbient) where
  left : WindingOneState p pAmbient
  right : WindingOneState q qAmbient
  separated : left.box.Separated right.box

def separateTracks
    {p q : GaussianPolynomial} {pAmbient qAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (pTrack : WindingOneTrack p pAmbient)
    (pCurrent : WindingOneState p pAmbient)
    (qTrack : WindingOneTrack q qAmbient)
    (qCurrent : WindingOneState q qAmbient) :
    TrackPairSeparation pTrack pCurrent qTrack qCurrent :=
  let left := RFAP.CoprimeBounds.protectedState
    coprime pTrack pCurrent
  let right := RFAP.CoprimeBounds.uniformlySmallState
    qTrack qCurrent
    (RFAP.CoprimeBounds.rightMargin coprime pAmbient)
    (RFAP.CoprimeBounds.rightMargin_pos coprime pAmbient)
  ⟨left, right,
    RFAP.CoprimeBounds.protectedState_separated_uniformlySmallState
      pDegreePositive qDegreePositive coprime pTrack pCurrent qTrack qCurrent⟩

/-- Input for one higher-degree multiplicity site.  `source` is the
normalized same-side cofactor represented by the complete multiplicity
decomposition; `opposite` is the other reduced cofactor. -/
structure TrackSiteInput
    (source opposite : GaussianPolynomial) where
  decomposition : RFAP.Factorization.Decomposition source
  pairwise : decomposition.positiveMultiplicityEntries.Pairwise
    fun left right => RFAP.Multiplicity.CoprimeRelation
      left.part right.part
  context : PositiveContext decomposition.positiveMultiplicityEntries
  oppositeNonzero : opposite.isZero = false
  focusOppositeCoprime :
    CoprimeCertificate context.focus.part.polynomial opposite
  track : WindingOneTrack context.focus.part.polynomial
    (RFAP.GlobalWinding.largeSquareBox
      context.focus.part.polynomial)
  current : WindingOneState context.focus.part.polynomial
    (RFAP.GlobalWinding.largeSquareBox
      context.focus.part.polynomial)

namespace TrackSiteInput

abbrev ambient
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) : Box :=
  RFAP.GlobalWinding.largeSquareBox
    input.context.focus.part.polynomial

def otherCoprime
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    CoprimeCertificate input.context.focus.part.polynomial
      (input.context.otherPolynomial input.decomposition) :=
  input.context.otherCoprime input.decomposition input.pairwise

theorem otherNonzero
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    (input.context.otherPolynomial input.decomposition).isZero = false :=
  input.context.otherPolynomial_nonzero input.decomposition

/-- One request no larger than either of the two separately computed
protection radii. -/
def protectionRequest
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) : Coordinate :=
  min
    (RFAP.CoprimeBounds.protectionRadius input.otherCoprime
      input.ambient)
    (RFAP.CoprimeBounds.protectionRadius
      input.focusOppositeCoprime input.ambient)

theorem protectionRequest_pos
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    0 < input.protectionRequest :=
  lt_min
    (RFAP.CoprimeBounds.protectionRadius_pos input.otherCoprime
      input.ambient)
    (RFAP.CoprimeBounds.protectionRadius_pos
      input.focusOppositeCoprime input.ambient)

theorem protectionRequest_le_other
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    input.protectionRequest ≤
      RFAP.CoprimeBounds.protectionRadius input.otherCoprime
        input.ambient :=
  min_le_left _ _

theorem protectionRequest_le_opposite
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    input.protectionRequest ≤
      RFAP.CoprimeBounds.protectionRadius
        input.focusOppositeCoprime input.ambient :=
  min_le_right _ _

/-- The one jointly protected observation of the focused shrinking track. -/
def state
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    WindingOneState input.context.focus.part.polynomial input.ambient :=
  RFAP.CoprimeBounds.protectedStateAt input.track input.current
    input.protectionRequest input.protectionRequest_pos

def otherClearance
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    BoundaryClearance (input.context.otherPolynomial input.decomposition)
      input.state.box :=
  RFAP.CoprimeBounds.protectedStateAt_rightBoundaryClearance
    input.context.focus.degreePositive input.otherCoprime input.track
    input.current input.protectionRequest_pos input.protectionRequest_le_other

def oppositeClearance
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    BoundaryClearance opposite input.state.box :=
  RFAP.CoprimeBounds.protectedStateAt_rightBoundaryClearance
    input.context.focus.degreePositive input.focusOppositeCoprime input.track
    input.current input.protectionRequest_pos
    input.protectionRequest_le_opposite

theorem otherWinding_zero
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    quadrupledBoxWinding
      (input.context.otherPolynomial input.decomposition) input.state.box = 0 :=
  RFAP.CoprimeBounds.protectedStateAt_rightWinding_zero_of_nonzero
    input.context.focus.degreePositive input.otherNonzero input.otherCoprime
    input.track input.current input.protectionRequest_pos
    input.protectionRequest_le_other

theorem oppositeWinding_zero
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    quadrupledBoxWinding opposite input.state.box = 0 :=
  RFAP.CoprimeBounds.protectedStateAt_rightWinding_zero_of_nonzero
    input.context.focus.degreePositive input.oppositeNonzero
    input.focusOppositeCoprime input.track input.current
    input.protectionRequest_pos input.protectionRequest_le_opposite

/-- The factored same-side numerator used for the local quotient winding.
Its evaluation is certified equal to `source` by
`representedFactorization`. -/
def representedSource
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) : GaussianPolynomial :=
  RFAP.Multiplicity.polynomialPower
      input.context.focus.part.polynomial input.context.focus.multiplicity *
    input.context.otherPolynomial input.decomposition

theorem representedFactorization
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    RFAP.Factorization.ProductIdentity source
      (RFAP.Multiplicity.polynomialPower
        input.context.focus.part.polynomial input.context.focus.multiplicity)
      (input.context.otherPolynomial input.decomposition) :=
  input.context.multiplicityFactorization input.decomposition rfl

def representedSourceClearance
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    BoundaryClearance input.representedSource input.state.box :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.MultiplicityWinding.polynomialPower_boundaryClearance
      input.state.clearance input.context.focus.multiplicity)
    input.otherClearance

theorem representedSourceWinding
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    quadrupledBoxWinding input.representedSource input.state.box =
      (4 : Int) * input.context.focus.multiplicity := by
  have powerWinding :=
    RFAP.MultiplicityWinding.quadrupledBoxWinding_polynomialPower
      input.state.proper input.state.clearance input.context.focus.multiplicity
  have productWinding :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (RFAP.Multiplicity.polynomialPower
        input.context.focus.part.polynomial input.context.focus.multiplicity)
      (input.context.otherPolynomial input.decomposition) input.state.box
      input.state.proper
      (RFAP.MultiplicityWinding.polynomialPower_boundaryClearance
        input.state.clearance input.context.focus.multiplicity)
      input.otherClearance
  change quadrupledBoxWinding
      (RFAP.Multiplicity.polynomialPower
          input.context.focus.part.polynomial input.context.focus.multiplicity *
        input.context.otherPolynomial input.decomposition) input.state.box = _
  rw [productWinding, powerWinding, input.state.rawWindingFour,
    input.otherWinding_zero]
  ring1

/-- The local quotient represented by the exact weighted factorization has
raw winding `4m`; ordinary winding is therefore the positive multiplicity
`m`. -/
theorem representedRationalWinding
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    RFAP.RationalWinding.rationalQuadrupledWinding
        input.representedSource opposite input.state.box =
      (4 : Int) * input.context.focus.multiplicity := by
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.representedSource opposite input.state.box input.state.proper
      input.representedSourceClearance input.oppositeClearance
  rw [quotient, input.representedSourceWinding, input.oppositeWinding_zero]
  ring1

theorem representedBoxWinding
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    RFAP.RationalWinding.rationalBoxWinding
        input.representedSource opposite input.state.box =
      input.context.focus.multiplicity :=
  RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
    input.representedRationalWinding

/-- Reversing the displayed quotient makes the same protected site a pole
of signed multiplicity `-m`. -/
theorem representedPoleRationalWinding
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    RFAP.RationalWinding.rationalQuadrupledWinding
        opposite input.representedSource input.state.box =
      -(4 : Int) * input.context.focus.multiplicity := by
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      opposite input.representedSource input.state.box input.state.proper
      input.oppositeClearance input.representedSourceClearance
  rw [quotient, input.oppositeWinding_zero, input.representedSourceWinding]
  ring1

theorem representedPoleBoxWinding
    {source opposite : GaussianPolynomial}
    (input : TrackSiteInput source opposite) :
    RFAP.RationalWinding.rationalBoxWinding
        opposite input.representedSource input.state.box =
      -(input.context.focus.multiplicity : Int) := by
  apply RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [input.representedPoleRationalWinding]
  ring1

end TrackSiteInput

end RFAP.SignedMultiplicity
