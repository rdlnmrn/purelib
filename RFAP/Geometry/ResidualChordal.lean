import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.Chordal
import RFAP.Geometry.DyadicBracket
import RFAP.Winding.Residual

/-!
# Constructive residual-to-chordal winding boxes

A sufficiently small polynomial residual at a displayed Gaussian rational,
together with a containing winding-one state and finite squarefree and axis
elimination certificates, constructs a nearby winding-one box and its total
shrinking track.  No completed root is selected or asserted.
-/

namespace RFAP.ResidualChordal

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

/-- Minimal protected view used by the generalized residual constructor. -/
abbrev protectedAmbient
    {p : GaussianPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) :
    RFAP.ResidualWinding.ProtectedAmbient p ambient :=
  RFAP.ResidualWinding.ProtectedAmbient.ofWindingOne current

open RFAP.ConstructiveGaussian.Gaussian

/-- Reassociate a displayed division using only the explicit fraction
multiplication laws.  The generic field normalizer introduces an avoidable
choice dependency when an inverse occurs as an atom. -/
private theorem mul_div_reassociate (a b c : Coordinate) :
    a * (b / c) = (a / c) * b := by
  change a * (b * c⁻¹) = (a * c⁻¹) * b
  ring1

/-- Move a displayed factor across a displayed quotient without invoking a
generic inverse normalizer. -/
private theorem mul_mul_div_reassociate (a b c : Coordinate) :
    a * b / c = (b / c) * a := by
  change (a * b) * c⁻¹ = (b * c⁻¹) * a
  ring1

private theorem eighteen_mul_four : (18 : Coordinate) * 4 = 72 := by ring1

private theorem thirtyTwo_mul_four : (32 : Coordinate) * 4 = 128 := by ring1

/-- Paper-facing output of the local residual converse.  Every field is
finite data or a proof about displayed rational data. -/
structure ResidualChordalResult
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) where
  residualTarget : Coordinate
  residualTarget_eq : residualTarget =
    RFAP.ResidualWinding.anchoredResidualTarget
      squarefree (protectedAmbient current) sample epsilon
  residualTargetPositive : 0 < residualTarget
  radius : Coordinate
  radiusPositive : 0 < radius
  radiusLeRequested : radius <= epsilon
  state : WindingOneState p ambient
  stateStrictCurrent : state.box.StrictInterior current.box
  windingFour :
    RFAP.Winding.quadrupledBoxWinding p state.box = 4
  bandDiagonal : state.box.diagonalSq <= 32 * radius ^ 2
  diagonalBound : state.box.diagonalSq <= 32 * epsilon ^ 2
  track : WindingOneTrack p ambient
  trackInitial : track.initial = state
  bandNearSample : forall z, state.box.Contains z ->
    normSq (z - sample) <= 18 * radius ^ 2
  chordalBound : forall z, state.box.Contains z ->
    RFAP.Chordal.affineChordalSq sample z <= 18 * epsilon ^ 2

/-- The public residual observation distinguishes an exact displayed
Gaussian-rational zero from the genuinely approximate winding-box case. -/
inductive ResidualChordalObservation
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) : Type where
  | exact (evaluation : p.eval sample = 0)
  | band
      (result : ResidualChordalResult squarefree elimination current sample
        epsilon)

/-- The exact positive residual request used by the constructor. -/
def residualTarget
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  RFAP.ResidualWinding.anchoredResidualTarget
    squarefree (protectedAmbient current) sample epsilon

theorem residualTarget_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < residualTarget squarefree current sample epsilon := by
  exact RFAP.ResidualWinding.anchoredResidualTarget_pos
    squarefree (protectedAmbient current) sample strict epsilonPositive

/-- A displayed strict-interior sample below the computed positive residual
target constructs a nearby winding-one box and an ordinary shrinking RAT.
Every displayed point in the new box has squared chordal distance at most
`18 * epsilon^2` from the sample. -/
def ofResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      residualTarget squarefree current sample epsilon) :
    ResidualChordalResult squarefree elimination current sample epsilon := by
  let seed := RFAP.ResidualWinding.seedOfResidual squarefree
    elimination (protectedAmbient current) sample strict epsilonPositive
      residualSmall
  let state := seed.state degreeAtLeastTwo
  let track := seed.track degreeAtLeastTwo
  have radiusLe :=
    RFAP.ResidualWinding.seedOfResidual_radius_le_cap squarefree
      elimination (protectedAmbient current) sample strict epsilonPositive
        residualSmall
  have radiusSquareLe : seed.radius ^ 2 <= epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct seed.radiusPositive.le
      radiusLe 2
  have scaledRadiusSquare : 18 * seed.radius ^ 2 <= 18 * epsilon ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusSquareLe (by decide)
  exact
    { residualTarget := residualTarget squarefree current sample epsilon
      residualTarget_eq := rfl
      residualTargetPositive := residualTarget_pos squarefree current sample
        strict epsilonPositive
      radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := radiusLe
      state := state
      stateStrictCurrent := seed.state_strict_current degreeAtLeastTwo
      windingFour := (seed.state degreeAtLeastTwo).rawWindingFour
      bandDiagonal := by
        simpa only [state, RFAP.ResidualWinding.Seed.state,
          RFAP.ResidualWinding.Seed.band] using
            seed.band.diagonalSq_le seed.radiusPositive
      diagonalBound := by
        have bandDiagonal := seed.band.diagonalSq_le seed.radiusPositive
        have scaled : 32 * seed.radius ^ 2 <= 32 * epsilon ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe
              (RFAP.ConstructiveFraction.natCast_pos_direct
                (n := 32) (by decide)).le
        exact (by
          simpa only [state, RFAP.ResidualWinding.Seed.state,
            RFAP.ResidualWinding.Seed.band] using
              bandDiagonal.trans scaled)
      track := track
      trackInitial := rfl
      bandNearSample := by
        intro z inside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall inside
        simpa only [seed, state,
          RFAP.ResidualWinding.Seed.state,
          RFAP.ResidualWinding.Seed.band,
          RFAP.ResidualWinding.seedOfResidual,
          RFAP.ResidualWinding.AnchoredInput.seed,
          RFAP.ResidualWinding.anchoredInputOfResidual,
          RFAP.ResidualWinding.anchoredSquare_anchor] using distance
      chordalBound := by
        intro z inside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall inside
        have distanceFromSample : normSq (sample - z) <=
            18 * seed.radius ^ 2 := by
          have swapped : sample - z = -(z - sample) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
              ring1
          rw [swapped, normSq_neg]
          simpa only [seed, state,
            RFAP.ResidualWinding.Seed.state,
            RFAP.ResidualWinding.Seed.band,
            RFAP.ResidualWinding.seedOfResidual,
            RFAP.ResidualWinding.AnchoredInput.seed,
            RFAP.ResidualWinding.anchoredInputOfResidual,
            RFAP.ResidualWinding.anchoredSquare_anchor] using
              distance
        exact (RFAP.Chordal.affineChordalSq_le_normSq sample z).trans
          (distanceFromSample.trans scaledRadiusSquare) }

/-- Point-independent variant for an ordinarily contained sample.  The
boundary-clearance quarter first proves strict containment, then invokes the
same local constructor. -/
def ofUniformResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (contains : current.box.Contains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      RFAP.ResidualWinding.uniformAnchoredResidualTarget
        squarefree (protectedAmbient current) epsilon) :
    ResidualChordalResult squarefree elimination current sample epsilon := by
  have localized :=
    RFAP.ResidualWinding.uniform_residual_strict_and_anchored
      squarefree (protectedAmbient current) sample contains epsilonPositive
        residualSmall
  exact ofResidual degreeAtLeastTwo squarefree elimination current sample
    localized.1 epsilonPositive localized.2

/-- Exact evaluation is returned immediately; only a non-exact displayed
sample is packaged as a nearby winding-one band. -/
def observeOfResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      residualTarget squarefree current sample epsilon) :
    ResidualChordalObservation squarefree elimination current sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofResidual degreeAtLeastTwo squarefree elimination current sample
      strict epsilonPositive residualSmall)

/-- Point-independent public classifier for an ordinarily contained sample. -/
def observeOfUniformResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (contains : current.box.Contains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      RFAP.ResidualWinding.uniformAnchoredResidualTarget
        squarefree (protectedAmbient current) epsilon) :
    ResidualChordalObservation squarefree elimination current sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofUniformResidual degreeAtLeastTwo squarefree elimination current
      sample contains epsilonPositive residualSmall)

/-! ## Sharper dyadic residual-linear converse -/

/-- The positive coefficient scale common to the source-variation and
Newton-displacement residual budgets. -/
def linearResidualScale
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient) : Coordinate :=
  min
    (RFAP.LocalExtraction.derivativeMargin
      squarefree current.box)
    (2 * RFAP.PolynomialBounds.denseLipschitzBound
      p current.box)

theorem linearResidualScale_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient) :
    0 < linearResidualScale squarefree current := by
  exact lt_min
    (RFAP.LocalExtraction.derivativeMargin_pos
      squarefree current.box)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.PolynomialBounds.denseLipschitzBound_pos
        p current.box))

/-- The reference radius contains all geometric, derivative, and Taylor caps.
The sharper theorem asks the actual residual to be small enough that its
dyadic scale lies strictly below this radius. -/
def linearReferenceRadius
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) : Coordinate :=
  RFAP.ResidualWinding.anchoredRadius
    squarefree (protectedAmbient current) sample 1

theorem linearReferenceRadius_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample) :
    0 < linearReferenceRadius squarefree current sample := by
  exact RFAP.ResidualWinding.anchoredRadius_pos
    squarefree (protectedAmbient current) sample strict (by decide)

/-- Positive local smallness threshold for the residual-linear theorem.
The first term puts `R / mu` below one.  The second puts the factor-four
dyadic upper bracket below the complete safe reference radius. -/
def linearResidualThreshold
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) : Coordinate :=
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  min mu (mu * safe ^ 2 / 4)

theorem linearResidualThreshold_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample) :
    0 < linearResidualThreshold squarefree current sample := by
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  exact lt_min muPositive
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct muPositive
        (RFAP.ConstructiveFraction.pow_pos_direct safePositive 2))
      (by decide))

/-- Output of the local residual-linear converse.  The construction retains
the selected dyadic bracket in addition to the ordinary winding-one state and
track returned by `ResidualChordalResult`. -/
structure LinearResidualChordalResult
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) where
  radius : Coordinate
  radiusPositive : 0 < radius
  residualOverScale_lt_radiusSq :
    normSq (p.eval sample) / linearResidualScale squarefree current <
      radius ^ 2
  radiusSq_le_fourResidualOverScale :
    radius ^ 2 <=
      4 * (normSq (p.eval sample) / linearResidualScale squarefree current)
  construction :
    ResidualChordalResult squarefree elimination current sample radius
  chordalLinear : forall z, construction.state.box.Contains z ->
    RFAP.Chordal.affineChordalSq sample z <=
      (72 / linearResidualScale squarefree current) *
        normSq (p.eval sample)
  diagonalLinear :
    construction.state.box.diagonalSq <=
      (128 / linearResidualScale squarefree current) *
        normSq (p.eval sample)

/-- Exact displayed zeros remain a separate finite terminal; the dyadic
branch is used only when exact evaluation is nonzero. -/
inductive LinearResidualChordalObservation
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) : Type where
  | exact (evaluation : p.eval sample = 0)
  | band
      (result : LinearResidualChordalResult squarefree elimination current
        sample)

/-- The positive-residual branch of the sharper theorem.  A bounded dyadic
scan chooses `r` with `R / mu < r^2 <= 4 R / mu`; the explicit threshold
places `r` beneath every pre-existing Newton-band safety cap. -/
def ofPositiveLinearResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (evaluationNonzero : p.eval sample ≠ 0)
    (residualSmall : normSq (p.eval sample) <
      linearResidualThreshold squarefree current sample) :
    LinearResidualChordalResult squarefree elimination current sample := by
  let residual := normSq (p.eval sample)
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have residualPositive : 0 < residual := normSq_pos evaluationNonzero
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  have residualLtMu : residual < mu := by
    exact residualSmall.trans_le (min_le_left _ _)
  let target := residual / mu
  have targetPositive : 0 < target :=
    RFAP.ConstructiveFraction.div_pos_direct residualPositive muPositive
  have targetLtOne : target < 1 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).2
    simpa only [RFAP.ConstructiveFraction.one_mul] using residualLtMu
  let bracket := RFAP.DyadicBracket.select target targetPositive
    targetLtOne
  have residualLtSafeBudget : residual < mu * safe ^ 2 / 4 := by
    exact residualSmall.trans_le (min_le_right _ _)
  have targetLtQuarterSafe : target < safe ^ 2 / 4 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).2
    calc
      residual < mu * safe ^ 2 / 4 := residualLtSafeBudget
      _ = (safe ^ 2 / 4) * mu :=
        mul_mul_div_reassociate mu (safe ^ 2) 4
  have fourTargetLtSafeSq : 4 * target < safe ^ 2 := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 4 by decide) targetLtQuarterSafe
    calc
      4 * target < 4 * (safe ^ 2 / 4) := scaled
      _ = safe ^ 2 := by
        calc
          4 * (safe ^ 2 / 4) = (safe ^ 2 / 4) * 4 := by
            exact RFAP.ConstructiveFraction.mul_comm _ _
          _ = safe ^ 2 :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 4 (by decide)
  have radiusSqLtSafeSq : bracket.radius ^ 2 < safe ^ 2 :=
    bracket.square_le_four_target.trans_lt fourTargetLtSafeSq
  have radiusLtSafe : bracket.radius < safe :=
    RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
      safePositive.le radiusSqLtSafeSq
  have radiusIdentity :
      RFAP.ResidualWinding.anchoredRadius
          squarefree (protectedAmbient current) sample bracket.radius =
        bracket.radius :=
    RFAP.ResidualWinding.anchoredRadius_eq_cap_of_le_reference
      squarefree (protectedAmbient current) sample radiusLtSafe.le
  have scaleLeMargin : mu <=
      RFAP.LocalExtraction.derivativeMargin
        squarefree current.box := min_le_left _ _
  have scaleLeTwiceLipschitz : mu <=
      2 * RFAP.PolynomialBounds.denseLipschitzBound
        p current.box := min_le_right _ _
  have residualLtScaledRadius : residual < bracket.radius ^ 2 * mu := by
    exact (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).1
      bracket.target_lt_square
  have residualLtSource : residual <
      RFAP.PolynomialBounds.denseLipschitzBound p current.box *
        (2 * bracket.radius ^ 2) := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          (2 * RFAP.PolynomialBounds.denseLipschitzBound
            p current.box) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaleLeTwiceLipschitz
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = RFAP.PolynomialBounds.denseLipschitzBound
          p current.box * (2 * bracket.radius ^ 2) := by ring1
  have residualLtDisplacement : residual <
      RFAP.LocalExtraction.derivativeMargin
        squarefree current.box * bracket.radius ^ 2 := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          RFAP.LocalExtraction.derivativeMargin
            squarefree current.box :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaleLeMargin
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = RFAP.LocalExtraction.derivativeMargin
          squarefree current.box * bracket.radius ^ 2 := by ring1
  have constructorTarget : residual <
      residualTarget squarefree current sample bracket.radius := by
    rw [residualTarget, RFAP.ResidualWinding.anchoredResidualTarget,
      protectedAmbient,
      radiusIdentity]
    exact lt_min residualLtSource residualLtDisplacement
  let construction := ofResidual degreeAtLeastTwo squarefree elimination
    current sample strict bracket.radiusPositive constructorTarget
  have chordalLinear : forall z, construction.state.box.Contains z ->
      RFAP.Chordal.affineChordalSq sample z <=
        (72 / mu) * residual := by
    intro z inside
    calc
      RFAP.Chordal.affineChordalSq sample z <=
          18 * bracket.radius ^ 2 := construction.chordalBound z inside
      _ <= 18 * (4 * target) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_four_target (by decide)
      _ = (72 / mu) * residual := by
        dsimp only [target]
        calc
          18 * (4 * (residual / mu)) =
              (18 * 4) * (residual / mu) :=
            (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
          _ = 72 * (residual / mu) := by rw [eighteen_mul_four]
          _ = (72 / mu) * residual :=
            mul_div_reassociate 72 residual mu
  have diagonalLinear : construction.state.box.diagonalSq <=
      (128 / mu) * residual := by
    calc
      construction.state.box.diagonalSq <= 32 * bracket.radius ^ 2 :=
        construction.diagonalBound
      _ <= 32 * (4 * target) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_four_target
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 32) (by decide)).le
      _ = (128 / mu) * residual := by
        dsimp only [target]
        calc
          32 * (4 * (residual / mu)) =
              (32 * 4) * (residual / mu) :=
            (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
          _ = 128 * (residual / mu) := by rw [thirtyTwo_mul_four]
          _ = (128 / mu) * residual :=
            mul_div_reassociate 128 residual mu
  exact
    { radius := bracket.radius
      radiusPositive := bracket.radiusPositive
      residualOverScale_lt_radiusSq := by
        simpa only [residual, mu, target] using bracket.target_lt_square
      radiusSq_le_fourResidualOverScale := by
        simpa only [residual, mu, target] using
          bracket.square_le_four_target
      construction := construction
      chordalLinear := by
        simpa only [mu, residual] using chordalLinear
      diagonalLinear := by
        simpa only [mu, residual] using diagonalLinear }

/-- Public sharper classifier.  Exact finite evaluation is checked first;
only a positive displayed residual runs the bounded dyadic selector. -/
def observeOfLinearResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (residualSmall : normSq (p.eval sample) <
      linearResidualThreshold squarefree current sample) :
    LinearResidualChordalObservation squarefree elimination current sample :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofPositiveLinearResidual degreeAtLeastTwo squarefree elimination
      current sample strict evaluation residualSmall)

/-! ## Accuracy-parameterized finite residual-linear converse -/

/-- Positive smallness threshold for a caller-supplied rational square
factor.  The factor is explicit input; positivity is proved below under the
required hypothesis `1 < factor`. -/
def adjustableLinearResidualThreshold
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) : Coordinate :=
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  min mu (mu * safe ^ 2 / factor)

theorem adjustableLinearResidualThreshold_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (factor : Coordinate) (factorGreater : 1 < factor) :
    0 < adjustableLinearResidualThreshold squarefree current sample factor := by
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  exact lt_min muPositive
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct muPositive
        (RFAP.ConstructiveFraction.pow_pos_direct safePositive 2))
      ((show (0 : Coordinate) < 1 by decide).trans factorGreater))

/-- Output of the residual-linear converse at a displayed requested factor. -/
structure AdjustableLinearResidualChordalResult
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) where
  radius : Coordinate
  radiusPositive : 0 < radius
  residualOverScale_lt_radiusSq :
    normSq (p.eval sample) / linearResidualScale squarefree current <
      radius ^ 2
  radiusSq_le_factorResidualOverScale :
    radius ^ 2 <=
      factor *
        (normSq (p.eval sample) / linearResidualScale squarefree current)
  construction :
    ResidualChordalResult squarefree elimination current sample radius
  chordalLinear : forall z, construction.state.box.Contains z ->
    RFAP.Chordal.affineChordalSq sample z <=
      ((18 * factor) /
        linearResidualScale squarefree current) *
        normSq (p.eval sample)
  diagonalLinear :
    construction.state.box.diagonalSq <=
      ((32 * factor) / linearResidualScale squarefree current) *
        normSq (p.eval sample)

/-- Exact displayed zeros remain a separate finite terminal. -/
inductive AdjustableLinearResidualChordalObservation
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) : Type where
  | exact (evaluation : p.eval sample = 0)
  | band
      (result : AdjustableLinearResidualChordalResult squarefree elimination
        current sample factor)

/-- Positive-residual branch using a bounded finite bracket at the displayed
factor. -/
def ofPositiveAdjustableLinearResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (evaluationNonzero : p.eval sample ≠ 0)
    (factor : Coordinate) (factorGreater : 1 < factor)
    (residualSmall : normSq (p.eval sample) <
      adjustableLinearResidualThreshold squarefree current sample factor) :
    AdjustableLinearResidualChordalResult squarefree elimination current
      sample factor := by
  let residual := normSq (p.eval sample)
  let mu := linearResidualScale squarefree current
  let safe := linearReferenceRadius squarefree current sample
  have residualPositive : 0 < residual := normSq_pos evaluationNonzero
  have muPositive : 0 < mu := linearResidualScale_pos squarefree current
  have safePositive : 0 < safe :=
    linearReferenceRadius_pos squarefree current sample strict
  have residualLtMu : residual < mu :=
    residualSmall.trans_le (min_le_left _ _)
  let target := residual / mu
  have targetPositive : 0 < target :=
    RFAP.ConstructiveFraction.div_pos_direct residualPositive muPositive
  have targetLtOne : target < 1 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).2
    simpa only [RFAP.ConstructiveFraction.one_mul] using residualLtMu
  have factorPositive : 0 < factor :=
    (show (0 : Coordinate) < 1 by decide).trans factorGreater
  let bracket := RFAP.DyadicBracket.selectWithin target factor targetPositive
    targetLtOne factorGreater
  have residualLtSafeBudget :
      residual < mu * safe ^ 2 / factor :=
    residualSmall.trans_le (min_le_right _ _)
  have residualFactorLtSafeBudget :
      residual * factor < mu * safe ^ 2 :=
    (RFAP.ConstructiveFraction.lt_div_iff_pos factorPositive).1
      residualLtSafeBudget
  have factorTargetLtSafeSq : factor * target < safe ^ 2 := by
    have rearranged : factor * target = (residual * factor) / mu := by
      dsimp only [target]
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    rw [rearranged]
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).2
    calc
      residual * factor < mu * safe ^ 2 := residualFactorLtSafeBudget
      _ = safe ^ 2 * mu := by ring1
  have radiusSqLtSafeSq : bracket.radius ^ 2 < safe ^ 2 :=
    bracket.square_le_factor_target.trans_lt factorTargetLtSafeSq
  have radiusLtSafe : bracket.radius < safe :=
    RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
      safePositive.le radiusSqLtSafeSq
  have radiusIdentity :
      RFAP.ResidualWinding.anchoredRadius
          squarefree (protectedAmbient current) sample bracket.radius =
        bracket.radius :=
    RFAP.ResidualWinding.anchoredRadius_eq_cap_of_le_reference
      squarefree (protectedAmbient current) sample radiusLtSafe.le
  have scaleLeMargin : mu <=
      RFAP.LocalExtraction.derivativeMargin squarefree current.box :=
    min_le_left _ _
  have scaleLeTwiceLipschitz : mu <=
      2 * RFAP.PolynomialBounds.denseLipschitzBound p current.box :=
    min_le_right _ _
  have residualLtScaledRadius : residual < bracket.radius ^ 2 * mu :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos muPositive).1
      bracket.target_lt_square
  have residualLtSource : residual <
      RFAP.PolynomialBounds.denseLipschitzBound p current.box *
        (2 * bracket.radius ^ 2) := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          (2 * RFAP.PolynomialBounds.denseLipschitzBound p current.box) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaleLeTwiceLipschitz
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = RFAP.PolynomialBounds.denseLipschitzBound p current.box *
          (2 * bracket.radius ^ 2) := by ring1
  have residualLtDisplacement : residual <
      RFAP.LocalExtraction.derivativeMargin squarefree current.box *
        bracket.radius ^ 2 := by
    calc
      residual < bracket.radius ^ 2 * mu := residualLtScaledRadius
      _ <= bracket.radius ^ 2 *
          RFAP.LocalExtraction.derivativeMargin squarefree current.box :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          scaleLeMargin
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            bracket.radiusPositive.le 2)
      _ = RFAP.LocalExtraction.derivativeMargin squarefree current.box *
          bracket.radius ^ 2 := by ring1
  have constructorTarget : residual <
      residualTarget squarefree current sample bracket.radius := by
    rw [residualTarget, RFAP.ResidualWinding.anchoredResidualTarget,
      protectedAmbient,
      radiusIdentity]
    exact lt_min residualLtSource residualLtDisplacement
  let construction := ofResidual degreeAtLeastTwo squarefree elimination
    current sample strict bracket.radiusPositive constructorTarget
  have chordalLinear : forall z, construction.state.box.Contains z ->
      RFAP.Chordal.affineChordalSq sample z <=
        ((18 * factor) / mu) * residual := by
    intro z inside
    calc
      RFAP.Chordal.affineChordalSq sample z <=
          18 * bracket.radius ^ 2 := construction.chordalBound z inside
      _ <= 18 * (factor * target) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_factor_target (by decide)
      _ = ((18 * factor) / mu) * residual := by
        dsimp only [target]
        calc
          18 * (factor * (residual / mu)) =
              (18 * factor) * (residual / mu) := by
            rw [RFAP.ConstructiveFraction.mul_assoc]
          _ = ((18 * factor) / mu) * residual :=
            mul_div_reassociate (18 * factor) residual mu
  have diagonalLinear : construction.state.box.diagonalSq <=
      ((32 * factor) / mu) * residual := by
    calc
      construction.state.box.diagonalSq <= 32 * bracket.radius ^ 2 :=
        construction.diagonalBound
      _ <= 32 * (factor * target) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bracket.square_le_factor_target
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 32) (by decide)).le
      _ = ((32 * factor) / mu) * residual := by
        dsimp only [target]
        calc
          32 * (factor * (residual / mu)) =
              (32 * factor) * (residual / mu) := by
            rw [RFAP.ConstructiveFraction.mul_assoc]
          _ = ((32 * factor) / mu) * residual :=
            mul_div_reassociate (32 * factor) residual mu
  exact
    { radius := bracket.radius
      radiusPositive := bracket.radiusPositive
      residualOverScale_lt_radiusSq := by
        simpa only [residual, mu, target] using bracket.target_lt_square
      radiusSq_le_factorResidualOverScale := by
        simpa only [residual, mu, target] using
          bracket.square_le_factor_target
      construction := construction
      chordalLinear := by
        simpa only [mu, residual] using chordalLinear
      diagonalLinear := by
        simpa only [mu, residual] using diagonalLinear }

/-- Public classifier at a displayed requested factor. -/
def observeOfAdjustableLinearResidual
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (factor : Coordinate) (factorGreater : 1 < factor)
    (residualSmall : normSq (p.eval sample) <
      adjustableLinearResidualThreshold squarefree current sample factor) :
    AdjustableLinearResidualChordalObservation squarefree elimination current
      sample factor :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (ofPositiveAdjustableLinearResidual degreeAtLeastTwo squarefree
      elimination current sample strict evaluation factor factorGreater
      residualSmall)

end RFAP.ResidualChordal
