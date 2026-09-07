import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.LocalExtraction

/-!
# Choice-free protected boundary strips

A finite boundary-clearance certificate and the Horner Lipschitz bound define
an explicit rational strip.  Any sufficiently small nonzero-winding subbox
must avoid that strip.  The proof projects one supplied corner to one parent
edge and uses only finite squared-norm inequalities.
-/

namespace RFAP.ProtectedBoundary

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds
open RFAP.GlobalWinding
open RFAP.Winding
open RFAP.LocalExtraction

/-- The finite scale used to turn the later squared-distance estimate into a
linear one.  Writing it as three small factors also keeps quotient numeral
elaboration shallow. -/
def protectedBoundaryScale : Coordinate := (8 : Coordinate) * 8 * 8

/-- Factored upper bound for the squared distance to a projected boundary
point. -/
def protectedBoundaryDistanceScale : Coordinate := (8 : Coordinate) * 8

private theorem protectedBoundaryScale_pos :
    0 < protectedBoundaryScale := by
  unfold protectedBoundaryScale
  have eightPositive : (0 : Coordinate) < 8 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct eightPositive eightPositive)
    eightPositive

/-- A conservative positive strip radius.  The reciprocal scale cap makes the
later squared-distance estimate linear in the displayed radius. -/
def protectedBoundaryRadius
    (p : GaussianPolynomial) (ambient : Box)
    (clearance : BoundaryClearance p ambient) : Coordinate :=
  min (1 / protectedBoundaryScale)
    (min (clearance.bound / (2 * denseLipschitzBound p ambient))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

theorem protectedBoundaryRadius_pos
    (p : GaussianPolynomial) {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper) :
    0 < protectedBoundaryRadius p ambient clearance := by
  have widthXPositive : 0 < ambient.widthX := by
    exact RFAP.ConstructiveFraction.sub_pos_direct proper.1
  have widthYPositive : 0 < ambient.widthY := by
    exact RFAP.ConstructiveFraction.sub_pos_direct proper.2
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  have onePositive : (0 : Coordinate) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
  have twoPositive : (0 : Coordinate) < 2 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 2) (by decide)
  have sixteenPositive : (0 : Coordinate) < 16 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 16) (by decide)
  exact lt_min
    (RFAP.ConstructiveFraction.div_pos_direct onePositive
      protectedBoundaryScale_pos)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct clearance.positive
        (RFAP.ConstructiveFraction.mul_pos_direct twoPositive
          lipschitzPositive))
      (lt_min
        (RFAP.ConstructiveFraction.div_pos_direct widthXPositive
          sixteenPositive)
        (RFAP.ConstructiveFraction.div_pos_direct widthYPositive
          sixteenPositive)))

/-- The protected radius remains nonnegative even for a degenerate box.  This
weak form is useful for coefficient monotonicity statements whose conclusions
do not require a proper ambient box. -/
theorem protectedBoundaryRadius_nonneg
    (p : GaussianPolynomial) (ambient : Box)
    (clearance : BoundaryClearance p ambient) :
    0 ≤ protectedBoundaryRadius p ambient clearance := by
  have onePositive : (0 : Coordinate) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
  have twoPositive : (0 : Coordinate) < 2 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 2) (by decide)
  have sixteenPositive : (0 : Coordinate) < 16 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 16) (by decide)
  have widthXQuotientNonnegative :
      0 ≤ ambient.widthX / (16 : Coordinate) := by
    change 0 ≤ ambient.widthX * (16 : Coordinate)⁻¹
    exact RFAP.ConstructiveFraction.mul_nonneg_direct ambient.widthX_nonneg
      (RFAP.ConstructiveFraction.inv_pos_direct sixteenPositive).le
  have widthYQuotientNonnegative :
      0 ≤ ambient.widthY / (16 : Coordinate) := by
    change 0 ≤ ambient.widthY * (16 : Coordinate)⁻¹
    exact RFAP.ConstructiveFraction.mul_nonneg_direct ambient.widthY_nonneg
      (RFAP.ConstructiveFraction.inv_pos_direct sixteenPositive).le
  exact le_min
    (RFAP.ConstructiveFraction.div_pos_direct onePositive
      protectedBoundaryScale_pos).le
    (le_min
      (RFAP.ConstructiveFraction.div_pos_direct clearance.positive
        (RFAP.ConstructiveFraction.mul_pos_direct twoPositive
          (denseLipschitzBound_pos p ambient))).le
      (le_min widthXQuotientNonnegative widthYQuotientNonnegative))

theorem protectedBoundaryRadius_le_widths
    (p : GaussianPolynomial) (ambient : Box)
    (clearance : BoundaryClearance p ambient) :
    protectedBoundaryRadius p ambient clearance ≤ ambient.widthX / 16 ∧
      protectedBoundaryRadius p ambient clearance ≤ ambient.widthY / 16 := by
  have belowInner : protectedBoundaryRadius p ambient clearance ≤
      min (clearance.bound / (2 * denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)) := by
    exact min_le_right
      (1 / protectedBoundaryScale)
      (min (clearance.bound / (2 * denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)))
  have widths : protectedBoundaryRadius p ambient clearance ≤
      min (ambient.widthX / 16) (ambient.widthY / 16) := by
    exact belowInner.trans
      (min_le_right
        (clearance.bound / (2 * denseLipschitzBound p ambient))
        (min (ambient.widthX / 16) (ambient.widthY / 16)))
  exact ⟨widths.trans (min_le_left _ _),
    widths.trans (min_le_right _ _)⟩

/-- Proof-relevant selection of the parent side met by a small box. -/
inductive BoundaryStripSide
    (ambient : Box) (width : Coordinate) (z : Gaussian) : Type
  | left (inside : z.re ≤ ambient.xLower + width)
  | right (inside : ambient.xUpper - width ≤ z.re)
  | bottom (inside : z.im ≤ ambient.yLower + width)
  | top (inside : ambient.yUpper - width ≤ z.im)

/-- A supplied finite point of the small box and the side it places in the
parent strip. -/
structure BoundaryStripWitness
    (ambient small : Box) (width : Coordinate) where
  point : Gaussian
  point_mem : small.Contains point
  side : BoundaryStripSide ambient width point

/-- Parent-boundary projection with an explicit anchor-distance estimate. -/
structure NearbyBoundaryPoint
    (ambient small : Box) (rho : Coordinate) where
  point : Gaussian
  boundary : RFAP.BoxClearance.OnBoxBoundary ambient point
  distance : normSq (point - small.anchor) ≤
    protectedBoundaryDistanceScale * rho ^ 2

/-- Project the supplied strip point to its selected parent side. -/
def nearbyBoundaryPoint
    {ambient small : Box} {rho : Coordinate}
    (refines : small.Refines ambient)
    (diagonal : small.diagonalSq ≤ rho ^ 2)
    (witness : BoundaryStripWitness ambient small (4 * rho)) :
    NearbyBoundaryPoint ambient small rho := by
  rcases witness with ⟨z, zSmall, side⟩
  have zAmbient := refines.contains zSmall
  have zAnchorDistance := small.normSq_sub_anchor_le zSmall
  have zAnchorBound : normSq (z - small.anchor) ≤ rho ^ 2 :=
    zAnchorDistance.trans diagonal
  have projectionFinish : ∀ point : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary ambient point →
      normSq (point - z) ≤ 16 * rho ^ 2 →
      NearbyBoundaryPoint ambient small rho := by
    intro point boundary projectionBound
    have decomposition : point - small.anchor =
        (point - z) + (z - small.anchor) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;>
        ring1
    have sumBound := normSq_add_le_two (point - z) (z - small.anchor)
    have squareNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct rho
    have squareLeProjection : rho ^ 2 ≤ 16 * rho ^ 2 := by
      calc
        rho ^ 2 = 1 * rho ^ 2 := by ring1
        _ ≤ 16 * rho ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (RFAP.ConstructiveFraction.natCast_le_direct
              (m := 1) (n := 16) (by decide)) squareNonnegative
    have twoNonnegative : (0 : Coordinate) ≤ 2 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 2) (by decide)).le
    refine ⟨point, boundary, ?_⟩
    rw [decomposition]
    calc
      normSq ((point - z) + (z - small.anchor)) ≤
          2 * (normSq (point - z) + normSq (z - small.anchor)) := sumBound
      _ ≤ 2 * (16 * rho ^ 2 + rho ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add projectionBound zAnchorBound) (by decide)
      _ ≤ 2 * (16 * rho ^ 2 + 16 * rho ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (le_refl _) squareLeProjection)
          twoNonnegative
      _ = protectedBoundaryDistanceScale * rho ^ 2 := by
        unfold protectedBoundaryDistanceScale
        ring1
  cases side with
  | left sideBound =>
      let point : Gaussian := ⟨ambient.xLower, z.im⟩
      have deltaNonnegative : 0 ≤ z.re - ambient.xLower :=
        sub_nonneg.mpr zAmbient.1
      have deltaBound : z.re - ambient.xLower ≤ 4 * rho := by
        have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct sideBound ambient.xLower
        calc
          z.re - ambient.xLower ≤
              ambient.xLower + 4 * rho - ambient.xLower := shifted
          _ = 4 * rho := by ring1
      have squareBound := RFAP.ConstructiveFraction.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨le_rfl, ambient.x_valid, zAmbient.2.2.1,
          zAmbient.2.2.2⟩, Or.inl rfl⟩
      · calc
          normSq (point - z) = (z.re - ambient.xLower) ^ 2 := by
            dsimp only [point, normSq, sub_re, sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | right sideBound =>
      let point : Gaussian := ⟨ambient.xUpper, z.im⟩
      have deltaNonnegative : 0 ≤ ambient.xUpper - z.re :=
        sub_nonneg.mpr zAmbient.2.1
      have deltaBound : ambient.xUpper - z.re ≤ 4 * rho := by
        have shifted := RFAP.ConstructiveFraction.sub_le_sub_left_direct sideBound ambient.xUpper
        calc
          ambient.xUpper - z.re ≤
              ambient.xUpper - (ambient.xUpper - 4 * rho) := shifted
          _ = 4 * rho := by ring1
      have squareBound := RFAP.ConstructiveFraction.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨ambient.x_valid, le_rfl, zAmbient.2.2.1,
          zAmbient.2.2.2⟩, Or.inr (Or.inl rfl)⟩
      · calc
          normSq (point - z) = (ambient.xUpper - z.re) ^ 2 := by
            dsimp only [point, normSq, sub_re, sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | bottom sideBound =>
      let point : Gaussian := ⟨z.re, ambient.yLower⟩
      have deltaNonnegative : 0 ≤ z.im - ambient.yLower :=
        sub_nonneg.mpr zAmbient.2.2.1
      have deltaBound : z.im - ambient.yLower ≤ 4 * rho := by
        have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct sideBound ambient.yLower
        calc
          z.im - ambient.yLower ≤
              ambient.yLower + 4 * rho - ambient.yLower := shifted
          _ = 4 * rho := by ring1
      have squareBound := RFAP.ConstructiveFraction.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨zAmbient.1, zAmbient.2.1, le_rfl,
          ambient.y_valid⟩, Or.inr (Or.inr (Or.inl rfl))⟩
      · calc
          normSq (point - z) = (z.im - ambient.yLower) ^ 2 := by
            dsimp only [point, normSq, sub_re, sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | top sideBound =>
      let point : Gaussian := ⟨z.re, ambient.yUpper⟩
      have deltaNonnegative : 0 ≤ ambient.yUpper - z.im :=
        sub_nonneg.mpr zAmbient.2.2.2
      have deltaBound : ambient.yUpper - z.im ≤ 4 * rho := by
        have shifted := RFAP.ConstructiveFraction.sub_le_sub_left_direct sideBound ambient.yUpper
        calc
          ambient.yUpper - z.im ≤
              ambient.yUpper - (ambient.yUpper - 4 * rho) := shifted
          _ = 4 * rho := by ring1
      have squareBound := RFAP.ConstructiveFraction.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨zAmbient.1, zAmbient.2.1, ambient.y_valid,
          le_rfl⟩, Or.inr (Or.inr (Or.inr rfl))⟩
      · calc
          normSq (point - z) = (ambient.yUpper - z.im) ^ 2 := by
            dsimp only [point, normSq, sub_re, sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1

/-- The protected radius leaves enough numerical room for the projected
boundary value to dominate both source oscillations. -/
theorem protectedBoundaryRadius_dominates
    (p : GaussianPolynomial) {ambient small : Box}
    (clearance : BoundaryClearance p ambient)
    (proper : ambient.Proper)
    (diagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2) :
    2 * (anchorResidualBound p ambient small +
      denseLipschitzBound p ambient *
        (protectedBoundaryDistanceScale *
          protectedBoundaryRadius p ambient clearance ^ 2)) <
      clearance.bound := by
  let rho := protectedBoundaryRadius p ambient clearance
  let lipschitz := denseLipschitzBound p ambient
  have rhoPositive := protectedBoundaryRadius_pos p clearance proper
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  have rhoCap : rho ≤ 1 / protectedBoundaryScale := min_le_left _ _
  have rhoRatio : rho ≤ clearance.bound / (2 * lipschitz) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have rhoScaled : rho * protectedBoundaryScale ≤ 1 :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      protectedBoundaryScale_pos).mp rhoCap
  have ratioScaled : rho * (2 * lipschitz) ≤ clearance.bound :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        lipschitzPositive)).mp rhoRatio
  let base := lipschitz * rho ^ 2
  have basePositive : 0 < base := RFAP.ConstructiveFraction.mul_pos_direct
    lipschitzPositive (RFAP.ConstructiveFraction.pow_pos_direct rhoPositive 2)
  have capScaled : protectedBoundaryScale * base ≤ lipschitz * rho := by
    have multiplierNonnegative : 0 ≤ lipschitz * rho :=
      (RFAP.ConstructiveFraction.mul_pos_direct
        lipschitzPositive rhoPositive).le
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      rhoScaled multiplierNonnegative
    calc
      protectedBoundaryScale * base =
          (rho * protectedBoundaryScale) * (lipschitz * rho) := by
        dsimp only [base]
        ring1
      _ ≤ 1 * (lipschitz * rho) := scaled
      _ = lipschitz * rho := by ring1
  let halfScale : Coordinate := (4 : Coordinate) * 8 * 8
  have oneLeEight : (1 : Coordinate) ≤ 8 :=
    RFAP.ConstructiveFraction.natCast_le_direct
      (m := 1) (n := 8) (by decide)
  have baseLeEight : base ≤ 8 * base := by
    calc
      base = 1 * base := by ring1
      _ ≤ 8 * base :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          oneLeEight basePositive.le
  have baseLeDistanceScale : base ≤
      protectedBoundaryDistanceScale * base := by
    have eightNonnegative : (0 : Coordinate) ≤ 8 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide)).le
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      baseLeEight eightNonnegative
    calc
      base ≤ 8 * base := baseLeEight
      _ ≤ 8 * (8 * base) := scaled
      _ = protectedBoundaryDistanceScale * base := by
        unfold protectedBoundaryDistanceScale
        ring1
  have strictCoefficient : halfScale * base <
      protectedBoundaryScale * base := by
    have halfScalePositive : 0 < halfScale := by
      dsimp only [halfScale]
      have fourPositive : (0 : Coordinate) < 4 :=
        RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide)
      have eightPositive : (0 : Coordinate) < 8 :=
        RFAP.ConstructiveFraction.natCast_pos_direct (n := 8) (by decide)
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.mul_pos_direct fourPositive eightPositive)
        eightPositive
    have halfBasePositive := RFAP.ConstructiveFraction.mul_pos_direct
      halfScalePositive basePositive
    calc
      halfScale * base = 0 + halfScale * base := by ring1
      _ < halfScale * base + halfScale * base :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          halfBasePositive (halfScale * base)
      _ = protectedBoundaryScale * base := by
        dsimp only [halfScale, protectedBoundaryScale]
        ring1
  have lipschitzRhoPositive :=
    RFAP.ConstructiveFraction.mul_pos_direct lipschitzPositive rhoPositive
  have strictDoubling : lipschitz * rho < 2 * lipschitz * rho := by
    calc
      lipschitz * rho = 0 + lipschitz * rho := by ring1
      _ < lipschitz * rho + lipschitz * rho :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          lipschitzRhoPositive (lipschitz * rho)
      _ = 2 * lipschitz * rho := by ring1
  have residualBound : anchorResidualBound p ambient small ≤ base := by
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      diagonal lipschitzPositive.le
  calc
    2 * (anchorResidualBound p ambient small +
        lipschitz * (protectedBoundaryDistanceScale * rho ^ 2)) ≤
        halfScale * base := by
      have residualDistance : anchorResidualBound p ambient small ≤
          protectedBoundaryDistanceScale * base :=
        residualBound.trans baseLeDistanceScale
      have twoNonnegative : (0 : Coordinate) ≤ 2 :=
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 2) (by decide)).le
      have variationAsBase :
          lipschitz * (protectedBoundaryDistanceScale * rho ^ 2) =
            protectedBoundaryDistanceScale * base := by
        dsimp only [base]
        ring1
      calc
        2 * (anchorResidualBound p ambient small +
            lipschitz * (protectedBoundaryDistanceScale * rho ^ 2)) =
            2 * (anchorResidualBound p ambient small +
              protectedBoundaryDistanceScale * base) := by
          rw [variationAsBase]
        _ ≤ 2 * (protectedBoundaryDistanceScale * base +
            protectedBoundaryDistanceScale * base) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add residualDistance (le_refl _)) twoNonnegative
        _ = halfScale * base := by
          dsimp only [halfScale, protectedBoundaryDistanceScale]
          ring1
    _ < protectedBoundaryScale * base := strictCoefficient
    _ ≤ lipschitz * rho := capScaled
    _ < 2 * lipschitz * rho := strictDoubling
    _ ≤ clearance.bound := by
      have rearranged : 2 * lipschitz * rho =
          rho * (2 * lipschitz) := by ring1
      rw [rearranged]
      exact ratioScaled

/-- Meeting the protected strip forces raw winding zero. -/
theorem quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (clearance : BoundaryClearance p ambient)
    (ambientProper : ambient.Proper) (smallProper : small.Proper)
    (refines : small.Refines ambient)
    (diagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2)
    (witness : BoundaryStripWitness ambient small
      (4 * protectedBoundaryRadius p ambient clearance)) :
    quadrupledBoxWinding p small = 0 := by
  let rho := protectedBoundaryRadius p ambient clearance
  have rhoPositive := protectedBoundaryRadius_pos p clearance ambientProper
  have nearby : NearbyBoundaryPoint ambient small rho :=
    nearbyBoundaryPoint (ambient := ambient) (small := small)
      (rho := rho) refines diagonal witness
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variationRaw := normSq_eval_sub_eval_le_denseLipschitzBound
    p nearby.boundary.1 anchorInside
  have variation : normSq (p.eval nearby.point - p.eval small.anchor) ≤
      denseLipschitzBound p ambient *
        (protectedBoundaryDistanceScale * rho ^ 2) :=
    variationRaw.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        nearby.distance (denseLipschitzBound_pos p ambient).le)
  have valueIdentity : p.eval nearby.point = p.eval small.anchor +
      (p.eval nearby.point - p.eval small.anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im] <;>
      ring1
  have valueUpper := normSq_add_le_two (p.eval small.anchor)
    (p.eval nearby.point - p.eval small.anchor)
  rw [← valueIdentity] at valueUpper
  have dominance := protectedBoundaryRadius_dominates
    p clearance ambientProper diagonal
  have chain :
      2 * (anchorResidualBound p ambient small +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2)) <
        2 * (normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2)) := by
    have twoNonnegative : (0 : Coordinate) ≤ 2 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 2) (by decide)).le
    calc
      2 * (anchorResidualBound p ambient small +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2)) <
          clearance.bound := dominance
      _ ≤ normSq (p.eval nearby.point) :=
        clearance.lower nearby.point nearby.boundary
      _ ≤ 2 * (normSq (p.eval small.anchor) +
          normSq (p.eval nearby.point - p.eval small.anchor)) := valueUpper
      _ ≤ 2 * (normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2)) := by
        have added : normSq (p.eval small.anchor) +
              normSq (p.eval nearby.point - p.eval small.anchor) ≤
            normSq (p.eval small.anchor) +
              denseLipschitzBound p ambient *
                (protectedBoundaryDistanceScale * rho ^ 2) :=
          add_le_add (le_refl _) variation
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          added twoNonnegative
  have cancelledScale :
      anchorResidualBound p ambient small +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2) <
        normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient *
            (protectedBoundaryDistanceScale * rho ^ 2) := by
    have twoPositive : (0 : Coordinate) < 2 :=
      RFAP.ConstructiveFraction.natCast_pos_direct (n := 2) (by decide)
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2) ?_ twoPositive
    simpa only [RFAP.ConstructiveFraction.mul_comm] using chain
  have large : anchorResidualBound p ambient small <
      normSq (p.eval small.anchor) :=
    RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct cancelledScale
  exact quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    p degreePositive refines smallProper large

/-- A sufficiently small nonzero-winding source lies beyond all four
protected strips. -/
theorem strictly_inside_protectedBoundary
    {p : GaussianPolynomial} {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (clearance : BoundaryClearance p ambient)
    (ambientProper : ambient.Proper) (smallProper : small.Proper)
    (refines : small.Refines ambient)
    (rawNonzero : quadrupledBoxWinding p small ≠ 0)
    (diagonal : small.diagonalSq ≤
      protectedBoundaryRadius p ambient clearance ^ 2) :
    let rho := protectedBoundaryRadius p ambient clearance
    ambient.xLower + 4 * rho < small.xLower ∧
      small.xUpper < ambient.xUpper - 4 * rho ∧
      ambient.yLower + 4 * rho < small.yLower ∧
      small.yUpper < ambient.yUpper - 4 * rho := by
  let rho := protectedBoundaryRadius p ambient clearance
  have left : ambient.xLower + 4 * rho < small.xLower := by
    by_cases strict : ambient.xLower + 4 * rho < small.xLower
    · exact strict
    · have side : small.xLower ≤ ambient.xLower + 4 * rho :=
        le_of_not_gt strict
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨small.anchor, small.contains_anchor, BoundaryStripSide.left side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have right : small.xUpper < ambient.xUpper - 4 * rho := by
    by_cases strict : small.xUpper < ambient.xUpper - 4 * rho
    · exact strict
    · have side : ambient.xUpper - 4 * rho ≤ small.xUpper :=
        le_of_not_gt strict
      let point : Gaussian := ⟨small.xUpper, small.yLower⟩
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨point, ⟨small.x_valid, le_rfl, le_rfl, small.y_valid⟩,
          BoundaryStripSide.right side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have bottom : ambient.yLower + 4 * rho < small.yLower := by
    by_cases strict : ambient.yLower + 4 * rho < small.yLower
    · exact strict
    · have side : small.yLower ≤ ambient.yLower + 4 * rho :=
        le_of_not_gt strict
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨small.anchor, small.contains_anchor, BoundaryStripSide.bottom side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have top : small.yUpper < ambient.yUpper - 4 * rho := by
    by_cases strict : small.yUpper < ambient.yUpper - 4 * rho
    · exact strict
    · have side : ambient.yUpper - 4 * rho ≤ small.yUpper :=
        le_of_not_gt strict
      let point : Gaussian := ⟨small.xLower, small.yUpper⟩
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨point, ⟨le_rfl, small.x_valid, small.y_valid, le_rfl⟩,
          BoundaryStripSide.top side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  exact ⟨left, right, bottom, top⟩

end RFAP.ProtectedBoundary
