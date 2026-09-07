import CCL.Riemann.PeriodMatrix

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

namespace CCL.Riemann.FinitePositivity

open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev RationalVector := CCL.Riemann.PeriodMatrix.RationalVector
abbrev GaussianMatrix := CCL.Riemann.PeriodMatrix.GaussianMatrix
abbrev RationalMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Coordinate size

/-- Elementary rational square comparison kept local so the finite period
theorem does not inherit the unrelated Cauchy-resolution development. -/
private theorem lt_of_sq_lt_sq_of_nonneg {a b : Coordinate}
    (bNonnegative : 0 <= b) (squares : a ^ 2 < b ^ 2) : a < b := by
  rcases lt_trichotomy a b with less | rfl | greater
  · exact less
  · exact (lt_irrefl _ squares).elim
  · by_cases bZero : b = 0
    · subst b
      exact ((not_lt_of_ge
        (RFAP.ConstructiveFraction.sq_nonneg_direct a)) squares).elim
    · have bPositive : 0 < b := lt_of_le_of_ne bNonnegative (Ne.symm bZero)
      have aPositive : 0 < a := bPositive.trans greater
      have first : b * b < a * b :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          greater bPositive
      have second : a * b < a * a :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          aPositive greater
      have reverse : b ^ 2 < a ^ 2 := by
        simpa only [pow_two] using first.trans second
      exact (lt_asymm squares reverse).elim

/-- Halving a positive rational gives a strictly smaller positive rational. -/
private theorem half_lt_self {value : Coordinate} (positive : 0 < value) :
    value / 2 < value := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    value = value * 1 := by ring1
    _ < value * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

/-- Finite sums preserve pointwise weak inequalities. -/
theorem sumFin_mono {count : Nat} (left right : Fin count -> Coordinate)
    (pointwise : forall index, left index <= right index) :
    RFAP.ConstructiveFiniteMatrix.sumFin left <=
      RFAP.ConstructiveFiniteMatrix.sumFin right := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      exact add_le_add (pointwise 0)
        (inductionHypothesis
          (fun index : Fin count => left index.succ)
          (fun index : Fin count => right index.succ)
          (fun index => pointwise index.succ))

/-- Total displayed perturbation budget of a finite matrix. -/
def totalBudget {size : Nat} (budget : RationalMatrix size) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
    RFAP.ConstructiveFiniteMatrix.sumFin fun column => budget row column

/-- Rational centre matrix returned by one shared finite request. -/
def centerMatrix {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : Coordinate) (positive : 0 < target) : GaussianMatrix genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    data.omegaCenter target positive row column

@[simp] theorem centerMatrix_apply {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : Coordinate) (positive : 0 < target)
    (row column : Fin genus) :
    centerMatrix data target positive row column =
      data.omegaCenter target positive row column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Sample squared enclosure radii at `r²` when `r` is the desired rational
linear entry radius. -/
def squaredRefinementTarget (radius : Coordinate) : Coordinate :=
  radius ^ 2

theorem squaredRefinementTarget_positive {radius : Coordinate}
    (positive : 0 < radius) : 0 < squaredRefinementTarget radius := by
  unfold squaredRefinementTarget
  exact RFAP.ConstructiveFraction.pow_pos_direct positive 2

/-- The canonical entrywise radius matrix repeats the chosen shrinking
rational radius.  Sampling at its square avoids extracting square roots. -/
def automaticRadius {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (_data : NormalizedPeriodData curve)
    (radius : Coordinate) (_positive : 0 < radius) : RationalMatrix genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _row _column => radius

@[simp] theorem automaticRadius_apply {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    automaticRadius data radius positive row column = radius :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem automaticRadius_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    0 < automaticRadius data radius positive row column := by
  rw [automaticRadius_apply]
  exact positive

theorem omegaRadiusSq_lt_automaticRadius_sq {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    data.omegaRadiusSq (squaredRefinementTarget radius)
        (squaredRefinementTarget_positive positive) row column <
      (automaticRadius data radius positive row column) ^ 2 := by
  rw [automaticRadius_apply]
  exact data.omegaRadiusSq_lt_target (squaredRefinementTarget radius)
    (squaredRefinementTarget_positive positive) row column

/-- A strict squared Gaussian bound supplies strict signed bounds on its
imaginary coordinate. -/
theorem imaginary_bounds_of_normSq_lt_sq
    {delta : Gaussian} {radius : Coordinate} (radiusPositive : 0 < radius)
    (distance : RFAP.ConstructiveGaussian.Gaussian.normSq delta < radius ^ 2) :
    -radius < delta.im /\ delta.im < radius := by
  have imaginarySquare : delta.im ^ 2 < radius ^ 2 :=
    (show delta.im ^ 2 <= delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct delta.re)).trans_lt
      distance
  have upper := lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le imaginarySquare
  have negativeUpper := lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le (a := -delta.im) (by
      calc
        (-delta.im) ^ 2 = delta.im ^ 2 := by ring1
        _ < radius ^ 2 := imaginarySquare)
  exact
    ⟨by
      have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct negativeUpper
      simpa only [neg_neg] using negated,
    upper⟩

/-- Expanding a candidate matrix around a displayed centre turns its
quadratic form into the centre value plus a finite perturbation sum. -/
theorem imaginaryQuadraticForm_eq_center_add_perturbation {size : Nat}
    (vector : RationalVector size) (candidate center : GaussianMatrix size) :
    imaginaryQuadraticForm vector candidate =
      imaginaryQuadraticForm vector center +
        RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
          RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
            vector row * (candidate row column - center row column).im *
              vector column := by
  unfold imaginaryQuadraticForm
  rw [← RFAP.ConstructiveFiniteMatrix.sumFin_add]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro row
  rw [← RFAP.ConstructiveFiniteMatrix.sumFin_add]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro column
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_im]
  ring1

/-- Every rational coefficient is bounded above by its square plus one. -/
theorem value_le_sq_add_one (value : Coordinate) :
    value <= value ^ 2 + 1 := by
  by_cases positive : 0 < value
  · rcases le_total value 1 with small | large
    · exact small.trans (le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct value))
    · calc
        value = value * 1 := by ring1
        _ <= value * value :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            large positive.le
        _ = value ^ 2 := by ring1
        _ <= value ^ 2 + 1 := le_add_of_nonneg_right (by decide)
  · have nonpositive : value <= 0 := le_of_not_gt positive
    exact nonpositive.trans
      (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct value)
        (by decide))

/-- The negative coefficient has the same square-plus-one upper bound. -/
theorem neg_value_le_sq_add_one (value : Coordinate) :
    -value <= value ^ 2 + 1 := by
  calc
    -value <= (-value) ^ 2 + 1 := value_le_sq_add_one (-value)
    _ = value ^ 2 + 1 := by ring1

/-- A signed scalar perturbation inside `(-radius,radius)` has the automatic
square-plus-one lower budget. -/
theorem weighted_lower_of_radius (coefficient delta radius : Coordinate)
    (radiusPositive : 0 < radius) (lower : -radius < delta)
    (upper : delta < radius) :
    -((coefficient ^ 2 + 1) * radius) <= coefficient * delta := by
  rcases le_total 0 coefficient with nonnegative | nonpositive
  · have coefficientBound := value_le_sq_add_one coefficient
    have scaledBound : coefficient * radius <=
        (coefficient ^ 2 + 1) * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientBound radiusPositive.le
    have negatedBound :=
      RFAP.ConstructiveFraction.neg_le_neg_direct scaledBound
    have scaledLower : coefficient * (-radius) <= coefficient * delta :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        lower.le nonnegative
    calc
      -((coefficient ^ 2 + 1) * radius) <= -(coefficient * radius) :=
        negatedBound
      _ = coefficient * (-radius) := by ring1
      _ <= coefficient * delta := scaledLower
  · let magnitude := -coefficient
    have magnitudeNonnegative : 0 <= magnitude := by
      exact neg_nonneg.mpr nonpositive
    have magnitudeBound : magnitude <= coefficient ^ 2 + 1 := by
      simpa only [magnitude] using neg_value_le_sq_add_one coefficient
    have scaledBound : magnitude * radius <=
        (coefficient ^ 2 + 1) * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        magnitudeBound radiusPositive.le
    have negatedBound :=
      RFAP.ConstructiveFraction.neg_le_neg_direct scaledBound
    have scaledUpper : magnitude * delta <= magnitude * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        upper.le magnitudeNonnegative
    have negatedUpper :=
      RFAP.ConstructiveFraction.neg_le_neg_direct scaledUpper
    calc
      -((coefficient ^ 2 + 1) * radius) <= -(magnitude * radius) :=
        negatedBound
      _ <= -(magnitude * delta) := negatedUpper
      _ = coefficient * delta := by
        dsimp only [magnitude]
        ring1

/-- Automatically computed entrywise perturbation budget for one vector and
one positive radius matrix. -/
def automaticBudget {size : Nat} (vector : RationalVector size)
    (radius : RationalMatrix size) : RationalMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    ((vector row * vector column) ^ 2 + 1) * radius row column

@[simp] theorem automaticBudget_apply {size : Nat}
    (vector : RationalVector size) (radius : RationalMatrix size)
    (row column : Fin size) :
    automaticBudget vector radius row column =
      ((vector row * vector column) ^ 2 + 1) * radius row column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem automaticBudget_nonnegative {size : Nat}
    (vector : RationalVector size) (radius : RationalMatrix size)
    (radiusNonnegative : forall row column, 0 <= radius row column)
    (row column : Fin size) :
    0 <= automaticBudget vector radius row column := by
  rw [automaticBudget_apply]
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (vector row * vector column)) (by decide))
    (radiusNonnegative row column)

/-- The automatically assembled finite double-sum budget is nonnegative. -/
theorem totalAutomaticBudget_nonnegative {size : Nat}
    (vector : RationalVector size) (radius : RationalMatrix size)
    (radiusNonnegative : forall row column, 0 <= radius row column) :
    0 <= totalBudget (automaticBudget vector radius) := by
  unfold totalBudget
  calc
    0 = RFAP.ConstructiveFiniteMatrix.sumFin
          (fun _ : Fin size => (0 : Coordinate)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_zero.symm
    _ <= RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
          RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
            automaticBudget vector radius row column)) := by
      apply sumFin_mono
      intro row
      calc
        0 = RFAP.ConstructiveFiniteMatrix.sumFin
              (fun _ : Fin size => (0 : Coordinate)) :=
          RFAP.ConstructiveFiniteMatrix.sumFin_zero.symm
        _ <= RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
              automaticBudget vector radius row column) := by
          apply sumFin_mono
          intro column
          exact automaticBudget_nonnegative vector radius radiusNonnegative
            row column

theorem automaticBudget_weighted_lower {size : Nat}
    (vector : RationalVector size) (radius : RationalMatrix size)
    (radiusPositive : forall row column, 0 < radius row column)
    (row column : Fin size) (delta : Coordinate)
    (lower : -(radius row column) < delta)
    (upper : delta < radius row column) :
    -(automaticBudget vector radius row column) <=
      vector row * delta * vector column := by
  rw [automaticBudget_apply]
  calc
    -(((vector row * vector column) ^ 2 + 1) * radius row column) <=
        (vector row * vector column) * delta :=
      weighted_lower_of_radius (vector row * vector column) delta
        (radius row column) (radiusPositive row column) lower upper
    _ = vector row * delta * vector column := by ring1

/-- An entrywise squared-distance comparison gives a lower bound for the
whole finite imaginary quadratic form.  The bound is the same automatic
double-sum budget used for public matrix boxes, so it can also compare an
exact synchronized quotient with a separately refined persistent centre. -/
theorem imaginaryQuadraticForm_sub_automaticBudget_le {size : Nat}
    (vector : RationalVector size) (reference candidate : GaussianMatrix size)
    (radius : RationalMatrix size)
    (radiusPositive : forall row column, 0 < radius row column)
    (close : forall row column,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate row column - reference row column) <
        (radius row column) ^ 2) :
    imaginaryQuadraticForm vector reference -
        totalBudget (automaticBudget vector radius) <=
      imaginaryQuadraticForm vector candidate := by
  let perturbation : Coordinate :=
    RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
      RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
        vector row * (candidate row column - reference row column).im *
          vector column
  have perturbationLower :
      -totalBudget (automaticBudget vector radius) <= perturbation := by
    unfold totalBudget perturbation
    rw [← RFAP.ConstructiveFiniteMatrix.sumFin_neg]
    apply sumFin_mono
    intro row
    rw [← RFAP.ConstructiveFiniteMatrix.sumFin_neg]
    apply sumFin_mono
    intro column
    let delta := candidate row column - reference row column
    have bounds := imaginary_bounds_of_normSq_lt_sq
      (radiusPositive row column) (by simpa only [delta] using close row column)
    exact automaticBudget_weighted_lower vector radius radiusPositive
      row column delta.im bounds.1 bounds.2
  have shifted :
      imaginaryQuadraticForm vector reference -
          totalBudget (automaticBudget vector radius) <=
        imaginaryQuadraticForm vector reference + perturbation := by
    simpa only [sub_eq_add_neg, add_comm] using
      add_le_add_left perturbationLower
        (imaginaryQuadraticForm vector reference)
  have identity := imaginaryQuadraticForm_eq_center_add_perturbation
    vector candidate reference
  rw [show imaginaryQuadraticForm vector candidate =
      imaginaryQuadraticForm vector reference + perturbation by
        simpa only [perturbation] using identity]
  exact shifted

/-- A finite rational certificate sufficient to answer one pointwise
positivity request.  `weighted_lower` is only an entrywise scalar inequality;
the universal matrix-box conclusion is derived below by finite summation. -/
structure RequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  refinementTarget : Coordinate
  refinementPositive : 0 < refinementTarget
  refinement_lt_target : refinementTarget < target
  epsilon : Coordinate
  epsilon_positive : 0 < epsilon
  radius : RationalMatrix genus
  radius_positive : forall row column, 0 < radius row column
  radiusSq_lt_sq : forall row column,
    data.omegaRadiusSq refinementTarget refinementPositive row column <
      (radius row column) ^ 2
  budget : RationalMatrix genus
  budget_nonnegative : forall row column, 0 <= budget row column
  weighted_lower : forall row column (delta : Coordinate),
    -(radius row column) < delta -> delta < radius row column ->
      -(budget row column) <= vector row * delta * vector column
  center_margin :
    epsilon + totalBudget budget <
      imaginaryQuadraticForm vector
        (centerMatrix data refinementTarget refinementPositive)

namespace RequestCertificate

/-- The finite radius and budget checks imply the original universal box
positivity contract. -/
theorem compatible_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RequestCertificate data vector nonzero target positive)
    (candidate : GaussianMatrix genus)
    (compatible : forall row column : Fin genus,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate row column -
            data.omegaCenter certificate.refinementTarget
              certificate.refinementPositive row column) <=
        data.omegaRadiusSq certificate.refinementTarget
          certificate.refinementPositive row column) :
    certificate.epsilon < imaginaryQuadraticForm vector candidate := by
  let center := centerMatrix data certificate.refinementTarget
    certificate.refinementPositive
  let perturbation : Coordinate :=
    RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
      RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
        vector row * (candidate row column - center row column).im *
          vector column
  have perturbationLower : -totalBudget certificate.budget <= perturbation := by
    unfold totalBudget perturbation
    rw [← RFAP.ConstructiveFiniteMatrix.sumFin_neg]
    apply sumFin_mono
    intro row
    rw [← RFAP.ConstructiveFiniteMatrix.sumFin_neg]
    apply sumFin_mono
    intro column
    let delta := candidate row column - center row column
    have compatibleDistance :
        RFAP.ConstructiveGaussian.Gaussian.normSq delta <=
          data.omegaRadiusSq certificate.refinementTarget
            certificate.refinementPositive row column := by
      simpa only [delta, center, centerMatrix_apply] using
        compatible row column
    have distance : RFAP.ConstructiveGaussian.Gaussian.normSq delta <
        (certificate.radius row column) ^ 2 :=
      compatibleDistance.trans_lt
        (certificate.radiusSq_lt_sq row column)
    have bounds := imaginary_bounds_of_normSq_lt_sq
      (certificate.radius_positive row column) distance
    exact certificate.weighted_lower row column delta.im bounds.1 bounds.2
  have shiftedMargin : certificate.epsilon <
      imaginaryQuadraticForm vector center -
        totalBudget certificate.budget := by
    calc
      certificate.epsilon =
          (certificate.epsilon + totalBudget certificate.budget) +
            -(totalBudget certificate.budget) := by ring1
      _ < imaginaryQuadraticForm vector center +
            -(totalBudget certificate.budget) :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          certificate.center_margin (-(totalBudget certificate.budget))
      _ = imaginaryQuadraticForm vector center -
            totalBudget certificate.budget := by ring1
  have perturbedLower :
      imaginaryQuadraticForm vector center - totalBudget certificate.budget <=
        imaginaryQuadraticForm vector center + perturbation := by
    simpa only [sub_eq_add_neg, add_comm] using
      add_le_add_left perturbationLower
        (imaginaryQuadraticForm vector center)
  have identity := imaginaryQuadraticForm_eq_center_add_perturbation
    vector candidate center
  rw [show imaginaryQuadraticForm vector candidate =
      imaginaryQuadraticForm vector center + perturbation by
        simpa only [perturbation] using identity]
  exact shiftedMargin.trans_le perturbedLower

/-- Package the derived robustness theorem as the public positivity request
certificate. -/
def toPositiveRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RequestCertificate data vector nonzero target positive) :
    PositiveRequestCertificate data vector nonzero target positive where
  refinementTarget := certificate.refinementTarget
  refinementPositive := certificate.refinementPositive
  refinement_lt_target := certificate.refinement_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  compatible_positive := certificate.compatible_positive

end RequestCertificate

/-- Minimal finite robustness input for one positivity request.  All
entrywise budgets and weighted perturbation bounds are computed from the
displayed rational vector and radius matrix. -/
structure RadiusCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  refinementTarget : Coordinate
  refinementPositive : 0 < refinementTarget
  refinement_lt_target : refinementTarget < target
  epsilon : Coordinate
  epsilon_positive : 0 < epsilon
  radius : RationalMatrix genus
  radius_positive : forall row column, 0 < radius row column
  radiusSq_lt_sq : forall row column,
    data.omegaRadiusSq refinementTarget refinementPositive row column <
      (radius row column) ^ 2
  center_margin :
    epsilon + totalBudget (automaticBudget vector radius) <
      imaginaryQuadraticForm vector
        (centerMatrix data refinementTarget refinementPositive)

namespace RadiusCertificate

/-- Expand the minimal radius certificate into the detailed finite
perturbation certificate. -/
def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RadiusCertificate data vector nonzero target positive) :
    RequestCertificate data vector nonzero target positive where
  refinementTarget := certificate.refinementTarget
  refinementPositive := certificate.refinementPositive
  refinement_lt_target := certificate.refinement_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  radius := certificate.radius
  radius_positive := certificate.radius_positive
  radiusSq_lt_sq := certificate.radiusSq_lt_sq
  budget := automaticBudget vector certificate.radius
  budget_nonnegative := automaticBudget_nonnegative vector certificate.radius
    (fun row column => (certificate.radius_positive row column).le)
  weighted_lower := automaticBudget_weighted_lower vector certificate.radius
    certificate.radius_positive
  center_margin := certificate.center_margin

end RadiusCertificate

/-- Minimal positivity input for one finite request.  The caller selects a
positive rational linear radius whose square is below the public target and
proves one strict rational centre margin.  Sampling, entry radii, budgets, and
perturbation inequalities are then computed canonically. -/
structure MarginCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    squaredRefinementTarget refinementRadius < target
  center_exceeds_budget :
    totalBudget (automaticBudget vector
      (automaticRadius data refinementRadius refinementRadiusPositive)) <
      imaginaryQuadraticForm vector
        (centerMatrix data (squaredRefinementTarget refinementRadius)
          (squaredRefinementTarget_positive refinementRadiusPositive))

namespace MarginCertificate

/-- The total rational perturbation budget determined by the selected finite
refinement. -/
def budget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    Coordinate :=
  totalBudget (automaticBudget vector
    (automaticRadius data certificate.refinementRadius
      certificate.refinementRadiusPositive))

/-- The displayed rational quadratic-form value at the selected finite
refinement. -/
def centerValue {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    Coordinate :=
  imaginaryQuadraticForm vector
    (centerMatrix data
      (squaredRefinementTarget certificate.refinementRadius)
      (squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))

/-- The exact positive rational clearance left after subtracting every finite
perturbation budget. -/
def margin {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    Coordinate :=
  certificate.centerValue - certificate.budget

theorem margin_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    0 < certificate.margin :=
  RFAP.ConstructiveFraction.sub_pos_direct certificate.center_exceeds_budget

/-- A canonical positive output margin: half of the clearance remaining after
all finite perturbation budgets. -/
def epsilon {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    Coordinate :=
  certificate.margin / 2

theorem epsilon_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    0 < certificate.epsilon := by
  unfold epsilon
  exact RFAP.ConstructiveFraction.div_pos_direct
    certificate.margin_positive (by decide)

theorem epsilon_add_budget_lt_center {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    certificate.epsilon + certificate.budget < certificate.centerValue := by
  calc
    certificate.epsilon + certificate.budget <
        certificate.margin + certificate.budget :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        (half_lt_self certificate.margin_positive) certificate.budget
    _ = certificate.centerValue := by
      unfold margin budget centerValue
      ring1

/-- Expand the centre-margin witness into the canonical positive radii and
the detailed finite robustness certificate. -/
def toRadiusCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : MarginCertificate data vector nonzero target positive) :
    RadiusCertificate data vector nonzero target positive where
  refinementTarget := squaredRefinementTarget certificate.refinementRadius
  refinementPositive := squaredRefinementTarget_positive
    certificate.refinementRadiusPositive
  refinement_lt_target := certificate.refinementTarget_lt_target
  epsilon := certificate.epsilon
  epsilon_positive := certificate.epsilon_positive
  radius := automaticRadius data certificate.refinementRadius
    certificate.refinementRadiusPositive
  radius_positive := automaticRadius_positive data
    certificate.refinementRadius certificate.refinementRadiusPositive
  radiusSq_lt_sq := omegaRadiusSq_lt_automaticRadius_sq data
    certificate.refinementRadius certificate.refinementRadiusPositive
  center_margin := by
    simpa only [budget, centerValue] using
      certificate.epsilon_add_budget_lt_center

end MarginCertificate

/-- Pointwise positivity supplied entirely through finite rational robustness
checks at each request. -/
structure Certificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    MarginCertificate data vector nonzero target positive

namespace Certificate

/-- Forget the explicit radii and budgets only after proving the public
pointwise positivity contract. -/
def toPointwisePositivity {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve} (certificate : Certificate data) :
    PointwisePositivity data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRadiusCertificate.toRequestCertificate.toPositiveRequestCertificate

end Certificate

end CCL.Riemann.FinitePositivity
