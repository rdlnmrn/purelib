import DivineProportions.Conics.Center
import DivineProportions.Trigonometry.QuadranceToLine

/-!
# Divine Proportions, Exercise 15.6: ribbons

A ribbon is kept as finite coefficient data for the cleared equation
`(ax+by+c)² = K(a²+b²)`.  The presentation retains its arbitrary nonzero
conic scale, while equality of displayed lines remains the quotient-free
relation `Line.Equivalent`.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Ribbon

/-- The cleared conic attached to `Q(X,l)=K`. -/
def conic (line : Line K) (ribbonQuadrance : K) : Conic K where
  d := line.a ^ 2
  e := 2 * line.a * line.b
  f := line.b ^ 2
  a := 2 * line.a * line.c
  b := 2 * line.b * line.c
  c := line.c ^ 2 - ribbonQuadrance * lineNorm line
  quadratic_nonzero := by
    rcases line.direction_nonzero with lineANonzero | lineBNonzero
    · exact Or.inl (by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero lineANonzero lineANonzero)
    · exact Or.inr (Or.inr (by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero lineBNonzero lineBNonzero))

/-- Data for a scaled six-coefficient ribbon certificate. -/
structure PresentationData (source : Conic K) (line : Line K)
    (ribbonQuadrance : K) where
  lineNonNull : ¬ line.IsNull
  scale : K
  scaleNonzero : scale ≠ 0
  dEquation : source.d = scale * line.a ^ 2
  eEquation : source.e = scale * (2 * line.a * line.b)
  fEquation : source.f = scale * line.b ^ 2
  aEquation : source.a = scale * (2 * line.a * line.c)
  bEquation : source.b = scale * (2 * line.b * line.c)
  cEquation : source.c =
    scale * (line.c ^ 2 - ribbonQuadrance * lineNorm line)

/-- The proposition asserting an explicitly witnessed ribbon presentation. -/
def IsPresentation (source : Conic K) (line : Line K)
    (ribbonQuadrance : K) : Prop :=
  Nonempty (PresentationData source line ribbonQuadrance)

/-- A ribbon is a conic with one explicitly exhibited valid presentation. -/
def IsRibbon (source : Conic K) : Prop :=
  ∃ line : Line K, ∃ ribbonQuadrance : K,
    IsPresentation source line ribbonQuadrance

/-- The canonical cleared coefficient record has scale one. -/
theorem conic_isPresentation [Nontrivial K]
    (line : Line K) (ribbonQuadrance : K)
    (lineNonNull : ¬ line.IsNull) :
    IsPresentation (conic line ribbonQuadrance) line ribbonQuadrance := by
  refine ⟨
    { lineNonNull := lineNonNull
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  all_goals (unfold conic; ring1)

/-- Direct expansion of the cleared ribbon equation. -/
theorem conic_evaluate (line : Line K) (ribbonQuadrance : K)
    (point : Point K) :
    (conic line ribbonQuadrance).evaluate point =
      (line.a * point.x + line.b * point.y + line.c) ^ 2 -
        ribbonQuadrance * lineNorm line := by
  unfold conic Conic.evaluate lineNorm
  ring1

/-- Expansion of an arbitrarily scaled ribbon presentation. -/
theorem PresentationData.evaluate {source : Conic K} {line : Line K}
    {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (point : Point K) :
    source.evaluate point =
      presentation.scale *
        ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
          ribbonQuadrance * lineNorm line) := by
  unfold Conic.evaluate
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  ring1

private theorem eq_zero_of_nonzero_mul_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor * factor⁻¹) * value := by rw [factorCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

private theorem eq_of_nonzero_mul_left
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have productZero : factor * (left - right) = 0 := by
    calc
      factor * (left - right) = factor * left - factor * right := by ring1
      _ = 0 := by rw [productsEqual]; ring1
  have differenceZero :=
    eq_zero_of_nonzero_mul_left factorNonzero productZero
  calc
    left = (left - right) + right := by ring1
    _ = right := by rw [differenceZero]; ring1

/-- The canonical conic has exactly the metric locus `Q(X,l)=K`. -/
theorem conic_contains_iff [DecidableEq K]
    (line : Line K) (ribbonQuadrance : K)
    (lineNonNull : ¬ line.IsNull) (point : Point K) :
    (conic line ribbonQuadrance).Contains point ↔
      pointLineQuadrance point line lineNonNull = ribbonQuadrance := by
  have normNonzero : lineNorm line ≠ 0 := lineNonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  rw [Conic.Contains, conic_evaluate,
    pointLineQuadrance_formula point line lineNonNull]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  let numerator :=
    (line.a * point.x + line.b * point.y + line.c) ^ 2
  change numerator - ribbonQuadrance * lineNorm line = 0 ↔
    numerator * (lineNorm line)⁻¹ = ribbonQuadrance
  constructor
  · intro clearedEquation
    calc
      numerator * (lineNorm line)⁻¹ =
          (numerator - ribbonQuadrance * lineNorm line) *
              (lineNorm line)⁻¹ +
            ribbonQuadrance *
              (lineNorm line * (lineNorm line)⁻¹) := by ring1
      _ = ribbonQuadrance := by rw [clearedEquation, normCancel]; ring1
  · intro quotientEquation
    have numeratorEquation :
        numerator = ribbonQuadrance * lineNorm line := by
      calc
        numerator = numerator *
            (lineNorm line * (lineNorm line)⁻¹) := by rw [normCancel]; ring1
        _ = (numerator * (lineNorm line)⁻¹) * lineNorm line := by ring1
        _ = ribbonQuadrance * lineNorm line := by rw [quotientEquation]
    rw [numeratorEquation]
    ring1

/-- Every scaled ribbon presentation recovers the source's metric equation. -/
theorem PresentationData.contains_iff [DecidableEq K]
    {source : Conic K} {line : Line K} {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (point : Point K) :
    source.Contains point ↔
      pointLineQuadrance point line presentation.lineNonNull =
        ribbonQuadrance := by
  constructor
  · intro sourceContains
    have scaledZero :
        presentation.scale *
          ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
            ribbonQuadrance * lineNorm line) = 0 := by
      calc
        presentation.scale *
            ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
              ribbonQuadrance * lineNorm line) = source.evaluate point :=
          (presentation.evaluate point).symm
        _ = 0 := sourceContains
    have clearedZero :=
      eq_zero_of_nonzero_mul_left presentation.scaleNonzero scaledZero
    apply (conic_contains_iff line ribbonQuadrance
      presentation.lineNonNull point).1
    unfold Conic.Contains
    rw [conic_evaluate]
    exact clearedZero
  · intro metricEquation
    have canonicalContains :=
      (conic_contains_iff line ribbonQuadrance
        presentation.lineNonNull point).2 metricEquation
    have clearedZero :
        (line.a * point.x + line.b * point.y + line.c) ^ 2 -
            ribbonQuadrance * lineNorm line = 0 := by
      unfold Conic.Contains at canonicalContains
      rw [conic_evaluate] at canonicalContains
      exact canonicalContains
    unfold Conic.Contains
    rw [presentation.evaluate, clearedZero]
    ring1

/-- The centers of a presented ribbon are exactly the points on its defining
line.  This strengthens the last clause of Exercise 15.6 to an equivalence. -/
theorem PresentationData.isCenter_iff_contains
    {source : Conic K} {line : Line K} {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (twoNonzero : (2 : K) ≠ 0) (point : Point K) :
    source.IsCenter point ↔ line.Contains point := by
  let lineValue := line.a * point.x + line.b * point.y + line.c
  have firstIdentity :
      2 * source.d * point.x + source.e * point.y + source.a =
        2 * presentation.scale * line.a * lineValue := by
    rw [presentation.dEquation, presentation.eEquation,
      presentation.aEquation]
    unfold lineValue
    ring1
  have secondIdentity :
      source.e * point.x + 2 * source.f * point.y + source.b =
        2 * presentation.scale * line.b * lineValue := by
    rw [presentation.eEquation, presentation.fEquation,
      presentation.bEquation]
    unfold lineValue
    ring1
  change
    (2 * source.d * point.x + source.e * point.y + source.a = 0 ∧
      source.e * point.x + 2 * source.f * point.y + source.b = 0) ↔
        lineValue = 0
  constructor
  · intro centerEquations
    rcases line.direction_nonzero with lineANonzero | lineBNonzero
    · apply eq_zero_of_nonzero_mul_left
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero
            presentation.scaleNonzero) lineANonzero)
      calc
        2 * presentation.scale * line.a * lineValue =
            2 * source.d * point.x + source.e * point.y + source.a :=
          firstIdentity.symm
        _ = 0 := centerEquations.1
    · apply eq_zero_of_nonzero_mul_left
        (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero
            presentation.scaleNonzero) lineBNonzero)
      calc
        2 * presentation.scale * line.b * lineValue =
            source.e * point.x + 2 * source.f * point.y + source.b :=
          secondIdentity.symm
        _ = 0 := centerEquations.2
  · intro onLine
    constructor
    · calc
        2 * source.d * point.x + source.e * point.y + source.a =
            2 * presentation.scale * line.a * lineValue := firstIdentity
        _ = 0 := by rw [onLine]; ring1
    · calc
        source.e * point.x + 2 * source.f * point.y + source.b =
            2 * presentation.scale * line.b * lineValue := secondIdentity
        _ = 0 := by rw [onLine]; ring1

private theorem line_equivalent_of_same_contains
    (first second : Line K)
    (sameContains : ∀ point : Point K,
      first.Contains point ↔ second.Contains point) :
    first.Equivalent second := by
  rcases first.direction_nonzero with firstANonzero | firstBNonzero
  · let base : Point K := ⟨-first.c / first.a, 0⟩
    let shifted : Point K := ⟨base.x + first.b, base.y - first.a⟩
    have quotientCancel : (-first.c / first.a) * first.a = -first.c :=
      RFAP.ExplicitField.div_mul_cancel (-first.c) firstANonzero
    have firstBase : first.Contains base := by
      unfold base Line.Contains
      calc
        first.a * (-first.c / first.a) + first.b * 0 + first.c =
            (-first.c / first.a) * first.a + first.c := by ring1
        _ = 0 := by rw [quotientCancel]; ring1
    have firstShifted : first.Contains shifted := by
      have baseEquation := firstBase
      unfold Line.Contains at baseEquation
      unfold shifted Line.Contains
      calc
        first.a * (base.x + first.b) +
              first.b * (base.y - first.a) + first.c =
            (first.a * base.x + first.b * base.y + first.c) +
              (first.a * first.b - first.b * first.a) := by ring1
        _ = 0 := by rw [baseEquation]; ring1
    have secondBase := (sameContains base).1 firstBase
    have secondShifted := (sameContains shifted).1 firstShifted
    have directionDifference :
        second.a * first.b - second.b * first.a = 0 := by
      have baseEquation := secondBase
      have shiftedEquation := secondShifted
      unfold Line.Contains at baseEquation shiftedEquation
      unfold shifted at shiftedEquation
      calc
        second.a * first.b - second.b * first.a =
            (second.a * (base.x + first.b) +
                second.b * (base.y - first.a) + second.c) -
              (second.a * base.x + second.b * base.y + second.c) := by ring1
        _ = 0 := by rw [shiftedEquation, baseEquation]; ring1
    have parallel : first.Parallel second := by
      unfold Line.Parallel
      calc
        first.a * second.b - second.a * first.b =
            -(second.a * first.b - second.b * first.a) := by ring1
        _ = 0 := by rw [directionDifference]; ring1
    exact line_equivalent_of_parallel_and_common_point first second base
      parallel firstBase secondBase
  · let base : Point K := ⟨0, -first.c / first.b⟩
    let shifted : Point K := ⟨base.x + first.b, base.y - first.a⟩
    have quotientCancel : (-first.c / first.b) * first.b = -first.c :=
      RFAP.ExplicitField.div_mul_cancel (-first.c) firstBNonzero
    have firstBase : first.Contains base := by
      unfold base Line.Contains
      calc
        first.a * 0 + first.b * (-first.c / first.b) + first.c =
            (-first.c / first.b) * first.b + first.c := by ring1
        _ = 0 := by rw [quotientCancel]; ring1
    have firstShifted : first.Contains shifted := by
      have baseEquation := firstBase
      unfold Line.Contains at baseEquation
      unfold shifted Line.Contains
      calc
        first.a * (base.x + first.b) +
              first.b * (base.y - first.a) + first.c =
            (first.a * base.x + first.b * base.y + first.c) +
              (first.a * first.b - first.b * first.a) := by ring1
        _ = 0 := by rw [baseEquation]; ring1
    have secondBase := (sameContains base).1 firstBase
    have secondShifted := (sameContains shifted).1 firstShifted
    have directionDifference :
        second.a * first.b - second.b * first.a = 0 := by
      have baseEquation := secondBase
      have shiftedEquation := secondShifted
      unfold Line.Contains at baseEquation shiftedEquation
      unfold shifted at shiftedEquation
      calc
        second.a * first.b - second.b * first.a =
            (second.a * (base.x + first.b) +
                second.b * (base.y - first.a) + second.c) -
              (second.a * base.x + second.b * base.y + second.c) := by ring1
        _ = 0 := by rw [shiftedEquation, baseEquation]; ring1
    have parallel : first.Parallel second := by
      unfold Line.Parallel
      calc
        first.a * second.b - second.a * first.b =
            -(second.a * first.b - second.b * first.a) := by ring1
        _ = 0 := by rw [directionDifference]; ring1
    exact line_equivalent_of_parallel_and_common_point first second base
      parallel firstBase secondBase

/-- Uniqueness part of Exercise 15.6: the line is unique up to its displayed
coefficient proportion, and the ribbon quadrance is literally unique. -/
theorem uniqueness
    (source : Conic K) (twoNonzero : (2 : K) ≠ 0)
    {firstLine secondLine : Line K}
    {firstQuadrance secondQuadrance : K}
    (firstPresentation : IsPresentation source firstLine firstQuadrance)
    (secondPresentation : IsPresentation source secondLine secondQuadrance) :
    firstLine.Equivalent secondLine ∧
      firstQuadrance = secondQuadrance := by
  rcases firstPresentation with ⟨first⟩
  rcases secondPresentation with ⟨second⟩
  have sameContains : ∀ point : Point K,
      firstLine.Contains point ↔ secondLine.Contains point := by
    intro point
    calc
      firstLine.Contains point ↔ source.IsCenter point :=
        (first.isCenter_iff_contains twoNonzero point).symm
      _ ↔ secondLine.Contains point :=
        second.isCenter_iff_contains twoNonzero point
  have linesEquivalent :=
    line_equivalent_of_same_contains firstLine secondLine sameContains
  rcases line_coefficient_scale_of_equivalent firstLine secondLine
      linesEquivalent with ⟨lineScale, secondA, secondB, secondC⟩
  have weightedScalesEqual :
      first.scale = second.scale * lineScale ^ 2 := by
    rcases firstLine.direction_nonzero with firstANonzero | firstBNonzero
    · have firstASquareNonzero : firstLine.a ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero firstANonzero firstANonzero
      apply eq_of_nonzero_mul_left firstASquareNonzero
      calc
        firstLine.a ^ 2 * first.scale = source.d := by
          rw [first.dEquation]
          ring1
        _ = second.scale * secondLine.a ^ 2 := second.dEquation
        _ = firstLine.a ^ 2 * (second.scale * lineScale ^ 2) := by
          rw [secondA]
          ring1
    · have firstBSquareNonzero : firstLine.b ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero firstBNonzero firstBNonzero
      apply eq_of_nonzero_mul_left firstBSquareNonzero
      calc
        firstLine.b ^ 2 * first.scale = source.f := by
          rw [first.fEquation]
          ring1
        _ = second.scale * secondLine.b ^ 2 := second.fEquation
        _ = firstLine.b ^ 2 * (second.scale * lineScale ^ 2) := by
          rw [secondB]
          ring1
  have secondNorm :
      lineNorm secondLine = lineScale ^ 2 * lineNorm firstLine := by
    unfold lineNorm
    rw [secondA, secondB]
    ring1
  have scaledConstantsEqual :
      first.scale *
          (firstLine.c ^ 2 - firstQuadrance * lineNorm firstLine) =
        first.scale *
          (firstLine.c ^ 2 - secondQuadrance * lineNorm firstLine) := by
    calc
      first.scale *
          (firstLine.c ^ 2 - firstQuadrance * lineNorm firstLine) =
        source.c := first.cEquation.symm
      _ = second.scale *
          (secondLine.c ^ 2 - secondQuadrance * lineNorm secondLine) :=
        second.cEquation
      _ = (second.scale * lineScale ^ 2) *
          (firstLine.c ^ 2 - secondQuadrance * lineNorm firstLine) := by
        rw [secondC, secondNorm]
        ring1
      _ = first.scale *
          (firstLine.c ^ 2 - secondQuadrance * lineNorm firstLine) := by
        rw [← weightedScalesEqual]
  have constantsEqual :=
    eq_of_nonzero_mul_left first.scaleNonzero scaledConstantsEqual
  have normProductZero :
      lineNorm firstLine * (firstQuadrance - secondQuadrance) = 0 := by
    calc
      lineNorm firstLine * (firstQuadrance - secondQuadrance) =
          -((firstLine.c ^ 2 - firstQuadrance * lineNorm firstLine) -
            (firstLine.c ^ 2 - secondQuadrance * lineNorm firstLine)) := by
        ring1
      _ = 0 := by rw [constantsEqual]; ring1
  have quadranceDifferenceZero :=
    eq_zero_of_nonzero_mul_left first.lineNonNull normProductZero
  refine ⟨linesEquivalent, ?_⟩
  calc
    firstQuadrance =
        (firstQuadrance - secondQuadrance) + secondQuadrance := by ring1
    _ = secondQuadrance := by rw [quadranceDifferenceZero]; ring1

/-- Exercise 15.6 packaged from the definition: a ribbon has a unique line
and quadrance, and every point on that line is an explicit center. -/
theorem exercise_15_6
    (source : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isRibbon : IsRibbon source) :
    ∃ line : Line K, ∃ ribbonQuadrance : K,
      IsPresentation source line ribbonQuadrance ∧
        (∀ otherLine : Line K, ∀ otherQuadrance : K,
          IsPresentation source otherLine otherQuadrance →
            line.Equivalent otherLine ∧
              ribbonQuadrance = otherQuadrance) ∧
        ∀ point : Point K,
          line.Contains point → source.IsCenter point := by
  rcases isRibbon with ⟨line, ribbonQuadrance, presentation⟩
  refine ⟨line, ribbonQuadrance, presentation, ?_, ?_⟩
  · intro otherLine otherQuadrance otherPresentation
    exact uniqueness source twoNonzero presentation otherPresentation
  · intro point onLine
    rcases presentation with ⟨presentation⟩
    exact (presentation.isCenter_iff_contains twoNonzero point).2 onLine

end Ribbon

end DivineProportions
