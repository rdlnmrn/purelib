import DivineProportions.Polygons.CornerTriangle
import DivineProportions.Plane.ReflectionComposition
import DivineProportions.Isometries.Models
import mathlib.Tactic.QuotientFreeOmega

/-!
# Divine Proportions, regular polygon construction

The source uses a doubly infinite reflection sequence.  Here every line and
point is obtained from the already executable natural-number iterator.  A
request for vertex `k` computes exactly the first `k` reflection steps.

The point-reflection product identity below is the finite natural-index form
of Exercise 14.1.  It is then used to prove that the closed formula
`A₂ₖ = σ_{lₖ}(A₀)` agrees with the source's successive construction through
the intervening mirrors `l₂ₖ₊₁`.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Point reflection is independent of the chosen nonzero coefficient
representative of a line. -/
theorem reflectPoint_eq_of_equivalent [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (equivalent : first.Equivalent second) (point : Point K) :
    reflectPoint first firstNonNull point =
      reflectPoint second secondNonNull point := by
  rcases line_coefficient_scale_of_equivalent first second equivalent with
    ⟨scale, secondA, secondB, secondC⟩
  have scaleNonzero : scale ≠ 0 := by
    intro scaleZero
    have secondAZero : second.a = 0 := by rw [secondA, scaleZero]; ring1
    have secondBZero : second.b = 0 := by rw [secondB, scaleZero]; ring1
    exact second.direction_nonzero.elim
      (fun nonzero => nonzero secondAZero)
      (fun nonzero => nonzero secondBZero)
  have scaleSquareNonzero : scale ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
  have secondNorm : lineNorm second = scale ^ 2 * lineNorm first := by
    unfold lineNorm
    rw [secondA, secondB]
    ring1
  let firstXNumerator : K :=
    (first.b ^ 2 - first.a ^ 2) * point.x -
      2 * first.a * first.b * point.y - 2 * first.a * first.c
  let firstYNumerator : K :=
    -2 * first.a * first.b * point.x +
      (first.a ^ 2 - first.b ^ 2) * point.y - 2 * first.b * first.c
  have secondXNumerator :
      (second.b ^ 2 - second.a ^ 2) * point.x -
          2 * second.a * second.b * point.y - 2 * second.a * second.c =
        scale ^ 2 * firstXNumerator := by
    unfold firstXNumerator
    rw [secondA, secondB, secondC]
    ring1
  have secondYNumerator :
      -2 * second.a * second.b * point.x +
          (second.a ^ 2 - second.b ^ 2) * point.y -
            2 * second.b * second.c =
        scale ^ 2 * firstYNumerator := by
    unfold firstYNumerator
    rw [secondA, secondB, secondC]
    ring1
  rw [reflectPoint_formula, reflectPoint_formula]
  apply Point.ext
  · change
      firstXNumerator / lineNorm first =
        ((second.b ^ 2 - second.a ^ 2) * point.x -
          2 * second.a * second.b * point.y - 2 * second.a * second.c) /
            lineNorm second
    have secondNormNonzero : lineNorm second ≠ 0 := secondNonNull
    apply eq_of_mul_eq_mul_right secondNormNonzero
    rw [RFAP.ExplicitField.div_mul_cancel
        (b := lineNorm second) _ secondNormNonzero,
      secondXNumerator, secondNorm]
    calc
      (firstXNumerator / lineNorm first) *
          (scale ^ 2 * lineNorm first) =
        scale ^ 2 *
          ((firstXNumerator / lineNorm first) * lineNorm first) := by ring1
      _ = scale ^ 2 * firstXNumerator := by
        rw [RFAP.ExplicitField.div_mul_cancel
          (b := lineNorm first) _ firstNonNull]
  · change
      firstYNumerator / lineNorm first =
        (-2 * second.a * second.b * point.x +
          (second.a ^ 2 - second.b ^ 2) * point.y -
            2 * second.b * second.c) / lineNorm second
    have secondNormNonzero : lineNorm second ≠ 0 := secondNonNull
    apply eq_of_mul_eq_mul_right secondNormNonzero
    rw [RFAP.ExplicitField.div_mul_cancel
        (b := lineNorm second) _ secondNormNonzero,
      secondYNumerator, secondNorm]
    calc
      (firstYNumerator / lineNorm first) *
          (scale ^ 2 * lineNorm first) =
        scale ^ 2 *
          ((firstYNumerator / lineNorm first) * lineNorm first) := by ring1
      _ = scale ^ 2 * firstYNumerator := by
        rw [RFAP.ExplicitField.div_mul_cancel
          (b := lineNorm first) _ firstNonNull]

/-- Reflection of a point in the requested line of a finite reflection
sequence. -/
def reflectionPointAt [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) (point : Point K) : Point K :=
  reflectPoint (reflectionLineAt initial index)
    (reflectionLineAt_nonNull initial index) point

/-- Every finite point reflection is an involution. -/
theorem reflectionPointAt_involutive [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) (point : Point K) :
    reflectionPointAt initial index
        (reflectionPointAt initial index point) = point := by
  exact reflectPoint_involutive
    (reflectionLineAt initial index)
    (reflectionLineAt_nonNull initial index) point

/-- The point reflections satisfy the same conjugation recurrence as the
line iterator. -/
theorem reflectionPointAt_succ_succ [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) (point : Point K) :
    reflectionPointAt initial (index + 2) point =
      reflectionPointAt initial (index + 1)
        (reflectionPointAt initial index
          (reflectionPointAt initial (index + 1) point)) := by
  have conjugation := reflection_composition
    (reflectionLineAt initial index)
    (reflectionLineAt initial (index + 1))
    (reflectionLineAt_nonNull initial index)
    (reflectionLineAt_nonNull initial (index + 1))
    (reflectionPointAt initial (index + 1) point)
  unfold reflectionPointAt at conjugation ⊢
  rw [reflectPoint_involutive] at conjugation
  simpa only [reflectionLineAt_succ_succ] using conjugation.symm

/-- Consecutive reflection products are independent of their finite starting
index. -/
theorem reflectionPointAt_adjacent_product [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) (point : Point K) :
    reflectionPointAt initial (index + 1)
        (reflectionPointAt initial index point) =
      reflectionPointAt initial 1 (reflectionPointAt initial 0 point) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      calc
        reflectionPointAt initial (Nat.succ index + 1)
            (reflectionPointAt initial (Nat.succ index) point) =
          reflectionPointAt initial (index + 1)
            (reflectionPointAt initial index point) := by
              rw [show Nat.succ index + 1 = index + 2 by omega0,
                show Nat.succ index = index + 1 by omega0,
                reflectionPointAt_succ_succ,
                reflectionPointAt_involutive]
        _ = reflectionPointAt initial 1
            (reflectionPointAt initial 0 point) := inductionHypothesis

/-- Shifting both mirrors forward once leaves their composed reflection
unchanged. -/
theorem reflectionPointAt_product_shift_one
    [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (first second : Nat) (point : Point K) :
    reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (second + 1) point) =
      reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
  have secondAtReflected :=
    reflectionPointAt_adjacent_product initial second
      (reflectionPointAt initial second point)
  rw [reflectionPointAt_involutive] at secondAtReflected
  have firstAtSecond :=
    reflectionPointAt_adjacent_product initial first
      (reflectionPointAt initial second point)
  have insideEquality :
      reflectionPointAt initial (second + 1) point =
        reflectionPointAt initial (first + 1)
          (reflectionPointAt initial first
            (reflectionPointAt initial second point)) :=
    secondAtReflected.trans firstAtSecond.symm
  calc
    reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (second + 1) point) =
      reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (first + 1)
          (reflectionPointAt initial first
            (reflectionPointAt initial second point))) := by
              rw [insideEquality]
    _ = reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
          rw [reflectionPointAt_involutive]

/-- Exercise 14.1, at the agreed finite boundary: for any requested natural
indices, simultaneously shifting the two mirrors by `offset` leaves their
composed point reflection unchanged. -/
theorem exercise_14_1 [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (first second offset : Nat)
    (point : Point K) :
    reflectionPointAt initial (first + offset)
        (reflectionPointAt initial (second + offset) point) =
      reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
  induction offset with
  | zero => simp
  | succ offset inductionHypothesis =>
      calc
        reflectionPointAt initial (first + Nat.succ offset)
            (reflectionPointAt initial (second + Nat.succ offset) point) =
          reflectionPointAt initial ((first + offset) + 1)
            (reflectionPointAt initial ((second + offset) + 1) point) := by
              simp only [Nat.add_succ]
        _ = reflectionPointAt initial (first + offset)
            (reflectionPointAt initial (second + offset) point) :=
          reflectionPointAt_product_shift_one initial
            (first + offset) (second + offset) point
        _ = reflectionPointAt initial first
            (reflectionPointAt initial second point) := inductionHypothesis

/-- A finite regular star of requested order.  The two closing equations are
exactly the data needed to continue the second-order reflection recurrence
periodically; pairwise nonparallelism ranges only over the finite prefix. -/
structure FiniteRegularStar (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] (order : Nat) where
  initial : ReflectionPair K
  orderAtLeastTwo : 2 ≤ order
  pairwiseNonparallel :
    ∀ first second : Fin order, first ≠ second →
      ¬ (reflectionLineAt initial first.val).Parallel
        (reflectionLineAt initial second.val)
  closesAtOrder :
    (reflectionLineAt initial order).Equivalent initial.previous
  closesAfterOrder :
    (reflectionLineAt initial (order + 1)).Equivalent initial.current

namespace FiniteRegularStar

variable [DecidableEq K] {order : Nat}

/-- The first two lines of a finite regular star are nonparallel. -/
theorem initial_nonparallel (star : FiniteRegularStar K order) :
    ¬ star.initial.previous.Parallel star.initial.current := by
  let first : Fin order := ⟨0, by
    have lower := star.orderAtLeastTwo
    omega0⟩
  let second : Fin order := ⟨1, by
    have lower := star.orderAtLeastTwo
    omega0⟩
  have different : first ≠ second := by
    intro equal
    have values : (0 : Nat) = 1 := by
      simpa only [first, second] using congrArg Fin.val equal
    exact Nat.zero_ne_one values
  simpa only [first, second, reflectionLineAt_zero,
    show reflectionLineAt star.initial 1 = star.initial.current by rfl] using
      star.pairwiseNonparallel first second different

/-- The explicit common intersection of the first two star lines. -/
def center (star : FiniteRegularStar K order) : Point K :=
  lineIntersection star.initial.previous star.initial.current
    star.initial_nonparallel

theorem previous_contains_center (star : FiniteRegularStar K order) :
    star.initial.previous.Contains star.center :=
  lineIntersection_on_first star.initial.previous star.initial.current
    star.initial_nonparallel

theorem current_contains_center (star : FiniteRegularStar K order) :
    star.initial.current.Contains star.center :=
  lineIntersection_on_second star.initial.previous star.initial.current
    star.initial_nonparallel

/-- Every requested line in the finite recurrence passes through the
explicit center. -/
theorem lineAt_contains_center (star : FiniteRegularStar K order)
    (index : Nat) :
    (reflectionLineAt star.initial index).Contains star.center :=
  reflectionLineAt_contains star.initial star.center
    star.previous_contains_center star.current_contains_center index

/-- The two closing representatives propagate through every requested
finite continuation of the second-order line recurrence. -/
theorem lineAt_add_order_equivalent [Nontrivial K]
    (star : FiniteRegularStar K order) (start : Nat) :
    (reflectionLineAt star.initial (start + order)).Equivalent
      (reflectionLineAt star.initial start) := by
  have paired : ∀ index : Nat,
      (reflectionLineAt star.initial (index + order)).Equivalent
          (reflectionLineAt star.initial index) ∧
        (reflectionLineAt star.initial (index + 1 + order)).Equivalent
          (reflectionLineAt star.initial (index + 1)) := by
    intro index
    induction index with
    | zero =>
        constructor
        · simpa only [Nat.zero_add, reflectionLineAt_zero] using
            star.closesAtOrder
        · simpa only [Nat.zero_add, Nat.one_mul, Nat.add_comm order 1,
            show reflectionLineAt star.initial 1 = star.initial.current by rfl]
            using star.closesAfterOrder
    | succ index inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · have reflected := reflectLine_equivalent_of_equivalent
            (reflectionLineAt star.initial (index + order + 1))
            (reflectionLineAt star.initial (index + 1))
            (reflectionLineAt star.initial (index + order))
            (reflectionLineAt star.initial index)
            (reflectionLineAt_nonNull star.initial (index + order + 1))
            (reflectionLineAt_nonNull star.initial (index + 1))
            (by simpa only [Nat.add_assoc, Nat.add_comm 1 order,
                Nat.add_left_comm 1 index order] using inductionHypothesis.2)
            inductionHypothesis.1
          simpa only [Nat.succ_eq_add_one,
            show index + 1 + 1 + order = (index + order) + 2 by omega0,
            show index + 1 + 1 = index + 2 by omega0,
            reflectionLineAt_succ_succ] using reflected
  exact (paired start).1

end FiniteRegularStar

/-- A point on a mirror is fixed by its reflection.  This direct altitude-foot
proof does not require characteristic two to be excluded. -/
theorem reflectPoint_fixed_of_contains_direct
    (line : Line K) (lineNonNull : ¬ line.IsNull)
    (point : Point K) (contains : line.Contains point) :
    reflectPoint line lineNonNull point = point := by
  have pointEqualsFoot := altitudeFoot_unique point line lineNonNull point
    contains (altitudeThrough_contains point line)
  unfold reflectPoint
  rw [← pointEqualsFoot]
  apply Point.ext <;>
    unfold rotateInPoint <;>
    ring1

/-- The source's closed finite formula for the point labelled `A₂ₖ`. -/
def regularPolygonVertexAt [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (index : Nat) : Point K :=
  reflectionPointAt star.initial index initialPoint

/-- The closed formula starts at the supplied point on `l₀`. -/
theorem regularPolygonVertexAt_zero [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint) :
    regularPolygonVertexAt star initialPoint 0 = initialPoint := by
  exact reflectPoint_fixed_of_contains_direct star.initial.previous
    star.initial.previousNonNull initialPoint initialContains

/-- Exercise 14.1 identifies the closed formula with the source's successive
construction: the mirror between `A₂ₖ` and `A₂₍ₖ₊₁₎` is `l₂ₖ₊₁`. -/
theorem regularPolygonVertexAt_succ [Nontrivial K] [DecidableEq K]
    {order : Nat} (star : FiniteRegularStar K order)
    (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (index : Nat) :
    regularPolygonVertexAt star initialPoint (index + 1) =
      reflectionPointAt star.initial (2 * index + 1)
        (regularPolygonVertexAt star initialPoint index) := by
  have shifted := exercise_14_1 star.initial (index + 1) 0 index initialPoint
  have initialFixed := regularPolygonVertexAt_zero star initialPoint
    initialContains
  unfold regularPolygonVertexAt at initialFixed ⊢
  rw [initialFixed] at shifted
  simpa only [Nat.zero_add,
    show index + 1 + index = 2 * index + 1 by omega0] using shifted.symm

/-- The constructed point `A₂ₖ` lies on its radial line `l₂ₖ`. -/
theorem regularPolygonVertexAt_on_radial_line
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (index : Nat) :
    (reflectionLineAt star.initial (2 * index)).Contains
      (regularPolygonVertexAt star initialPoint index) := by
  have reflectedContains := reflectLine_contains_reflectPoint
    (reflectionLineAt star.initial index)
    (reflectionLineAt star.initial 0)
    (reflectionLineAt_nonNull star.initial index)
    initialPoint (by simpa only [reflectionLineAt_zero] using initialContains)
  have radialEquivalent := cyclic_reflection_left star.initial index 0
  have transferred := line_contains_of_equivalent radialEquivalent
    (reflectPoint (reflectionLineAt star.initial index)
      (reflectionLineAt_nonNull star.initial index) initialPoint)
    (by simpa only [Nat.zero_add] using reflectedContains)
  simpa only [Nat.zero_add, regularPolygonVertexAt, reflectionPointAt] using
    transferred

/-- Every constructed vertex has the same quadrance from the common center
as the supplied initial point. -/
theorem regularPolygonVertexAt_radius
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (index : Nat) :
    quadrance star.center (regularPolygonVertexAt star initialPoint index) =
      quadrance star.center initialPoint := by
  have centerFixed := reflectPoint_fixed_of_contains_direct
    (reflectionLineAt star.initial index)
    (reflectionLineAt_nonNull star.initial index) star.center
    (star.lineAt_contains_center index)
  have preserved := reflectPoint_preserves_quadrance
    (reflectionLineAt star.initial index)
    (reflectionLineAt_nonNull star.initial index) initialPoint star.center
  unfold regularPolygonVertexAt reflectionPointAt
  calc
    quadrance star.center
        (reflectPoint (reflectionLineAt star.initial index)
          (reflectionLineAt_nonNull star.initial index) initialPoint) =
      quadrance
        (reflectPoint (reflectionLineAt star.initial index)
          (reflectionLineAt_nonNull star.initial index) initialPoint)
        star.center := quadrance_symm _ _
    _ = quadrance
        (reflectPoint (reflectionLineAt star.initial index)
          (reflectionLineAt_nonNull star.initial index) initialPoint)
        (reflectPoint (reflectionLineAt star.initial index)
          (reflectionLineAt_nonNull star.initial index) star.center) := by
            rw [centerFixed]
    _ = quadrance initialPoint star.center := preserved
    _ = quadrance star.center initialPoint := quadrance_symm _ _

/-- No constructed vertex is the center when the supplied initial point is
not the center. -/
theorem regularPolygonVertexAt_ne_center
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (initialDistinct : initialPoint ≠ star.center) (index : Nat) :
    regularPolygonVertexAt star initialPoint index ≠ star.center := by
  intro vertexCenter
  apply initialDistinct
  have centerFixed := reflectPoint_fixed_of_contains_direct
    (reflectionLineAt star.initial index)
    (reflectionLineAt_nonNull star.initial index) star.center
    (star.lineAt_contains_center index)
  calc
    initialPoint = reflectionPointAt star.initial index
        (reflectionPointAt star.initial index initialPoint) :=
      (reflectionPointAt_involutive star.initial index initialPoint).symm
    _ = reflectionPointAt star.initial index star.center := by
      exact congrArg (reflectionPointAt star.initial index) vertexCenter
    _ = star.center := centerFixed

/-- The two finite closing representatives return the construction to its
initial point after exactly `order` requested vertices. -/
theorem regularPolygonVertexAt_closes
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint) :
    regularPolygonVertexAt star initialPoint order = initialPoint := by
  calc
    regularPolygonVertexAt star initialPoint order =
        reflectPoint (reflectionLineAt star.initial order)
          (reflectionLineAt_nonNull star.initial order) initialPoint := rfl
    _ = reflectPoint star.initial.previous star.initial.previousNonNull
        initialPoint := reflectPoint_eq_of_equivalent
          (reflectionLineAt star.initial order) star.initial.previous
          (reflectionLineAt_nonNull star.initial order)
          star.initial.previousNonNull star.closesAtOrder initialPoint
    _ = initialPoint := reflectPoint_fixed_of_contains_direct
      star.initial.previous star.initial.previousNonNull initialPoint
      initialContains

/-- Distinct nonparallel radial lines force their constructed vertices to be
distinct, since their only common point is the center. -/
theorem regularPolygonVertices_ne_of_radial_nonparallel
    [Nontrivial K] [DecidableEq K] {order : Nat}
    (star : FiniteRegularStar K order) (initialPoint : Point K)
    (initialContains : star.initial.previous.Contains initialPoint)
    (initialDistinct : initialPoint ≠ star.center)
    (first second : Nat)
    (radialNonparallel :
      ¬ (reflectionLineAt star.initial (2 * first)).Parallel
        (reflectionLineAt star.initial (2 * second))) :
    regularPolygonVertexAt star initialPoint first ≠
      regularPolygonVertexAt star initialPoint second := by
  intro verticesEqual
  have firstContains := regularPolygonVertexAt_on_radial_line star initialPoint
    initialContains first
  have secondContains := regularPolygonVertexAt_on_radial_line star initialPoint
    initialContains second
  rw [← verticesEqual] at secondContains
  have vertexIntersection := lineIntersection_unique
    (reflectionLineAt star.initial (2 * first))
    (reflectionLineAt star.initial (2 * second)) radialNonparallel
    (regularPolygonVertexAt star initialPoint first)
    firstContains secondContains
  have centerIntersection := lineIntersection_unique
    (reflectionLineAt star.initial (2 * first))
    (reflectionLineAt star.initial (2 * second)) radialNonparallel star.center
    (star.lineAt_contains_center (2 * first))
    (star.lineAt_contains_center (2 * second))
  exact (regularPolygonVertexAt_ne_center star initialPoint initialDistinct first)
    (vertexIntersection.trans centerIntersection.symm)

/-- The altitude through a point to a non-null line is itself non-null. -/
theorem altitudeThrough_nonNull_of_nonNull
    (point : Point K) (line : Line K) (lineNonNull : ¬ line.IsNull) :
    ¬ (altitudeThrough point line).IsNull := by
  intro altitudeNull
  apply lineNonNull
  unfold Line.IsNull at altitudeNull ⊢
  change (-line.b) ^ 2 + line.a ^ 2 = 0 at altitudeNull
  calc
    line.a ^ 2 + line.b ^ 2 = (-line.b) ^ 2 + line.a ^ 2 := by ring1
    _ = 0 := altitudeNull

/-- Reflecting successively in a central line and its perpendicular altitude
is rotation in their common point. -/
theorem reflectPoint_altitude_comp_eq_rotate
    (line : Line K) (lineNonNull : ¬ line.IsNull)
    (center : Point K) (centerContains : line.Contains center)
    (point : Point K) :
    reflectPoint (altitudeThrough center line)
        (altitudeThrough_nonNull_of_nonNull center line lineNonNull)
        (reflectPoint line lineNonNull point) =
      rotateInPoint center point := by
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ lineNonNull
  have altitudeNorm : lineNorm (altitudeThrough center line) = lineNorm line := by
    unfold lineNorm altitudeThrough
    ring1
  have constantFormula : line.c = -line.a * center.x - line.b * center.y := by
    unfold Line.Contains at centerContains
    calc
      line.c =
          (line.a * center.x + line.b * center.y + line.c) -
            line.a * center.x - line.b * center.y := by ring1
      _ = -line.a * center.x - line.b * center.y := by
        rw [centerContains]
        ring1
  rw [reflectPoint_formula, reflectPoint_formula]
  apply Point.ext
  · unfold reflectionFormula rotateInPoint
    rw [altitudeNorm]
    simp only [altitudeThrough]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [constantFormula]
    calc
      _ =
        (2 * center.x - point.x) *
          (lineNorm line * (lineNorm line)⁻¹) ^ 2 +
          2 * line.b *
            (line.b * center.x - line.a * center.y) *
            (lineNorm line)⁻¹ *
            (1 - lineNorm line * (lineNorm line)⁻¹) := by
              unfold lineNorm
              ring1
      _ = 2 * center.x - point.x := by rw [normCancel]; ring1
  · unfold reflectionFormula rotateInPoint
    rw [altitudeNorm]
    simp only [altitudeThrough]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [constantFormula]
    calc
      _ =
        (2 * center.y - point.y) *
          (lineNorm line * (lineNorm line)⁻¹) ^ 2 +
          2 * line.a *
            (line.a * center.y - line.b * center.x) *
            (lineNorm line)⁻¹ *
            (1 - lineNorm line * (lineNorm line)⁻¹) := by
              unfold lineNorm
              ring1
      _ = 2 * center.y - point.y := by rw [normCancel]; ring1

/-- Composition of reflections in any two perpendicular non-null lines
through a common point is rotation in that point. -/
theorem reflectPoint_perpendicular_comp_eq_rotate [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (perpendicular : first.Perpendicular second)
    (center : Point K) (firstContains : first.Contains center)
    (secondContains : second.Contains center) (point : Point K) :
    reflectPoint second secondNonNull
        (reflectPoint first firstNonNull point) =
      rotateInPoint center point := by
  have secondParallelAltitude :
      second.Parallel (altitudeThrough center first) := by
    unfold Line.Parallel altitudeThrough
    unfold Line.Perpendicular at perpendicular
    calc
      second.a * first.a - (-first.b) * second.b =
          first.a * second.a + first.b * second.b := by ring1
      _ = 0 := perpendicular
  have secondEquivalentAltitude :=
    line_equivalent_of_parallel_and_common_point second
      (altitudeThrough center first) center secondParallelAltitude
      secondContains (altitudeThrough_contains center first)
  calc
    reflectPoint second secondNonNull
        (reflectPoint first firstNonNull point) =
      reflectPoint (altitudeThrough center first)
        (altitudeThrough_nonNull_of_nonNull center first firstNonNull)
        (reflectPoint first firstNonNull point) :=
      reflectPoint_eq_of_equivalent second (altitudeThrough center first)
        secondNonNull
        (altitudeThrough_nonNull_of_nonNull center first firstNonNull)
        secondEquivalentAltitude (reflectPoint first firstNonNull point)
    _ = rotateInPoint center point :=
      reflectPoint_altitude_comp_eq_rotate first firstNonNull center
        firstContains point

/-- In characteristic different from two, rotation in a point fixes only
that point. -/
theorem rotateInPoint_fixed_iff_center
    (center point : Point K) (twoNonzero : (2 : K) ≠ 0) :
    rotateInPoint center point = point ↔ point = center := by
  constructor
  · intro fixed
    have xFixed := congrArg Point.x fixed
    have yFixed := congrArg Point.y fixed
    apply Point.ext
    · have twiceDifference :
          (2 : K) * (point.x - center.x) = 0 := by
        change 2 * center.x - point.x = point.x at xFixed
        calc
          (2 : K) * (point.x - center.x) =
              -(2 * center.x - point.x - point.x) := by ring1
          _ = 0 := by rw [xFixed]; ring1
      have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
        RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
      calc
        point.x = (point.x - center.x) + center.x := by ring1
        _ = (2 * (2 : K)⁻¹) * (point.x - center.x) + center.x := by
          rw [twoCancel]
          ring1
        _ = (2 : K)⁻¹ * (2 * (point.x - center.x)) + center.x := by ring1
        _ = center.x := by rw [twiceDifference]; ring1
    · have twiceDifference :
          (2 : K) * (point.y - center.y) = 0 := by
        change 2 * center.y - point.y = point.y at yFixed
        calc
          (2 : K) * (point.y - center.y) =
              -(2 * center.y - point.y - point.y) := by ring1
          _ = 0 := by rw [yFixed]; ring1
      have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
        RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
      calc
        point.y = (point.y - center.y) + center.y := by ring1
        _ = (2 * (2 : K)⁻¹) * (point.y - center.y) + center.y := by
          rw [twoCancel]
          ring1
        _ = (2 : K)⁻¹ * (2 * (point.y - center.y)) + center.y := by ring1
        _ = center.y := by rw [twiceDifference]; ring1
  · intro pointCenter
    rw [pointCenter]
    apply Point.ext <;>
      unfold rotateInPoint <;>
      ring1

/-- The finite data certifying that the source construction gives a regular
`order`-gon.  Its vertices are the executable points `A₀,A₂,...`; all other
regularity properties are consequences of the generic construction lemmas. -/
structure ConstructedRegularPolygon (K : Type*) [RFAP.ExplicitField K]
    [Nontrivial K] [DecidableEq K] (order : Nat) where
  star : FiniteRegularStar K order
  initialPoint : Point K
  initialContains : star.initial.previous.Contains initialPoint
  initialDistinct : initialPoint ≠ star.center
  pairwiseVertices :
    ∀ first second : Fin order, first ≠ second →
      regularPolygonVertexAt star initialPoint first.val ≠
        regularPolygonVertexAt star initialPoint second.val

namespace ConstructedRegularPolygon

variable [Nontrivial K] [DecidableEq K] {order : Nat}

/-- The vertex `A₂ₖ` of the finite polygon. -/
def vertex (polygon : ConstructedRegularPolygon K order)
    (index : Fin order) : Point K :=
  regularPolygonVertexAt polygon.star polygon.initialPoint index.val

theorem vertex_injective (polygon : ConstructedRegularPolygon K order) :
    Function.Injective polygon.vertex := by
  intro first second verticesEqual
  by_cases same : first = second
  · exact same
  · exact False.elim ((polygon.pairwiseVertices first second same)
      verticesEqual)

theorem vertex_on_radial_line (polygon : ConstructedRegularPolygon K order)
    (index : Fin order) :
    (reflectionLineAt polygon.star.initial (2 * index.val)).Contains
      (polygon.vertex index) :=
  regularPolygonVertexAt_on_radial_line polygon.star polygon.initialPoint
    polygon.initialContains index.val

theorem vertex_radius (polygon : ConstructedRegularPolygon K order)
    (index : Fin order) :
    quadrance polygon.star.center (polygon.vertex index) =
      quadrance polygon.star.center polygon.initialPoint :=
  regularPolygonVertexAt_radius polygon.star polygon.initialPoint index.val

theorem successive_step (polygon : ConstructedRegularPolygon K order)
    (index : Nat) :
    regularPolygonVertexAt polygon.star polygon.initialPoint (index + 1) =
      reflectionPointAt polygon.star.initial (2 * index + 1)
        (regularPolygonVertexAt polygon.star polygon.initialPoint index) :=
  regularPolygonVertexAt_succ polygon.star polygon.initialPoint
    polygon.initialContains index

theorem closes (polygon : ConstructedRegularPolygon K order) :
    regularPolygonVertexAt polygon.star polygon.initialPoint order =
      polygon.initialPoint :=
  regularPolygonVertexAt_closes polygon.star polygon.initialPoint
    polygon.initialContains

end ConstructedRegularPolygon

end DivineProportions
