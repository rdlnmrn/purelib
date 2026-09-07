import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Isometries.Decomposition

/-!
# Divine Proportions, Exercise 13.3: central reflection mirrors

Reflection in a non-null central line has the book's central-reflection
coordinates.  Conversely, a unit parameter pair constructively determines a
central non-null mirror, unique up to the project's quotient-free
`Line.Equivalent` relation.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_two_mul_eq_zero (value : K)
    (twoNonzero : (2 : K) ≠ 0) (twiceZero : (2 : K) * value = 0) :
    value = 0 := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    value = 1 * value := by ring1
    _ = (2 * (2 : K)⁻¹) * value := by rw [twoCancel]
    _ = (2 : K)⁻¹ * (2 * value) := by ring1
    _ = 0 := by rw [twiceZero]; ring1

/-- A point is fixed by reflection in a non-null line exactly when it lies on
the mirror. -/
theorem reflectPoint_fixed_iff_contains (line : Line K)
    (nonNull : ¬ line.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    reflectPoint line nonNull point = point ↔ line.Contains point := by
  constructor
  · intro fixed
    have xFixed := congrArg Point.x fixed
    have yFixed := congrArg Point.y fixed
    change
      2 * (altitudeFoot point line nonNull).x - point.x = point.x
      at xFixed
    change
      2 * (altitudeFoot point line nonNull).y - point.y = point.y
      at yFixed
    have twiceXZero :
        (2 : K) * ((altitudeFoot point line nonNull).x - point.x) = 0 := by
      calc
        (2 : K) * ((altitudeFoot point line nonNull).x - point.x) =
            (2 * (altitudeFoot point line nonNull).x - point.x) -
              point.x := by ring1
        _ = 0 := by rw [xFixed]; ring1
    have twiceYZero :
        (2 : K) * ((altitudeFoot point line nonNull).y - point.y) = 0 := by
      calc
        (2 : K) * ((altitudeFoot point line nonNull).y - point.y) =
            (2 * (altitudeFoot point line nonNull).y - point.y) -
              point.y := by ring1
        _ = 0 := by rw [yFixed]; ring1
    have footEqualsPoint : altitudeFoot point line nonNull = point := by
      apply Point.ext
      · have differenceZero := eq_zero_of_two_mul_eq_zero
          ((altitudeFoot point line nonNull).x - point.x)
          twoNonzero twiceXZero
        calc
          (altitudeFoot point line nonNull).x =
              ((altitudeFoot point line nonNull).x - point.x) + point.x := by
                ring1
          _ = point.x := by rw [differenceZero]; ring1
      · have differenceZero := eq_zero_of_two_mul_eq_zero
          ((altitudeFoot point line nonNull).y - point.y)
          twoNonzero twiceYZero
        calc
          (altitudeFoot point line nonNull).y =
              ((altitudeFoot point line nonNull).y - point.y) + point.y := by
                ring1
          _ = point.y := by rw [differenceZero]; ring1
    rw [← footEqualsPoint]
    exact altitudeFoot_on_line point line nonNull
  · intro contains
    have pointEqualsFoot := altitudeFoot_unique point line nonNull point
      contains (altitudeThrough_contains point line)
    unfold reflectPoint
    rw [← pointEqualsFoot]
    apply Point.ext <;>
      unfold rotateInPoint <;>
      ring1

/-- The first central-reflection parameter associated to a central line. -/
def centralLineReflectionQ (line : Line K) : K :=
  (line.b ^ 2 - line.a ^ 2) / lineNorm line

/-- The second central-reflection parameter associated to a central line. -/
def centralLineReflectionR (line : Line K) : K :=
  (-2 * line.a * line.b) / lineNorm line

/-- The two parameters extracted from a non-null central line form a unit
pair. -/
theorem centralLineReflection_unit (line : Line K)
    (nonNull : ¬ line.IsNull) :
    centralLineReflectionQ line ^ 2 + centralLineReflectionR line ^ 2 = 1 := by
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ nonNull
  unfold centralLineReflectionQ centralLineReflectionR
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((line.b ^ 2 - line.a ^ 2) * (lineNorm line)⁻¹) ^ 2 +
        ((-2 * line.a * line.b) * (lineNorm line)⁻¹) ^ 2 =
      (lineNorm line * (lineNorm line)⁻¹) ^ 2 := by
        unfold lineNorm
        ring1
    _ = 1 := by rw [normCancel]; ring1

/-- The forward half of Exercise 13.3: reflection in a non-null central line
is the central reflection with its displayed unit parameters. -/
theorem centralLine_reflection_is_central (line : Line K)
    (nonNull : ¬ line.IsNull) (central : line.Contains planeOrigin)
    (point : Point K) :
    reflectPoint line nonNull point =
      centralReflectionPoint
        (centralLineReflectionQ line) (centralLineReflectionR line) point := by
  have cZero : line.c = 0 := by
    unfold Line.Contains planeOrigin at central
    simpa using central
  rw [reflectPoint_formula]
  apply Point.ext <;>
    unfold reflectionFormula centralReflectionPoint centralLineReflectionQ
      centralLineReflectionR <;>
    rw [cZero] <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- A concrete central mirror for parameters `[q,r]`.  The generic branch is
`⟨q-1:r:0⟩`; the exceptional identity-on-x parameter `q=1` uses
`⟨0:1:0⟩`. -/
def centralReflectionMirror [Nontrivial K] [DecidableEq K]
    (q r : K) : Line K :=
  if qOne : q = 1 then
    { a := 0
      b := 1
      c := 0
      direction_nonzero := Or.inr one_ne_zero }
  else
    { a := q - 1
      b := r
      c := 0
      direction_nonzero := Or.inl (by
        intro differenceZero
        apply qOne
        calc
          q = (q - 1) + 1 := by ring1
          _ = 1 := by rw [differenceZero]; ring1) }

private theorem square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact False.elim (squareNonzero squareZero)

/-- The concrete mirror is non-null for a unit pair outside characteristic
two. -/
theorem centralReflectionMirror_nonNull [Nontrivial K] [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (centralReflectionMirror q r).IsNull := by
  by_cases qOne : q = 1
  · unfold centralReflectionMirror
    simp only [qOne, dite_true, Line.IsNull]
    intro nullNorm
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  · unfold centralReflectionMirror
    simp only [qOne, dite_false, Line.IsNull]
    have oneMinusQNonzero : (1 : K) - q ≠ 0 := by
      intro differenceZero
      apply qOne
      calc
        q = 1 - (1 - q) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have normFormula : (q - 1) ^ 2 + r ^ 2 = 2 * (1 - q) := by
      calc
        (q - 1) ^ 2 + r ^ 2 =
            (q ^ 2 + r ^ 2) + 2 * (1 - q) - 1 := by ring1
        _ = 2 * (1 - q) := by rw [unit]; ring1
    rw [normFormula]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero oneMinusQNonzero

/-- The concrete mirror realizes the given central reflection. -/
theorem centralReflectionMirror_reflects [Nontrivial K] [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) (point : Point K) :
    reflectPoint (centralReflectionMirror q r)
        (centralReflectionMirror_nonNull q r unit twoNonzero) point =
      centralReflectionPoint q r point := by
  by_cases qOne : q = 1
  · have rSquareZero : r ^ 2 = 0 := by
      calc
        r ^ 2 = q ^ 2 + r ^ 2 - 1 := by rw [qOne]; ring1
        _ = 0 := by rw [unit]; ring1
    have rZero := square_eq_zero r rSquareZero
    have oneInverse : (1 : K)⁻¹ = 1 := by
      calc
        (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel 1 one_ne_zero
    rw [reflectPoint_formula]
    apply Point.ext <;>
      simp only [centralReflectionMirror, qOne, dite_true, reflectionFormula,
        lineNorm, centralReflectionPoint,
        RFAP.ExplicitField.div_eq_mul_inv] <;>
      rw [rZero] <;>
      rw [show (0 : K) ^ 2 + 1 ^ 2 = 1 by ring1] <;>
      rw [oneInverse] <;>
      ring1
  · let norm : K := (q - 1) ^ 2 + r ^ 2
    have normFormula : norm = 2 * (1 - q) := by
      unfold norm
      calc
        (q - 1) ^ 2 + r ^ 2 =
            (q ^ 2 + r ^ 2) + 2 * (1 - q) - 1 := by ring1
        _ = 2 * (1 - q) := by rw [unit]; ring1
    have oneMinusQNonzero : (1 : K) - q ≠ 0 := by
      intro differenceZero
      apply qOne
      calc
        q = 1 - (1 - q) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have normNonzero : norm ≠ 0 := by
      rw [normFormula]
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero oneMinusQNonzero
    have normCancel : norm * norm⁻¹ = 1 :=
      RFAP.ExplicitField.mul_inv_cancel norm normNonzero
    have qNumerator : r ^ 2 - (q - 1) ^ 2 = q * norm := by
      unfold norm
      calc
        r ^ 2 - (q - 1) ^ 2 =
            q * ((q - 1) ^ 2 + r ^ 2) +
              (1 - q) * (q ^ 2 + r ^ 2 - 1) := by ring1
        _ = q * ((q - 1) ^ 2 + r ^ 2) := by rw [unit]; ring1
    have rNumerator : -2 * (q - 1) * r = r * norm := by
      unfold norm
      calc
        -2 * (q - 1) * r =
            r * ((q - 1) ^ 2 + r ^ 2) -
              r * (q ^ 2 + r ^ 2 - 1) := by ring1
        _ = r * ((q - 1) ^ 2 + r ^ 2) := by rw [unit]; ring1
    have positiveRNumerator : 2 * (q - 1) * r = -(r * norm) := by
      calc
        2 * (q - 1) * r = -(-2 * (q - 1) * r) := by ring1
        _ = -(r * norm) := by rw [rNumerator]
    have negQNumerator : (q - 1) ^ 2 - r ^ 2 = -q * norm := by
      calc
        (q - 1) ^ 2 - r ^ 2 = -(r ^ 2 - (q - 1) ^ 2) := by ring1
        _ = -q * norm := by rw [qNumerator]; ring1
    rw [reflectPoint_formula]
    apply Point.ext
    · simp only [centralReflectionMirror, qOne, dite_false,
        reflectionFormula, lineNorm, centralReflectionPoint,
        RFAP.ExplicitField.div_eq_mul_inv, mul_zero, sub_zero]
      change
        ((r ^ 2 - (q - 1) ^ 2) * point.x -
            2 * (q - 1) * r * point.y) * norm⁻¹ =
          q * point.x + r * point.y
      rw [qNumerator, positiveRNumerator]
      calc
        (q * norm * point.x - -(r * norm) * point.y) * norm⁻¹ =
            (q * point.x + r * point.y) * (norm * norm⁻¹) := by ring1
        _ = q * point.x + r * point.y := by rw [normCancel]; ring1
    · simp only [centralReflectionMirror, qOne, dite_false,
        reflectionFormula, lineNorm, centralReflectionPoint,
        RFAP.ExplicitField.div_eq_mul_inv, mul_zero, sub_zero]
      change
        (-2 * (q - 1) * r * point.x +
            ((q - 1) ^ 2 - r ^ 2) * point.y) * norm⁻¹ =
          r * point.x - q * point.y
      rw [rNumerator, negQNumerator]
      calc
        (r * norm * point.x + (-q * norm) * point.y) * norm⁻¹ =
            (r * point.x - q * point.y) * (norm * norm⁻¹) := by ring1
        _ = r * point.x - q * point.y := by rw [normCancel]; ring1

/-- A direction point on a central line. -/
def centralLineDirectionPoint (line : Line K) : Point K :=
  ⟨line.b, -line.a⟩

/-- Two non-null central lines inducing the same point reflection are the same
ordered proportion. -/
theorem centralLine_reflection_unique [Nontrivial K]
    (first second : Line K) (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (firstCentral : first.Contains planeOrigin)
    (secondCentral : second.Contains planeOrigin)
    (sameReflection : ∀ point : Point K,
      reflectPoint first firstNonNull point =
        reflectPoint second secondNonNull point) :
    first.Equivalent second := by
  have firstDirectionContains :
      first.Contains (centralLineDirectionPoint first) := by
    have firstCZero : first.c = 0 := by
      unfold Line.Contains planeOrigin at firstCentral
      simpa using firstCentral
    unfold Line.Contains centralLineDirectionPoint
    rw [firstCZero]
    ring1
  have firstDirectionFixed :
      reflectPoint first firstNonNull (centralLineDirectionPoint first) =
        centralLineDirectionPoint first :=
    (reflectPoint_fixed_iff_contains first firstNonNull twoNonzero
      (centralLineDirectionPoint first)).2 firstDirectionContains
  have secondDirectionFixed :
      reflectPoint second secondNonNull (centralLineDirectionPoint first) =
        centralLineDirectionPoint first := by
    rw [← sameReflection]
    exact firstDirectionFixed
  have secondDirectionContains :
      second.Contains (centralLineDirectionPoint first) :=
    (reflectPoint_fixed_iff_contains second secondNonNull twoNonzero
      (centralLineDirectionPoint first)).1 secondDirectionFixed
  have parallel : first.Parallel second := by
    have secondCZero : second.c = 0 := by
      unfold Line.Contains planeOrigin at secondCentral
      simpa using secondCentral
    unfold Line.Contains centralLineDirectionPoint at secondDirectionContains
    unfold Line.Parallel
    rw [secondCZero] at secondDirectionContains
    calc
      first.a * second.b - second.a * first.b =
          -(second.a * first.b + second.b * (-first.a) + 0) := by ring1
      _ = 0 := by rw [secondDirectionContains]; ring1
  exact line_equivalent_of_parallel_and_common_point
    first second planeOrigin parallel firstCentral secondCentral

/-- Exercise 13.3, converse and uniqueness: every unit central reflection has
a displayed non-null central mirror, and any other such mirror is equivalent
to it. -/
theorem centralReflection_has_unique_mirror [Nontrivial K] [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ∃ mirror : Line K, ∃ mirrorNonNull : ¬ mirror.IsNull,
      mirror.Contains planeOrigin ∧
      (∀ point : Point K,
        reflectPoint mirror mirrorNonNull point =
          centralReflectionPoint q r point) ∧
      ∀ other : Line K, ∀ otherNonNull : ¬ other.IsNull,
        other.Contains planeOrigin →
        (∀ point : Point K,
          reflectPoint other otherNonNull point =
            centralReflectionPoint q r point) →
        other.Equivalent mirror := by
  let mirror := centralReflectionMirror q r
  let mirrorNonNull := centralReflectionMirror_nonNull q r unit twoNonzero
  refine ⟨mirror, mirrorNonNull, ?_, ?_, ?_⟩
  · unfold mirror centralReflectionMirror Line.Contains planeOrigin
    split <;> ring1
  · exact centralReflectionMirror_reflects q r unit twoNonzero
  · intro other otherNonNull otherCentral otherReflection
    apply centralLine_reflection_unique other mirror
      otherNonNull mirrorNonNull twoNonzero otherCentral
    · unfold mirror centralReflectionMirror Line.Contains planeOrigin
      split <;> ring1
    · intro point
      calc
        reflectPoint other otherNonNull point =
            centralReflectionPoint q r point := otherReflection point
        _ = reflectPoint mirror mirrorNonNull point :=
          (centralReflectionMirror_reflects q r unit twoNonzero point).symm

end DivineProportions
