import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.Boxes
import RFAP.Polynomial.Path
import RFAP.Sturm

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace RFAP.Winding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial

/-- A finite polynomial edge together with its oriented parameter interval. -/
structure PolynomialEdge where
  realPart : CoordinatePolynomial
  imagPart : CoordinatePolynomial
  start : Coordinate
  stop : Coordinate
deriving DecidableEq

/-- Twice the Cauchy index carried by one oriented polynomial edge. -/
def PolynomialEdge.doubledWinding (edge : PolynomialEdge) : Int :=
  RFAP.Sturm.cauchyIndex2 edge.realPart edge.imagPart
    edge.start edge.stop

/-- The two displayed coordinates of an edge have no common rational
parameter zero. -/
def PolynomialEdge.Coprime (edge : PolynomialEdge) : Prop :=
  RFAP.Sturm.NoCommonZero edge.realPart edge.imagPart

/-- Reverse an edge by reversing its finite parameter interval. -/
def PolynomialEdge.reverse (edge : PolynomialEdge) : PolynomialEdge :=
  { edge with start := edge.stop, stop := edge.start }

/-- Restrict an edge to a new oriented parameter interval. -/
def PolynomialEdge.restrict (edge : PolynomialEdge)
    (start stop : Coordinate) : PolynomialEdge :=
  { edge with start, stop }

@[simp] theorem PolynomialEdge.doubledWinding_reverse
    (edge : PolynomialEdge) :
    edge.reverse.doubledWinding = -edge.doubledWinding := by
  exact RFAP.Sturm.cauchyIndex2_reverse edge.realPart edge.imagPart
    edge.start edge.stop

theorem PolynomialEdge.doubledWinding_restrict_add
    (edge : PolynomialEdge) (a b c : Coordinate) :
    (edge.restrict a b).doubledWinding +
        (edge.restrict b c).doubledWinding =
      (edge.restrict a c).doubledWinding := by
  exact (RFAP.Sturm.cauchyIndex2_add
    edge.realPart edge.imagPart a b c).symm

/-- A coprime edge has the parity of the difference of its imaginary-coordinate
endpoint-zero flags. -/
theorem PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    (edge : PolynomialEdge) (coprime : edge.Coprime) :
    Even (edge.doubledWinding -
      ((if edge.imagPart.eval edge.start = 0 then 1 else 0) -
        (if edge.imagPart.eval edge.stop = 0 then 1 else 0))) := by
  exact RFAP.Sturm.cauchyIndex2_sub_secondZeroFlags_even
    coprime edge.start edge.stop

/-- The edge obtained by evaluating `p` on `origin + t * direction`. -/
def PolynomialEdge.ofLine (p : GaussianPolynomial)
    (origin direction : Gaussian) (start stop : Coordinate) : PolynomialEdge where
  realPart := pathReal p origin direction
  imagPart := pathImag p origin direction
  start := start
  stop := stop

@[simp] theorem PolynomialEdge.ofLine_normalize
    (p : GaussianPolynomial) (origin direction : Gaussian)
    (start stop : Coordinate) :
    PolynomialEdge.ofLine p.normalize origin direction start stop =
      PolynomialEdge.ofLine p origin direction start stop := by
  unfold PolynomialEdge.ofLine
  rw [pathReal_normalize, pathImag_normalize]

/-- Pointwise nonvanishing of an affine polynomial path gives the displayed
coordinate coprimality used by the constructive Sturm chain. -/
theorem PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    (p : GaussianPolynomial) (origin direction : Gaussian)
    (start stop : Coordinate)
    (nonzero : ∀ t : Coordinate, p.eval (line origin direction t) ≠ 0) :
    (PolynomialEdge.ofLine p origin direction start stop).Coprime := by
  intro t
  by_cases realZero :
      (PolynomialEdge.ofLine p origin direction start stop).realPart.eval t = 0
  · right
    intro imaginaryZero
    apply nonzero t
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · rw [← eval_pathReal]
      exact realZero
    · rw [← eval_pathImag]
      exact imaginaryZero
  · exact Or.inl realZero

/-- Conversely, displayed coordinate coprimality certifies pointwise
nonvanishing of the represented affine Gaussian path. -/
theorem PolynomialEdge.eval_ne_zero_of_ofLine_coprime
    (p : GaussianPolynomial) (origin direction : Gaussian)
    (start stop t : Coordinate)
    (coprime : (PolynomialEdge.ofLine p origin direction start stop).Coprime) :
    p.eval (line origin direction t) ≠ 0 := by
  intro zero
  rcases coprime t with realNonzero | imaginaryNonzero
  · apply realNonzero
    change (pathReal p origin direction).eval t = 0
    rw [eval_pathReal]
    exact congrArg (fun z : Gaussian => z.re) zero
  · apply imaginaryNonzero
    change (pathImag p origin direction).eval t = 0
    rw [eval_pathImag]
    exact congrArg (fun z : Gaussian => z.im) zero

@[simp] theorem PolynomialEdge.ofLine_real_eval (p : GaussianPolynomial)
    (origin direction : Gaussian) (start stop t : Coordinate) :
    (PolynomialEdge.ofLine p origin direction start stop).realPart.eval t =
      (p.eval (line origin direction t)).re := by
  exact eval_pathReal p origin direction t

@[simp] theorem PolynomialEdge.ofLine_imag_eval (p : GaussianPolynomial)
    (origin direction : Gaussian) (start stop t : Coordinate) :
    (PolynomialEdge.ofLine p origin direction start stop).imagPart.eval t =
      (p.eval (line origin direction t)).im := by
  exact eval_pathImag p origin direction t

def horizontalBase (y : Coordinate) : Gaussian := ⟨0, y⟩
def horizontalDirection : Gaussian := ⟨1, 0⟩
def verticalBase (x : Coordinate) : Gaussian := ⟨x, 0⟩
def verticalDirection : Gaussian := ⟨0, 1⟩
def point (x y : Coordinate) : Gaussian := ⟨x, y⟩

@[simp] theorem line_horizontal (y t : Coordinate) :
    line (horizontalBase y) horizontalDirection t = point t y := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [line, horizontalBase, horizontalDirection, point, add_re,
      add_im, mul_re, mul_im, ofCoordinate_re, ofCoordinate_im] <;>
    ring1

@[simp] theorem line_vertical (x t : Coordinate) :
    line (verticalBase x) verticalDirection t = point x t := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [line, verticalBase, verticalDirection, point, add_re,
      add_im, mul_re, mul_im, ofCoordinate_re, ofCoordinate_im] <;>
    ring1

/-- The oriented horizontal edge `t + iy`, for `a` to `b`. -/
def horizontalEdge (p : GaussianPolynomial) (y a b : Coordinate) :
    PolynomialEdge :=
  PolynomialEdge.ofLine p (horizontalBase y) horizontalDirection a b

/-- The oriented vertical edge `x + it`, for `a` to `b`. -/
def verticalEdge (p : GaussianPolynomial) (x a b : Coordinate) :
    PolynomialEdge :=
  PolynomialEdge.ofLine p (verticalBase x) verticalDirection a b

@[simp] theorem horizontalEdge_normalize (p : GaussianPolynomial)
    (y a b : Coordinate) :
    horizontalEdge p.normalize y a b = horizontalEdge p y a b := by
  unfold horizontalEdge
  exact PolynomialEdge.ofLine_normalize p _ _ _ _

@[simp] theorem verticalEdge_normalize (p : GaussianPolynomial)
    (x a b : Coordinate) :
    verticalEdge p.normalize x a b = verticalEdge p x a b := by
  unfold verticalEdge
  exact PolynomialEdge.ofLine_normalize p _ _ _ _

@[simp] theorem horizontalEdge_real_eval (p : GaussianPolynomial)
    (y a b t : Coordinate) :
    (horizontalEdge p y a b).realPart.eval t = (p.eval (point t y)).re := by
  simpa only [horizontalEdge, line_horizontal] using
    PolynomialEdge.ofLine_real_eval p (horizontalBase y)
      horizontalDirection a b t

@[simp] theorem horizontalEdge_imag_eval (p : GaussianPolynomial)
    (y a b t : Coordinate) :
    (horizontalEdge p y a b).imagPart.eval t = (p.eval (point t y)).im := by
  simpa only [horizontalEdge, line_horizontal] using
    PolynomialEdge.ofLine_imag_eval p (horizontalBase y)
      horizontalDirection a b t

@[simp] theorem verticalEdge_real_eval (p : GaussianPolynomial)
    (x a b t : Coordinate) :
    (verticalEdge p x a b).realPart.eval t = (p.eval (point x t)).re := by
  simpa only [verticalEdge, line_vertical] using
    PolynomialEdge.ofLine_real_eval p (verticalBase x) verticalDirection a b t

@[simp] theorem verticalEdge_imag_eval (p : GaussianPolynomial)
    (x a b t : Coordinate) :
    (verticalEdge p x a b).imagPart.eval t = (p.eval (point x t)).im := by
  simpa only [verticalEdge, line_vertical] using
    PolynomialEdge.ofLine_imag_eval p (verticalBase x) verticalDirection a b t

/-- Positively oriented four-edge boundary of a constructive box. -/
def boxBoundary (p : GaussianPolynomial) (box : Box) : List PolynomialEdge :=
  [horizontalEdge p box.yLower box.xLower box.xUpper,
    verticalEdge p box.xUpper box.yLower box.yUpper,
    horizontalEdge p box.yUpper box.xUpper box.xLower,
    verticalEdge p box.xLower box.yUpper box.yLower]

/-- Proof-relevant coprimality of all four oriented boundary coordinate
pairs.  Constructive path-clearance certificates supply these fields. -/
structure BoundaryCoprime (p : GaussianPolynomial) (box : Box) : Prop where
  bottom : (horizontalEdge p box.yLower box.xLower box.xUpper).Coprime
  right : (verticalEdge p box.xUpper box.yLower box.yUpper).Coprime
  top : (horizontalEdge p box.yUpper box.xUpper box.xLower).Coprime
  left : (verticalEdge p box.xLower box.yUpper box.yLower).Coprime

/-- Boundary coprimality is preserved by exact finite polynomial
multiplication. -/
theorem BoundaryCoprime.mul {p q : GaussianPolynomial} {box : Box}
    (pCoprime : BoundaryCoprime p box)
    (qCoprime : BoundaryCoprime q box) :
    BoundaryCoprime (p * q) box := by
  constructor
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [eval_mul]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (horizontalBase box.yLower) horizontalDirection
        box.xLower box.xUpper t pCoprime.bottom)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (horizontalBase box.yLower) horizontalDirection
        box.xLower box.xUpper t qCoprime.bottom)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [eval_mul]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (verticalBase box.xUpper) verticalDirection
        box.yLower box.yUpper t pCoprime.right)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (verticalBase box.xUpper) verticalDirection
        box.yLower box.yUpper t qCoprime.right)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [eval_mul]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (horizontalBase box.yUpper) horizontalDirection
        box.xUpper box.xLower t pCoprime.top)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (horizontalBase box.yUpper) horizontalDirection
        box.xUpper box.xLower t qCoprime.top)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [eval_mul]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (verticalBase box.xLower) verticalDirection
        box.yUpper box.yLower t pCoprime.left)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (verticalBase box.xLower) verticalDirection
        box.yUpper box.yLower t qCoprime.left)

/-- Sum of the four doubled edge indices. -/
def quadrupledBoxWinding (p : GaussianPolynomial) (box : Box) : Int :=
  ((boxBoundary p box).map PolynomialEdge.doubledWinding).sum

/-- Closed-box winding ignores the finite prefix of representation zeros
removed by dense normalization. -/
@[simp] theorem quadrupledBoxWinding_normalize
    (p : GaussianPolynomial) (box : Box) :
    quadrupledBoxWinding p.normalize box = quadrupledBoxWinding p box := by
  unfold quadrupledBoxWinding boxBoundary
  simp only [horizontalEdge_normalize, verticalEdge_normalize]

theorem quadrupledBoxWinding_eq (p : GaussianPolynomial) (box : Box) :
    quadrupledBoxWinding p box =
      (horizontalEdge p box.yLower box.xLower box.xUpper).doubledWinding +
      (verticalEdge p box.xUpper box.yLower box.yUpper).doubledWinding +
      (horizontalEdge p box.yUpper box.xUpper box.xLower).doubledWinding +
      (verticalEdge p box.xLower box.yUpper box.yLower).doubledWinding := by
  simp only [quadrupledBoxWinding, boxBoundary, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring1

/-- A closed coprime polynomial boundary has even raw winding.  The four
edge parities telescope through their shared real-coordinate vertex flags. -/
theorem quadrupledBoxWinding_even_of_boundaryCoprime
    (p : GaussianPolynomial) (box : Box)
    (coprime : BoundaryCoprime p box) :
    Even (quadrupledBoxWinding p box) := by
  have bottom := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.bottom
  have right := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.right
  have top := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.top
  have left := PolynomialEdge.doubledWinding_sub_imagZeroFlags_even
    _ coprime.left
  simp only [horizontalEdge_imag_eval] at bottom top
  simp only [verticalEdge_imag_eval] at right left
  let lowerLeftFlag : Int :=
    if (p.eval (point box.xLower box.yLower)).im = 0 then 1 else 0
  let lowerRightFlag : Int :=
    if (p.eval (point box.xUpper box.yLower)).im = 0 then 1 else 0
  let upperRightFlag : Int :=
    if (p.eval (point box.xUpper box.yUpper)).im = 0 then 1 else 0
  let upperLeftFlag : Int :=
    if (p.eval (point box.xLower box.yUpper)).im = 0 then 1 else 0
  change Even ((horizontalEdge p box.yLower box.xLower
      box.xUpper).doubledWinding -
    (lowerLeftFlag - lowerRightFlag)) at bottom
  change Even ((verticalEdge p box.xUpper box.yLower
      box.yUpper).doubledWinding -
    (lowerRightFlag - upperRightFlag)) at right
  change Even ((horizontalEdge p box.yUpper box.xUpper
      box.xLower).doubledWinding -
    (upperRightFlag - upperLeftFlag)) at top
  change Even ((verticalEdge p box.xLower box.yUpper
      box.yLower).doubledWinding -
    (upperLeftFlag - lowerLeftFlag)) at left
  rcases (((bottom.add right).add top).add left) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [quadrupledBoxWinding_eq]
  calc
    (horizontalEdge p box.yLower box.xLower
          box.xUpper).doubledWinding +
        (verticalEdge p box.xUpper box.yLower
          box.yUpper).doubledWinding +
        (horizontalEdge p box.yUpper box.xUpper
          box.xLower).doubledWinding +
        (verticalEdge p box.xLower box.yUpper
          box.yLower).doubledWinding =
      (((horizontalEdge p box.yLower box.xLower
            box.xUpper).doubledWinding -
          (lowerLeftFlag - lowerRightFlag)) +
        ((verticalEdge p box.xUpper box.yLower
            box.yUpper).doubledWinding -
          (lowerRightFlag - upperRightFlag)) +
        ((horizontalEdge p box.yUpper box.xUpper
            box.xLower).doubledWinding -
          (upperRightFlag - upperLeftFlag))) +
        ((verticalEdge p box.xLower box.yUpper
            box.yLower).doubledWinding -
          (upperLeftFlag - lowerLeftFlag)) := by
        ring1
    _ = k + k := hk

/-- The doubled-winding normalization used before boundary parity is known. -/
def doubledBoxWinding (p : GaussianPolynomial) (box : Box) : Int :=
  quadrupledBoxWinding p box / 2

/-- Ordinary winding, used after divisibility by four has been certified. -/
def boxWinding (p : GaussianPolynomial) (box : Box) : Int :=
  quadrupledBoxWinding p box / 4

private theorem horizontal_add (p : GaussianPolynomial)
    (y a b c : Coordinate) :
    (horizontalEdge p y a b).doubledWinding +
        (horizontalEdge p y b c).doubledWinding =
      (horizontalEdge p y a c).doubledWinding :=
  PolynomialEdge.doubledWinding_restrict_add
    (horizontalEdge p y a c) a b c

private theorem vertical_add (p : GaussianPolynomial)
    (x a b c : Coordinate) :
    (verticalEdge p x a b).doubledWinding +
        (verticalEdge p x b c).doubledWinding =
      (verticalEdge p x a c).doubledWinding :=
  PolynomialEdge.doubledWinding_restrict_add
    (verticalEdge p x a c) a b c

private theorem horizontal_reverse (p : GaussianPolynomial)
    (y a b : Coordinate) :
    (horizontalEdge p y b a).doubledWinding =
      -(horizontalEdge p y a b).doubledWinding :=
  PolynomialEdge.doubledWinding_reverse (horizontalEdge p y a b)

private theorem vertical_reverse (p : GaussianPolynomial)
    (x a b : Coordinate) :
    (verticalEdge p x b a).doubledWinding =
      -(verticalEdge p x a b).doubledWinding :=
  PolynomialEdge.doubledWinding_reverse (verticalEdge p x a b)

/-- Exact cancellation of the internal edge in a vertical subdivision. -/
theorem quadrupledBoxWinding_vertical_split (p : GaussianPolynomial) (box : Box)
    (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper) :
    quadrupledBoxWinding p box =
      quadrupledBoxWinding p (box.verticalLeft cut inside) +
        quadrupledBoxWinding p (box.verticalRight cut inside) := by
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  dsimp only [RFAP.Boxes.Box.verticalLeft,
    RFAP.Boxes.Box.verticalRight]
  have bottom := horizontal_add p box.yLower box.xLower cut box.xUpper
  have top := horizontal_add p box.yUpper box.xUpper cut box.xLower
  have internal := vertical_reverse p cut box.yLower box.yUpper
  rw [← bottom, ← top, internal]
  ring1

/-- Exact cancellation of the internal edge in a horizontal subdivision. -/
theorem quadrupledBoxWinding_horizontal_split (p : GaussianPolynomial)
    (box : Box) (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper) :
    quadrupledBoxWinding p box =
      quadrupledBoxWinding p (box.horizontalLower cut inside) +
        quadrupledBoxWinding p (box.horizontalUpper cut inside) := by
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq,
    quadrupledBoxWinding_eq]
  dsimp only [RFAP.Boxes.Box.horizontalLower,
    RFAP.Boxes.Box.horizontalUpper]
  have right := vertical_add p box.xUpper box.yLower cut box.yUpper
  have left := vertical_add p box.xLower box.yUpper cut box.yLower
  have internal := horizontal_reverse p cut box.xLower box.xUpper
  rw [← right, ← left, internal]
  ring1

/-- One vertical and one horizontal cut give exact four-child additivity. -/
theorem quadrupledBoxWinding_four_split (p : GaussianPolynomial) (box : Box)
    (xCut yCut : Coordinate)
    (xInside : box.xLower ≤ xCut ∧ xCut ≤ box.xUpper)
    (yInside : box.yLower ≤ yCut ∧ yCut ≤ box.yUpper) :
    let left := box.verticalLeft xCut xInside
    let right := box.verticalRight xCut xInside
    let yInsideLeft : left.yLower ≤ yCut ∧ yCut ≤ left.yUpper := yInside
    let yInsideRight : right.yLower ≤ yCut ∧ yCut ≤ right.yUpper := yInside
    quadrupledBoxWinding p box =
      quadrupledBoxWinding p (left.horizontalLower yCut yInsideLeft) +
      quadrupledBoxWinding p (left.horizontalUpper yCut yInsideLeft) +
      quadrupledBoxWinding p (right.horizontalLower yCut yInsideRight) +
      quadrupledBoxWinding p (right.horizontalUpper yCut yInsideRight) := by
  dsimp only
  rw [quadrupledBoxWinding_vertical_split p box xCut xInside,
    quadrupledBoxWinding_horizontal_split p
      (box.verticalLeft xCut xInside) yCut yInside,
    quadrupledBoxWinding_horizontal_split p
      (box.verticalRight xCut xInside) yCut yInside]
  ring1

/-! ## Normalized subdivision -/

theorem doubledBoxWinding_vertical_split (p : GaussianPolynomial) (box : Box)
    (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (leftEven : Even (quadrupledBoxWinding p (box.verticalLeft cut inside)))
    (rightEven : Even (quadrupledBoxWinding p (box.verticalRight cut inside))) :
    doubledBoxWinding p box =
      doubledBoxWinding p (box.verticalLeft cut inside) +
        doubledBoxWinding p (box.verticalRight cut inside) := by
  rcases leftEven with ⟨left, leftEven⟩
  rcases rightEven with ⟨right, rightEven⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_vertical_split p box cut inside,
    leftEven, rightEven]
  omega

theorem doubledBoxWinding_horizontal_split (p : GaussianPolynomial)
    (box : Box) (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (lowerEven : Even
      (quadrupledBoxWinding p (box.horizontalLower cut inside)))
    (upperEven : Even
      (quadrupledBoxWinding p (box.horizontalUpper cut inside))) :
    doubledBoxWinding p box =
      doubledBoxWinding p (box.horizontalLower cut inside) +
        doubledBoxWinding p (box.horizontalUpper cut inside) := by
  rcases lowerEven with ⟨lower, lowerEven⟩
  rcases upperEven with ⟨upper, upperEven⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_horizontal_split p box cut inside,
    lowerEven, upperEven]
  omega

theorem boxWinding_vertical_split (p : GaussianPolynomial) (box : Box)
    (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (leftDivisible : (4 : Int) ∣
      quadrupledBoxWinding p (box.verticalLeft cut inside))
    (rightDivisible : (4 : Int) ∣
      quadrupledBoxWinding p (box.verticalRight cut inside)) :
    boxWinding p box =
      boxWinding p (box.verticalLeft cut inside) +
        boxWinding p (box.verticalRight cut inside) := by
  rcases leftDivisible with ⟨left, leftDivisible⟩
  rcases rightDivisible with ⟨right, rightDivisible⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_vertical_split p box cut inside,
    leftDivisible, rightDivisible]
  omega

theorem boxWinding_horizontal_split (p : GaussianPolynomial) (box : Box)
    (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (lowerDivisible : (4 : Int) ∣
      quadrupledBoxWinding p (box.horizontalLower cut inside))
    (upperDivisible : (4 : Int) ∣
      quadrupledBoxWinding p (box.horizontalUpper cut inside)) :
    boxWinding p box =
      boxWinding p (box.horizontalLower cut inside) +
        boxWinding p (box.horizontalUpper cut inside) := by
  rcases lowerDivisible with ⟨lower, lowerDivisible⟩
  rcases upperDivisible with ⟨upper, upperDivisible⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_horizontal_split p box cut inside,
    lowerDivisible, upperDivisible]
  omega

end RFAP.Winding
