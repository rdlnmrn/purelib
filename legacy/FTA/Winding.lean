import FTA.PathPolynomial
import FTA.Sturm
import FTA.BoxGeometry

/-!
# Executable doubled winding on rational polynomial edges

Definition 4.1 is implemented by composing a dense Gaussian-rational
polynomial with horizontal or vertical affine paths, extracting rational
coordinate polynomials, and invoking the finite Cauchy--Sturm program.  The
reversal and rectangular subdivision identities of Lemma 4.2 are exact integer
identities; internal edges cancel without topology, integration, or limits.
-/

namespace FTA.Winding

open CCL
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Sturm

/-- A rational polynomial edge with an oriented parameter interval. -/
structure PolynomialEdge where
  realPart : Sturm.RatPolynomial
  imagPart : Sturm.RatPolynomial
  start : ℚ
  stop : ℚ
deriving DecidableEq, Repr

/-- Definition 4.1's doubled edge winding. -/
def PolynomialEdge.doubledWinding (e : PolynomialEdge) : ℤ :=
  cauchyIndex2 e.realPart e.imagPart e.start e.stop

/-- Reverse an edge by reversing only its oriented parameter interval. -/
def PolynomialEdge.reverse (e : PolynomialEdge) : PolynomialEdge :=
  { e with start := e.stop, stop := e.start }

/-- Restrict the same rational path polynomials to a new oriented interval. -/
def PolynomialEdge.restrict (e : PolynomialEdge) (a b : ℚ) : PolynomialEdge :=
  { e with start := a, stop := b }

/-- Coordinate polynomial for the pointwise product of two paths.  The first
edge supplies the common oriented parameter interval. -/
def PolynomialEdge.product (e f : PolynomialEdge) : PolynomialEdge where
  realPart := productReal e.realPart e.imagPart f.realPart f.imagPart
  imagPart := productImag e.realPart e.imagPart f.realPart f.imagPart
  start := e.start
  stop := e.stop

@[simp] theorem PolynomialEdge.product_real_eval (e f : PolynomialEdge) (t : ℚ) :
    (e.product f).realPart.eval t =
      e.realPart.eval t * f.realPart.eval t -
        e.imagPart.eval t * f.imagPart.eval t := by
  simp [PolynomialEdge.product]

@[simp] theorem PolynomialEdge.product_imag_eval (e f : PolynomialEdge) (t : ℚ) :
    (e.product f).imagPart.eval t =
      e.realPart.eval t * f.imagPart.eval t +
        e.imagPart.eval t * f.realPart.eval t := by
  simp [PolynomialEdge.product]

@[simp] theorem PolynomialEdge.doubledWinding_reverse (e : PolynomialEdge) :
    e.reverse.doubledWinding = -e.doubledWinding := by
  exact cauchyIndex2_reverse e.realPart e.imagPart e.start e.stop

theorem PolynomialEdge.doubledWinding_restrict_add (e : PolynomialEdge) (a b c : ℚ) :
    (e.restrict a b).doubledWinding + (e.restrict b c).doubledWinding =
      (e.restrict a c).doubledWinding := by
  exact cauchyIndex2_add e.realPart e.imagPart a b c

/-- Polynomial edge obtained by evaluating `p` along `u + t d`. -/
def PolynomialEdge.ofLine (p : GaussianPolynomial) (u d : QI) (a b : ℚ) :
    PolynomialEdge where
  realPart := (pathReal p u d).normalize
  imagPart := (pathImag p u d).normalize
  start := a
  stop := b

theorem PolynomialEdge.ofLine_real_eval (p : GaussianPolynomial) (u d : QI)
    (a b t : ℚ) :
    ((PolynomialEdge.ofLine p u d a b).realPart).eval t =
      (p.eval (line u d t)).re :=
  by
    rw [PolynomialEdge.ofLine, eval_normalize, eval_pathReal]

theorem PolynomialEdge.ofLine_imag_eval (p : GaussianPolynomial) (u d : QI)
    (a b t : ℚ) :
    ((PolynomialEdge.ofLine p u d a b).imagPart).eval t =
      (p.eval (line u d t)).im :=
  by
    rw [PolynomialEdge.ofLine, eval_normalize, eval_pathImag]

theorem PolynomialEdge.ofLine_mul_real_toPolynomial
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (p * q) u d a b).realPart.toPolynomial =
      ((PolynomialEdge.ofLine p u d a b).product
        (PolynomialEdge.ofLine q u d a b)).realPart.toPolynomial :=
  by
    dsimp only [PolynomialEdge.ofLine, PolynomialEdge.product]
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial, eval_normalize,
      eval_productReal, eval_normalize, eval_normalize,
      eval_normalize, eval_normalize]
    simpa only [eval_productReal] using
      eval_pathReal_mul p q u d ((i : ℕ) : ℚ)

theorem PolynomialEdge.ofLine_mul_imag_toPolynomial
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (p * q) u d a b).imagPart.toPolynomial =
      ((PolynomialEdge.ofLine p u d a b).product
        (PolynomialEdge.ofLine q u d a b)).imagPart.toPolynomial :=
  by
    dsimp only [PolynomialEdge.ofLine, PolynomialEdge.product]
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    rw [eval_toPolynomial, eval_toPolynomial, eval_normalize,
      eval_productImag, eval_normalize, eval_normalize,
      eval_normalize, eval_normalize]
    simpa only [eval_productImag] using
      eval_pathImag_mul p q u d ((i : ℕ) : ℚ)

/-- Canonical edge construction upgrades the sparse real-coordinate product
identity to exact equality of executable dense polynomials. -/
theorem PolynomialEdge.ofLine_mul_real_eq
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (p * q) u d a b).realPart =
      ((PolynomialEdge.ofLine p u d a b).product
        (PolynomialEdge.ofLine q u d a b)).realPart := by
  have h := normalize_eq_normalize_of_toPolynomial_eq
    (PolynomialEdge.ofLine_mul_real_toPolynomial p q u d a b)
  simpa [PolynomialEdge.ofLine, PolynomialEdge.product,
    productReal] using h

/-- Canonical edge construction likewise gives exact dense equality of the
imaginary product coordinate. -/
theorem PolynomialEdge.ofLine_mul_imag_eq
    (p q : GaussianPolynomial) (u d : QI) (a b : ℚ) :
    (PolynomialEdge.ofLine (p * q) u d a b).imagPart =
      ((PolynomialEdge.ofLine p u d a b).product
        (PolynomialEdge.ofLine q u d a b)).imagPart := by
  have h := normalize_eq_normalize_of_toPolynomial_eq
    (PolynomialEdge.ofLine_mul_imag_toPolynomial p q u d a b)
  simpa [PolynomialEdge.ofLine, PolynomialEdge.product,
    productImag] using h

def horizontalBase (y : ℚ) : QI where
  re := 0
  im := y

def horizontalDirection : QI where
  re := 1
  im := 0

def verticalBase (x : ℚ) : QI where
  re := x
  im := 0

def verticalDirection : QI where
  re := 0
  im := 1

/-- The oriented horizontal edge `t + iy`, for `a → b`. -/
def horizontalEdge (p : GaussianPolynomial) (y a b : ℚ) : PolynomialEdge :=
  PolynomialEdge.ofLine p (horizontalBase y) horizontalDirection a b

/-- The oriented vertical edge `x + it`, for `a → b`. -/
def verticalEdge (p : GaussianPolynomial) (x a b : ℚ) : PolynomialEdge :=
  PolynomialEdge.ofLine p (verticalBase x) verticalDirection a b

@[simp] theorem line_horizontal (y t : ℚ) :
    line (horizontalBase y) horizontalDirection t = (CCL.GaussianRat.mk t y) := by
  ext <;> simp [line, horizontalBase, horizontalDirection, ofRat]

@[simp] theorem line_vertical (x t : ℚ) :
    line (verticalBase x) verticalDirection t = (CCL.GaussianRat.mk x t) := by
  ext <;> simp [line, verticalBase, verticalDirection, ofRat]

theorem horizontalEdge_real_eval (p : GaussianPolynomial) (y a b t : ℚ) :
    (horizontalEdge p y a b).realPart.eval t =
      (p.eval (CCL.GaussianRat.mk t y)).re := by
  simpa only [horizontalEdge, line_horizontal] using
    PolynomialEdge.ofLine_real_eval p (horizontalBase y) horizontalDirection a b t

theorem horizontalEdge_imag_eval (p : GaussianPolynomial) (y a b t : ℚ) :
    (horizontalEdge p y a b).imagPart.eval t =
      (p.eval (CCL.GaussianRat.mk t y)).im := by
  simpa only [horizontalEdge, line_horizontal] using
    PolynomialEdge.ofLine_imag_eval p (horizontalBase y) horizontalDirection a b t

theorem verticalEdge_real_eval (p : GaussianPolynomial) (x a b t : ℚ) :
    (verticalEdge p x a b).realPart.eval t =
      (p.eval (CCL.GaussianRat.mk x t)).re := by
  simpa only [verticalEdge, line_vertical] using
    PolynomialEdge.ofLine_real_eval p (verticalBase x) verticalDirection a b t

theorem verticalEdge_imag_eval (p : GaussianPolynomial) (x a b t : ℚ) :
    (verticalEdge p x a b).imagPart.eval t =
      (p.eval (CCL.GaussianRat.mk x t)).im := by
  simpa only [verticalEdge, line_vertical] using
    PolynomialEdge.ofLine_imag_eval p (verticalBase x) verticalDirection a b t

/-- Positively oriented four-edge boundary of a rational box. -/
def boxBoundary (p : GaussianPolynomial) (B : CCL.RatBox) : List PolynomialEdge :=
  [ horizontalEdge p B.yLower B.xLower B.xUpper,
    verticalEdge p B.xUpper B.yLower B.yUpper,
    horizontalEdge p B.yUpper B.xUpper B.xLower,
    verticalEdge p B.xLower B.yUpper B.yLower ]

/-- Sum of the four doubled Cauchy indices.  Because `cauchyIndex2` stores
twice the ordinary Cauchy index, this raw finite sum is four times the usual
integer winding on a clear boundary. -/
def quadrupledBoxWinding (p : GaussianPolynomial) (B : CCL.RatBox) : ℤ :=
  (boxBoundary p B).map PolynomialEdge.doubledWinding |>.sum

theorem quadrupledBoxWinding_eq (p : GaussianPolynomial) (B : CCL.RatBox) :
    quadrupledBoxWinding p B =
      (horizontalEdge p B.yLower B.xLower B.xUpper).doubledWinding +
      (verticalEdge p B.xUpper B.yLower B.yUpper).doubledWinding +
      (horizontalEdge p B.yUpper B.xUpper B.xLower).doubledWinding +
      (verticalEdge p B.xLower B.yUpper B.yLower).doubledWinding := by
  simp [quadrupledBoxWinding, boxBoundary]
  ring

/-- Definition 4.1's `Wind₂`, normalized from the doubled-index engine. -/
def doubledBoxWinding (p : GaussianPolynomial) (B : CCL.RatBox) : ℤ :=
  quadrupledBoxWinding p B / 2

/-- The ordinary integer winding normalization used after boundary parity has
been certified. -/
def boxWinding (p : GaussianPolynomial) (B : CCL.RatBox) : ℤ :=
  quadrupledBoxWinding p B / 4

private theorem horizontal_add (p : GaussianPolynomial) (y a b c : ℚ) :
    (horizontalEdge p y a b).doubledWinding +
      (horizontalEdge p y b c).doubledWinding =
        (horizontalEdge p y a c).doubledWinding := by
  exact cauchyIndex2_add _ _ a b c

private theorem vertical_add (p : GaussianPolynomial) (x a b c : ℚ) :
    (verticalEdge p x a b).doubledWinding +
      (verticalEdge p x b c).doubledWinding =
        (verticalEdge p x a c).doubledWinding := by
  exact cauchyIndex2_add _ _ a b c

private theorem horizontal_reverse (p : GaussianPolynomial) (y a b : ℚ) :
    (horizontalEdge p y b a).doubledWinding =
      -(horizontalEdge p y a b).doubledWinding := by
  exact cauchyIndex2_reverse _ _ a b

private theorem vertical_reverse (p : GaussianPolynomial) (x a b : ℚ) :
    (verticalEdge p x b a).doubledWinding =
      -(verticalEdge p x a b).doubledWinding := by
  exact cauchyIndex2_reverse _ _ a b

/-- Lemma 4.2 for a vertical rational subdivision.  The internal vertical
edge occurs twice with opposite orientations and cancels exactly. -/
theorem quadrupledBoxWinding_vertical_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.xLower ≤ c ∧ c ≤ B.xUpper) :
    quadrupledBoxWinding p B =
      quadrupledBoxWinding p (B.verticalLeft c hc) +
        quadrupledBoxWinding p (B.verticalRight c hc) := by
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq, quadrupledBoxWinding_eq]
  dsimp only [CCL.RatBox.verticalLeft, CCL.RatBox.verticalRight]
  have hbottom := horizontal_add p B.yLower B.xLower c B.xUpper
  have htop := horizontal_add p B.yUpper B.xUpper c B.xLower
  have hinternal := vertical_reverse p c B.yLower B.yUpper
  omega

/-- Lemma 4.2 for a horizontal rational subdivision.  The internal horizontal
edge occurs twice with opposite orientations and cancels exactly. -/
theorem quadrupledBoxWinding_horizontal_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.yLower ≤ c ∧ c ≤ B.yUpper) :
    quadrupledBoxWinding p B =
      quadrupledBoxWinding p (B.horizontalLower c hc) +
        quadrupledBoxWinding p (B.horizontalUpper c hc) := by
  rw [quadrupledBoxWinding_eq, quadrupledBoxWinding_eq, quadrupledBoxWinding_eq]
  dsimp only [CCL.RatBox.horizontalLower, CCL.RatBox.horizontalUpper]
  have hright := vertical_add p B.xUpper B.yLower c B.yUpper
  have hleft := vertical_add p B.xLower B.yUpper c B.yLower
  have hinternal := horizontal_reverse p c B.xLower B.xUpper
  omega

/-- One vertical and one horizontal cut give the four-child grid additivity
used by the finite extraction routine. -/
theorem quadrupledBoxWinding_four_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (cx cy : ℚ) (hcx : B.xLower ≤ cx ∧ cx ≤ B.xUpper)
    (hcy : B.yLower ≤ cy ∧ cy ≤ B.yUpper) :
    let L := B.verticalLeft cx hcx
    let R := B.verticalRight cx hcx
    let hcyL : L.yLower ≤ cy ∧ cy ≤ L.yUpper := hcy
    let hcyR : R.yLower ≤ cy ∧ cy ≤ R.yUpper := hcy
    quadrupledBoxWinding p B =
      quadrupledBoxWinding p (L.horizontalLower cy hcyL) +
      quadrupledBoxWinding p (L.horizontalUpper cy hcyL) +
      quadrupledBoxWinding p (R.horizontalLower cy hcyR) +
      quadrupledBoxWinding p (R.horizontalUpper cy hcyR) := by
  dsimp only
  rw [quadrupledBoxWinding_vertical_split p B cx hcx,
    quadrupledBoxWinding_horizontal_split p (B.verticalLeft cx hcx) cy hcy,
    quadrupledBoxWinding_horizontal_split p (B.verticalRight cx hcx) cy hcy]
  ring

/-! ## Normalized subdivision -/

/-- Once the two child raw sums are even, the paper's doubled normalization
inherits vertical additivity exactly. -/
theorem doubledBoxWinding_vertical_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.xLower ≤ c ∧ c ≤ B.xUpper)
    (hleft : Even (quadrupledBoxWinding p (B.verticalLeft c hc)))
    (hright : Even (quadrupledBoxWinding p (B.verticalRight c hc))) :
    doubledBoxWinding p B =
      doubledBoxWinding p (B.verticalLeft c hc) +
        doubledBoxWinding p (B.verticalRight c hc) := by
  rcases hleft with ⟨left, hleft⟩
  rcases hright with ⟨right, hright⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_vertical_split p B c hc, hleft, hright]
  omega

theorem doubledBoxWinding_horizontal_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.yLower ≤ c ∧ c ≤ B.yUpper)
    (hlower : Even (quadrupledBoxWinding p (B.horizontalLower c hc)))
    (hupper : Even (quadrupledBoxWinding p (B.horizontalUpper c hc))) :
    doubledBoxWinding p B =
      doubledBoxWinding p (B.horizontalLower c hc) +
        doubledBoxWinding p (B.horizontalUpper c hc) := by
  rcases hlower with ⟨lower, hlower⟩
  rcases hupper with ⟨upper, hupper⟩
  rw [doubledBoxWinding, doubledBoxWinding, doubledBoxWinding,
    quadrupledBoxWinding_horizontal_split p B c hc, hlower, hupper]
  omega

/-- Ordinary winding additivity follows once each child raw sum is certified
divisible by four, the parity condition for a clear closed boundary in this
doubled-index representation. -/
theorem boxWinding_vertical_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.xLower ≤ c ∧ c ≤ B.xUpper)
    (hleft : (4 : ℤ) ∣ quadrupledBoxWinding p (B.verticalLeft c hc))
    (hright : (4 : ℤ) ∣ quadrupledBoxWinding p (B.verticalRight c hc)) :
    boxWinding p B =
      boxWinding p (B.verticalLeft c hc) +
        boxWinding p (B.verticalRight c hc) := by
  rcases hleft with ⟨left, hleft⟩
  rcases hright with ⟨right, hright⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_vertical_split p B c hc, hleft, hright]
  omega

theorem boxWinding_horizontal_split (p : GaussianPolynomial) (B : CCL.RatBox)
    (c : ℚ) (hc : B.yLower ≤ c ∧ c ≤ B.yUpper)
    (hlower : (4 : ℤ) ∣ quadrupledBoxWinding p (B.horizontalLower c hc))
    (hupper : (4 : ℤ) ∣ quadrupledBoxWinding p (B.horizontalUpper c hc)) :
    boxWinding p B =
      boxWinding p (B.horizontalLower c hc) +
        boxWinding p (B.horizontalUpper c hc) := by
  rcases hlower with ⟨lower, hlower⟩
  rcases hupper with ⟨upper, hupper⟩
  rw [boxWinding, boxWinding, boxWinding,
    quadrupledBoxWinding_horizontal_split p B c hc, hlower, hupper]
  omega

private def identityPolynomial : GaussianPolynomial := ⟨[1, 0]⟩
private def unitSquare : CCL.RatBox := CCL.RatBox.symmetric 1 (by norm_num)

/-- Regression fixing the normalization from Proposition 4.3: the raw engine
returns four, the paper's doubled winding is two, and ordinary winding is one. -/
theorem identity_unitSquare_normalization :
    quadrupledBoxWinding identityPolynomial unitSquare = 4 ∧
      doubledBoxWinding identityPolynomial unitSquare = 2 ∧
      boxWinding identityPolynomial unitSquare = 1 := by
  native_decide

end FTA.Winding
