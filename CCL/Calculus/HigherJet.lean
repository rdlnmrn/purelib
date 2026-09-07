import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FinitePolynomial

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace CCL.HigherJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := CCL.FinitePolynomial.Polynomial

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite one-variable Taylor jet, represented by its displayed
low-to-high rational coefficient list. -/
structure TaylorJet where
  polynomial : Polynomial
deriving DecidableEq

namespace TaylorJet

def ofCoefficients (coefficients : List Coordinate) : TaylorJet :=
  ⟨⟨coefficients⟩⟩

def coefficients (jet : TaylorJet) : List Coordinate :=
  jet.polynomial.coefficients

def coefficient (jet : TaylorJet) (degree : Nat) : Coordinate :=
  CCL.FinitePolynomial.coefficient jet.polynomial degree

def evaluate (jet : TaylorJet) (increment : Gaussian) : Gaussian :=
  CCL.FinitePolynomial.eval jet.polynomial increment

def truncate (count : Nat) (jet : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.truncate count jet.polynomial⟩

def add (left right : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.add left.polynomial right.polynomial⟩

def scale (factor : Coordinate) (jet : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.scale factor jet.polynomial⟩

/-- Truncated or untruncated multiplication is selected explicitly by the
caller; this constructor retains the whole finite Cauchy product. -/
def mul (left right : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.mul left.polynomial right.polynomial⟩

def compose (outer inner : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.compose
    outer.polynomial inner.polynomial⟩

def derivative (jet : TaylorJet) : TaylorJet :=
  ⟨CCL.FinitePolynomial.derivative jet.polynomial⟩

/-- The requested finite higher derivative table. -/
def derivativeOrder : TaylorJet → Nat → TaylorJet
  | jet, 0 => jet
  | jet, order + 1 => derivative (derivativeOrder jet order)

/-- The displayed higher coefficient at the expansion origin. -/
def higherCoefficient (jet : TaylorJet) (order : Nat) : Coordinate :=
  (jet.derivativeOrder order).coefficient 0

@[simp] theorem derivativeOrder_zero (jet : TaylorJet) :
    jet.derivativeOrder 0 = jet := rfl

@[simp] theorem derivativeOrder_succ (jet : TaylorJet) (order : Nat) :
    jet.derivativeOrder (order + 1) =
      (jet.derivativeOrder order).derivative := rfl

@[simp] theorem evaluate_add (left right : TaylorJet)
    (increment : Gaussian) :
    (left.add right).evaluate increment =
      left.evaluate increment + right.evaluate increment :=
  CCL.FinitePolynomial.eval_add
    left.polynomial right.polynomial increment

@[simp] theorem evaluate_mul (left right : TaylorJet)
    (increment : Gaussian) :
    (left.mul right).evaluate increment =
      left.evaluate increment * right.evaluate increment :=
  CCL.FinitePolynomial.eval_mul
    left.polynomial right.polynomial increment

@[simp] theorem evaluate_compose (outer inner : TaylorJet)
    (increment : Gaussian) :
    (outer.compose inner).evaluate increment =
      outer.evaluate (inner.evaluate increment) :=
  CCL.FinitePolynomial.eval_compose
    outer.polynomial inner.polynomial increment

/-- Every coefficient of a product is the displayed finite Cauchy row. -/
theorem coefficient_mul (left right : TaylorJet) (degree : Nat) :
    (left.mul right).coefficient degree =
      CCL.FinitePolynomial.coordinateSum
        (fun leftDegree =>
          left.coefficient leftDegree *
            right.coefficient (degree - leftDegree))
        (degree + 1) :=
  CCL.FinitePolynomial.coefficient_mul
    left.polynomial right.polynomial degree

/-- The finite higher-jet product rule holds coefficient by coefficient. -/
theorem derivative_mul (left right : TaylorJet) :
    CCL.FinitePolynomial.CoefficientwiseEqual
      (left.mul right).derivative.polynomial
      ((left.derivative.mul right).add
        (left.mul right.derivative)).polynomial :=
  CCL.FinitePolynomial.derivative_mul
    left.polynomial right.polynomial

end TaylorJet

/-! ## Finite-dimensional first jets -/

def addPartials : List Gaussian → List Gaussian → List Gaussian
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      (left + right) :: addPartials leftTail rightTail

def scalePartials (factor : Gaussian) (partials : List Gaussian) :
    List Gaussian :=
  partials.map (factor * ·)

/-- Finite dot product; missing coordinates are not manufactured. -/
def dot : List Gaussian → List Gaussian → Gaussian
  | left :: leftTail, right :: rightTail =>
      left * right + dot leftTail rightTail
  | _, _ => 0

theorem dot_addPartials : ∀ left right direction,
    dot (addPartials left right) direction =
      dot left direction + dot right direction
  | [], right, direction => by
      simp only [addPartials]
      cases direction <;>
        simp only [dot, RFAP.ConstructiveGaussian.Gaussian.zero_add]
  | left :: leftTail, [], direction => by
      simp only [addPartials]
      cases direction <;>
        simp only [dot, RFAP.ConstructiveGaussian.Gaussian.add_zero]
  | left :: leftTail, right :: rightTail, [] => by
      change (0 : Gaussian) = 0 + 0
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, zero_re, zero_im] <;> ring1
  | left :: leftTail, right :: rightTail,
      direction :: directionTail => by
      rw [addPartials, dot, dot, dot, dot_addPartials]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

theorem dot_scalePartials (factor : Gaussian) : ∀ partials direction,
    dot (scalePartials factor partials) direction =
      factor * dot partials direction
  | [], direction => by
      cases direction <;>
        simp only [scalePartials, List.map, dot, mul_zero]
  | coefficient :: partials, [] => by
      simp only [scalePartials, List.map, dot, mul_zero]
  | coefficient :: partials, direction :: directions => by
      have inductionHypothesis :=
        dot_scalePartials factor partials directions
      change dot (List.map (fun value => factor * value) partials) directions =
        factor * dot partials directions at inductionHypothesis
      rw [scalePartials, List.map, dot, dot, inductionHypothesis]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

/-- One value and a displayed finite list of partial coefficients. -/
structure MultivariableFirstJet where
  value : Gaussian
  partials : List Gaussian
deriving DecidableEq

namespace MultivariableFirstJet

def dimension (jet : MultivariableFirstJet) : Nat := jet.partials.length

def constant (dimension : Nat) (value : Gaussian) :
    MultivariableFirstJet :=
  ⟨value, List.replicate dimension 0⟩

def add (left right : MultivariableFirstJet) :
    MultivariableFirstJet :=
  ⟨left.value + right.value, addPartials left.partials right.partials⟩

def neg (jet : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨-jet.value, scalePartials (-1) jet.partials⟩

/-- The finite multivariable product rule, coordinate by coordinate. -/
def mul (left right : MultivariableFirstJet) :
    MultivariableFirstJet :=
  ⟨left.value * right.value,
    addPartials
      (scalePartials right.value left.partials)
      (scalePartials left.value right.partials)⟩

/-- Compose a displayed univariate value/slope pair with a multivariable
inner jet. -/
def compose (outerValue outerSlope : Gaussian)
    (inner : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨outerValue, scalePartials outerSlope inner.partials⟩

/-- A direction is accepted exactly when its displayed coordinate list has
the jet's displayed finite dimension. -/
def DirectionValid (jet : MultivariableFirstJet)
    (direction : List Gaussian) : Prop :=
  direction.length = jet.dimension

/-- Directional first coefficient, computed by finite recursion. -/
def directional (jet : MultivariableFirstJet)
    (direction : List Gaussian) : Gaussian :=
  dot jet.partials direction

theorem directional_add (left right : MultivariableFirstJet)
    (direction : List Gaussian) :
    (left.add right).directional direction =
      left.directional direction + right.directional direction :=
  dot_addPartials left.partials right.partials direction

theorem directional_mul (left right : MultivariableFirstJet)
    (direction : List Gaussian) :
    (left.mul right).directional direction =
      right.value * left.directional direction +
        left.value * right.directional direction := by
  change dot
      (addPartials
        (scalePartials right.value left.partials)
        (scalePartials left.value right.partials)) direction =
    right.value * dot left.partials direction +
      left.value * dot right.partials direction
  rw [dot_addPartials,
    dot_scalePartials, dot_scalePartials]

theorem directional_compose (outerValue outerSlope : Gaussian)
    (inner : MultivariableFirstJet) (direction : List Gaussian) :
    (inner.compose outerValue outerSlope).directional direction =
      outerSlope * inner.directional direction :=
  dot_scalePartials outerSlope inner.partials direction

end MultivariableFirstJet

end CCL.HigherJet
