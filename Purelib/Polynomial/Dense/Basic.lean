module
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
import Purelib.Data.List.DropWhile.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.Field.ExplicitField
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable dense polynomials and finite Euclidean division

Mathlib's sparse `Polynomial` arithmetic is intended for specifications at the
representation level.  The FTA algorithms therefore use this separate dense
coefficient program.  Coefficients are stored highest-degree first; leading
zeros are removed by a finite `dropWhile` pass.
-/

namespace Purelib

namespace Polynomial.Dense.Basic

set_option genInjectivity false in
/-- A finite high-to-low coefficient list. -/
structure DensePolynomial (K : Type*) where
  /-- The retained finite coefficient list, from highest degree to constant term. -/ coeffs : List K
deriving DecidableEq

constructive_injectivity DensePolynomial

end Polynomial.Dense.Basic

open Purelib.Polynomial

section DensePolynomial

open Purelib.Data.List

variable {K : Type*} [ExplicitField K] [DecidableEq K]

namespace Polynomial.Dense.Basic.DensePolynomial

omit [ExplicitField K] [DecidableEq K] in
/-- Equality of retained coefficient lists determines equality of dense polynomials. -/
@[ext] theorem ext {p q : DensePolynomial K} (h :
  p.coeffs = q.coeffs) : p = q := by
  cases p with
  | mk left =>
      cases q with
      | mk right =>
          change left = right at h
          cases h
          rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Algebra.Polynomial.DensePolynomial

open Purelib.Polynomial in
/-- The dense zero instance uses the empty coefficient list. -/
instance : Zero (Dense.Basic.DensePolynomial K) := ⟨⟨[]⟩⟩

end Algebra.Polynomial.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

omit [ExplicitField K] [DecidableEq K] in
open Purelib.Polynomial in
/-- The dense zero representation has an empty coefficient list. -/
@[simp] theorem zero_coeffs : (0 : DensePolynomial
  K).coeffs = [] := rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- Constant dense polynomial. -/
def constant (a : K) : DensePolynomial K := ⟨[a]⟩

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

omit [ExplicitField K] [DecidableEq K] in
open Purelib.Polynomial in
/-- The dense constant representation has the singleton coefficient list. -/
@[simp] theorem constant_coeffs (a : K) :
  (constant a).coeffs = [a] := rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- Remove representation-only leading zero coefficients. -/
def normalize (p : DensePolynomial K) :
  DensePolynomial K :=
  ⟨p.coeffs.dropWhile (· = 0)⟩

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Repeating leading-zero normalization preserves the retained coefficients. -/
@[simp] theorem normalize_normalize (p :
  DensePolynomial K) :
    p.normalize.normalize = p.normalize := by
  apply Dense.Basic.DensePolynomial.ext
  change (p.coeffs.dropWhile (· = 0)).dropWhile (· = 0) =
    p.coeffs.dropWhile (· = 0)
  exact DropWhile.idempotent _ p.coeffs

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- The empty zero polynomial is already normalized. -/
@[simp] theorem normalize_zero :
  Dense.Basic.DensePolynomial.normalize (0 : DensePolynomial K) = 0 := rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A nonzero constant already has a normalized coefficient list. -/
theorem normalize_constant_of_ne {a : K} (ha : a ≠ 0) :
    Dense.Basic.DensePolynomial.normalize (constant a) =
      constant a := by
  apply Dense.Basic.DensePolynomial.ext
  exact DropWhile.cons_of_false (fun value => decide (value = 0)) a []
    (decide_eq_false ha)

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Normalizing the zero constant removes its single zero coefficient. -/
@[simp] theorem normalize_constant_zero :
    Dense.Basic.DensePolynomial.normalize (constant (0 : K)) = 0 := by
  apply Dense.Basic.DensePolynomial.ext
  exact DropWhile.cons_of_true (fun value : K => decide (value = 0)) 0 []
    (decide_eq_true rfl)

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A displayed linear polynomial with a nonzero leading coefficient is normalized. -/
theorem normalize_linear_of_leading_ne_zero {leading trailing : K}
    (leadingNonzero : leading ≠ 0) :
    Dense.Basic.DensePolynomial.normalize ⟨[leading, trailing]⟩ = ⟨[leading, trailing]⟩ := by
  apply Dense.Basic.DensePolynomial.ext
  exact DropWhile.cons_of_false (fun value => decide (value = 0)) leading [trailing]
    (decide_eq_false leadingNonzero)

end Polynomial.Dense.Basic.DensePolynomial

section
open Purelib.Polynomial
namespace Polynomial.Dense.Basic.DensePolynomial

/-- Normalization drops exactly the initial zero coefficient block. -/
@[simp] theorem normalize_coeffs (p : DensePolynomial
  K) :
    p.normalize.coeffs = p.coeffs.dropWhile (· = 0) := rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Exact zero test on normalized finite coefficients. -/
def isZero (p : DensePolynomial K) : Bool :=
  p.normalize.coeffs.isEmpty

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- The empty dense zero polynomial passes the zero test. -/
@[simp] theorem isZero_zero : Dense.Basic.DensePolynomial.isZero
  (0 : DensePolynomial K) = true := rfl

end Polynomial.Dense.Basic.DensePolynomial

end

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Normalization preserves the Boolean zero test. -/
@[simp] theorem isZero_normalize (p : DensePolynomial
  K) :
    p.normalize.isZero = p.isZero := by
  exact congrArg (fun value => value.coeffs.isEmpty) p.normalize_normalize

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- Number of nonzero degree slots; zero has degree count zero and a degree
`d` polynomial has degree count `d+1`. -/
def degreeCount (p : DensePolynomial K) : ℕ :=
  p.normalize.coeffs.length

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A polynomial accepted by the zero test has no normalized degree slots. -/
theorem degreeCount_eq_zero_of_isZero {p :
  DensePolynomial K} (hp : p.isZero = true) :
    p.degreeCount = 0 := by
  change p.normalize.coeffs.isEmpty = true at hp
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.length = 0
      rw [coefficients]
      rfl
  | cons head tail =>
      rw [coefficients] at hp
      exact Bool.noConfusion hp

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Having no normalized degree slots makes the Boolean zero test true. -/
theorem isZero_true_of_degreeCount_eq_zero {p :
  DensePolynomial K}
    (count : p.degreeCount = 0) : p.isZero = true := by
  change p.normalize.coeffs.length = 0 at count
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.isEmpty = true
      rw [coefficients]
      rfl
  | cons head tail =>
      rw [coefficients] at count
      exact Nat.noConfusion count

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A polynomial accepted by the zero test normalizes to the empty representation. -/
theorem normalize_eq_zero_of_isZero {p :
  DensePolynomial K}
    (hp : p.isZero = true) : p.normalize = 0 := by
  apply Dense.Basic.DensePolynomial.ext
  change p.normalize.coeffs = []
  change p.normalize.coeffs.isEmpty = true at hp
  cases coefficients : p.normalize.coeffs with
  | nil => rfl
  | cons head tail =>
      rw [coefficients] at hp
      exact Bool.noConfusion hp

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- A polynomial failing the zero test has positive normalized coefficient count. -/
theorem degreeCount_pos_of_isZero_false {p :
  DensePolynomial K} (hp : p.isZero = false) :
    0 < p.degreeCount := by
  change p.normalize.coeffs.isEmpty = false at hp
  cases hcoeffs : p.normalize.coeffs with
  | nil =>
      rw [hcoeffs] at hp
      exact Bool.noConfusion hp
  | cons a as =>
      change 0 < p.normalize.coeffs.length
      rw [hcoeffs]
      exact Nat.zero_lt_succ _

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Normalization preserves the number of normalized degree slots. -/
@[simp] theorem degreeCount_normalize (p :
  DensePolynomial K) :
    p.normalize.degreeCount = p.degreeCount := by
  exact congrArg (fun value => value.coeffs.length) p.normalize_normalize

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- Natural degree, with the conventional junk value zero for the zero polynomial. -/
def natDegree (p : DensePolynomial K) : ℕ :=
  p.degreeCount - 1

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Normalization preserves the natural degree, including its zero-polynomial value. -/
@[simp] theorem natDegree_normalize (p :
  DensePolynomial K) :
    p.normalize.natDegree = p.natDegree := by
  exact congrArg (fun count : Nat => count - 1) p.degreeCount_normalize

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A nonzero polynomial has exactly one more degree slot than its natural degree. -/
theorem natDegree_add_one_eq_degreeCount {p :
  DensePolynomial K} (hp : p.isZero = false) :
    p.natDegree + 1 = p.degreeCount := by
  have positive := p.degreeCount_pos_of_isZero_false hp
  change p.degreeCount - 1 + 1 = p.degreeCount
  cases count : p.degreeCount with
  | zero =>
      rw [count] at positive
      exact Nat.not_lt_zero 0 positive |>.elim
  | succ value =>
      rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial in
/-- Leading coefficient, or zero for the zero polynomial. -/
def leadingCoeff (p : DensePolynomial K) : K :=
  p.normalize.coeffs.headD 0

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A nonempty zero-prefix scan retains a nonzero head coefficient. -/
private theorem dropWhile_headD_ne_zero (cs : List K)
    (h : (cs.dropWhile (· = 0)).isEmpty = false) :
    (cs.dropWhile (· = 0)).headD 0 ≠ 0 := by
  induction cs with
  | nil => exact Bool.noConfusion h
  | cons a as ih =>
      by_cases ha : a = 0
      · rw [DropWhile.cons_of_true _ a as (decide_eq_true ha)] at h ⊢
        exact ih h
      · rw [DropWhile.cons_of_false _ a as (decide_eq_false ha)]
        exact ha

end Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial
namespace Polynomial.Dense.Basic.DensePolynomial

/-- A polynomial failing the zero test has nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero {p : DensePolynomial K}
  (hp : p.isZero = false) :
    p.leadingCoeff ≠ 0 := by
  change (p.coeffs.dropWhile (· = 0)).headD 0 ≠ 0
  apply dropWhile_headD_ne_zero
  exact hp

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- Exact finite normalized coefficient shape of a represented nonzero
polynomial.

A represented nonzero polynomial has a retained first nonzero coefficient followed
by the exact remaining normalized list. Its degree count agrees with that list
length. -/
theorem normalized_coeffs_shape {p : DensePolynomial
  K}
    (nonzero : p.isZero = false) :
    ∃ tail,
      p.normalize.coeffs = p.leadingCoeff :: tail ∧
        tail.length = p.natDegree := by
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.isEmpty = false at nonzero
      rw [coefficients] at nonzero
      exact Bool.noConfusion nonzero
  | cons leading tail =>
      refine ⟨tail, ?_, ?_⟩
      · unfold leadingCoeff
        rw [coefficients]
        rfl
      · change tail.length = p.normalize.coeffs.length - 1
        rw [coefficients]
        rfl

end Polynomial.Dense.Basic.DensePolynomial

namespace Polynomial.Dense.Basic.DensePolynomial

/-- A represented nonzero polynomial of natural degree zero normalizes to its
single displayed leading coefficient.

For a represented nonzero polynomial with natural degree zero, the normalized list
contains exactly one nonzero coefficient. That retained coefficient is the leading
coefficient. -/
theorem normalize_eq_constant_leadingCoeff_of_degree_zero
    {p : DensePolynomial K} (nonzero : p.isZero = false)
    (degreeZero : p.natDegree = 0) :
    p.normalize = constant p.leadingCoeff := by
  have count := natDegree_add_one_eq_degreeCount nonzero
  rw [degreeZero] at count
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change 0 + 1 = p.normalize.coeffs.length at count
      rw [coefficients] at count
      exact Nat.noConfusion count
  | cons leading tail =>
      cases tail with
      | nil =>
          apply Dense.Basic.DensePolynomial.ext
          change p.normalize.coeffs = [p.leadingCoeff]
          rw [coefficients]
          unfold leadingCoeff
          rw [coefficients]
          rfl
      | cons next remaining =>
          change 0 + 1 = p.normalize.coeffs.length at count
          rw [coefficients] at count
          change 1 = remaining.length + 2 at count
          have impossible : 0 = remaining.length + 1 := Nat.succ.inj count
          exact Nat.noConfusion impossible

end Polynomial.Dense.Basic.DensePolynomial

end DensePolynomial

end Purelib

end

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial in
/-- The dense high-to-low polynomial representation over the supplied coefficient type. -/
abbrev CoefficientPolynomial (K : Type*) := DensePolynomial K
end Purelib.Polynomial.Dense.Basic

end

section
@[expose] public section

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

namespace Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial in
/-- The existing dense polynomial representation with constructive rational coefficients. -/
abbrev RationalPolynomial :=
  DensePolynomial Fraction.Rational

end Purelib.Polynomial.Dense.Basic
end

section
@[expose] public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.CCL.Boundary.Curve.BoxEventPartition
end Purelib.CCL.Boundary.Curve.BoxEventPartition

end

section
@[expose] public section

/-!
# Finite global clearance for a rationally parameterized curve

The real and imaginary denominator-cleared substitutions are ordinary finite
dense coordinate polynomials.  Their executable extended gcd therefore
decides an important easy case: a nonzero constant gcd certifies that the
displayed polynomial has no root at any finite parameter of the curve.

Local root counts for a nonconstant gcd are left to the subsequent Sturm
layer; this module supplies the algebraic reduction and its proof.
-/

namespace Purelib.CCL.Boundary.Curve.Clear
end Purelib.CCL.Boundary.Curve.Clear

end

section
@[expose] public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.BoundaryFactorization
open Purelib.Polynomial in
/-- The existing dense polynomial representation with constructive rational coefficients. -/
abbrev CoefficientPolynomial := Dense.Basic.DensePolynomial Fraction.Rational
end Purelib.Polynomial.Dense.BoundaryFactorization

end

section
@[expose] public section

/-!
# Constructive root events on rationally parameterized curves

The constant-gcd branch of `CurveClear` excludes a polynomial
root everywhere on a rational curve.  This module handles the complementary
finite cases.  If both cleared coordinates vanish identically it records that
degeneracy explicitly.  Otherwise a nonconstant gcd is an ordinary nonzero
coordinate polynomial, so its derivative/gcd Sturm chain has the executable
event partition constructed in `ConstructiveSturmEventPartition`.
-/

namespace Purelib.CCL.Boundary.Curve.Events
end Purelib.CCL.Boundary.Curve.Events

end

section
@[expose] public section

/-!
# Finite rational curves and denominator-cleared polynomial evaluation

A rationally parameterized Gaussian curve is represented by two finite dense
Gaussian polynomials `N(t)` and `D(t)`.  Evaluation means `N(t) / D(t)` only
at an explicitly supplied nonzero denominator.  A Horner fold computes
`D(t)^n p(N(t)/D(t))` without division; its real and imaginary coefficient
polynomials are therefore suitable for finite gcd and Sturm calculations.
-/

namespace Purelib.CCL.Boundary.Curve.Rational

/- The doubled public name `Purelib.CCL.Boundary.Curve.Rational.RationalCurve` is intentional:
the outer component names the module and the inner component names its main
finite data type. -/
end Purelib.CCL.Boundary.Curve.Rational

end

section
@[expose] public section

/-!
# Quantitative projective bounds for finite rational curves

The homogeneous numerator and denominator of a rational curve are ordinary
finite coordinate polynomials.  Componentwise Horner bounds therefore give
an explicit Lipschitz coefficient for their projective cross product.  Once
the denominator coordinates carry a positive Bézout clearance on a bounded
parameter interval, this becomes a squared-chordal image bound proportional
to the square of the parameter width.

No affine division, square root, completed point, or limiting argument is
used.  The result is the finite shrinking-cylinder estimate needed to compare
a persistent curve event with a simultaneously shrinking winding box.
-/

namespace Purelib.CCL.Boundary.Curve.RationalBounds
end Purelib.CCL.Boundary.Curve.RationalBounds

end

section
@[expose] public section

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

namespace Purelib.CCL.Boundary.CurveFormula
end Purelib.CCL.Boundary.CurveFormula

end

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Data.List

universe u_1

variable {K : Type u_1} [field : ExplicitField K]

/-- Normalization retains the same finite coefficient suffix under either supplied equality procedure.

Each procedure decides the same scalar equality to the retained field's zero.
The proof follows those original Boolean branches on the finite coefficient list.
-/
public theorem normalize_eq_of_decidableEq (first second : DecidableEq K)
    (p : DensePolynomial K) :
    @normalize K field first p = @normalize K field second p := by
  apply ext
  change p.coeffs.dropWhile (fun value => @decide (value = 0) (first value 0)) =
    p.coeffs.dropWhile (fun value => @decide (value = 0) (second value 0))
  induction p.coeffs with
  | nil => rfl
  | cons head tail agreement =>
      cases first head 0 with
      | isTrue zero =>
        have firstSelected : @decide (head = 0) (first head 0) = true :=
          @decide_eq_true (head = 0) (first head 0) zero
        have secondSelected : @decide (head = 0) (second head 0) = true :=
          @decide_eq_true (head = 0) (second head 0) zero
        rewrite [DropWhile.cons_of_true _ head tail firstSelected,
          DropWhile.cons_of_true _ head tail secondSelected]
        exact agreement
      | isFalse zero =>
        have firstRetained : @decide (head = 0) (first head 0) = false :=
          @decide_eq_false (head = 0) (first head 0) zero
        have secondRetained : @decide (head = 0) (second head 0) = false :=
          @decide_eq_false (head = 0) (second head 0) zero
        rewrite [DropWhile.cons_of_false _ head tail firstRetained,
          DropWhile.cons_of_false _ head tail secondRetained]
        rfl

/-- Equal polynomial inputs have the same normalized zero test under the supplied procedures. -/
private theorem isZero_agreement {first : DecidableEq K} [second : DecidableEq K]
    (p p' : DensePolynomial K) (same : p = p') :
    @isZero K field first p = @isZero K field second p' := by
  cases same
  exact congrArg (fun value : DensePolynomial K => value.coeffs.isEmpty)
    (normalize_eq_of_decidableEq first second p)

/-- Equal polynomial inputs have the same normalized degree count under the supplied procedures. -/
private theorem degreeCount_agreement {first : DecidableEq K} [second : DecidableEq K]
    (p p' : DensePolynomial K) (same : p = p') :
    @degreeCount K field first p = @degreeCount K field second p' := by
  cases same
  exact congrArg (fun value : DensePolynomial K => value.coeffs.length)
    (normalize_eq_of_decidableEq first second p)

/-- Equal polynomial inputs have the same natural degree under the supplied procedures. -/
private theorem natDegree_agreement {first : DecidableEq K} [second : DecidableEq K]
    (p p' : DensePolynomial K) (same : p = p') :
    @natDegree K field first p = @natDegree K field second p' := by
  exact congrArg (fun count : Nat => count - 1)
    (@degreeCount_agreement K field first second p p' same)

open Lean Elab Command in
run_elab do
  let kinds : Array Meta.CongrArgKind := #[.fixed, .fixed, .subsingletonInst, .eq]
  for (operation, agreement) in [(``isZero, ``isZero_agreement),
      (``degreeCount, ``degreeCount_agreement), (``natDegree, ``natDegree_agreement)] do
    let name := Name.str operation "congr_simp"
    let .thmInfo info ← getConstInfo agreement
      | throwError "finite normalization agreement is not a safe theorem"
    let operationInfo ← getConstInfo operation
    let .forallE carrier _ operationType _ := operationInfo.type
      | throwError "normalization readback has no carrier binder"
    let .forallE field _ operationType _ := operationType
      | throwError "normalization readback has no retained field binder"
    let .forallE procedure _ operationType _ := operationType
      | throwError "normalization readback has no equality procedure"
    let .forallE polynomial _ _ _ := operationType
      | throwError "normalization readback has no polynomial binder"
    let names := #[carrier, field, procedure, procedure, polynomial, polynomial,
      Name.str .anonymous ("e_" ++ polynomial.toString)]
    let rec retainNames (type : Expr) (index : Nat) : Expr :=
      match type with
      | .forallE original domain body mode =>
          .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
      | other => other
    Meta.realizeConst operation name do
      addDecl (.thmDecl {
        name, type := retainNames info.type 0, levelParams := info.levelParams
        value := info.value
      }) (forceExpose := true)
      modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
    let some congrThm ← Meta.mkCongrSimpForConst? operation (operationInfo.levelParams.map Level.param)
      | throwError "original normalization congruence lookup failed"
    unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
      throwError "automatic lookup changed the normalization certificate"

end Purelib.Polynomial.Dense.Basic.DensePolynomial
