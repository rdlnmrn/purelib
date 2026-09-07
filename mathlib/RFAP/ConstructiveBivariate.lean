import mathlib.Data.ConstructiveList
import mathlib.Data.ConstructiveFin
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructivePolynomial
import mathlib.RFAP.ConstructiveFiniteMatrix

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace RFAP.ConstructiveBivariate

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial (K : Type*) := RFAP.ComputablePolynomial.DensePolynomial K
abbrev Matrix (K : Type*) (n : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix K n

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- Outer coefficients are dense polynomials in the inner variable. -/
structure Bivariate (K : Type*) where
  coeffs : List (Polynomial K)
deriving DecidableEq

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

def zero : Bivariate K := ⟨[]⟩

def constant (a : K) : Bivariate K :=
  ⟨[RFAP.ComputablePolynomial.DensePolynomial.constant a]⟩

def outerX : Bivariate K :=
  ⟨[RFAP.ComputablePolynomial.DensePolynomial.constant 1,
    (0 : Polynomial K)]⟩

def innerX : Bivariate K := ⟨[⟨[1, 0]⟩]⟩

def padLeft (n : Nat) (coefficients : List (Polynomial K)) :
    List (Polynomial K) :=
  List.replicate n 0 ++ coefficients

def add (p q : Bivariate K) : Bivariate K :=
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  ⟨List.zipWith (fun a b => a + b) ps qs⟩

def neg (p : Bivariate K) : Bivariate K := ⟨p.coeffs.map (-·)⟩
def sub (p q : Bivariate K) : Bivariate K := add p (neg q)

def shiftOuter (p : Bivariate K) : Bivariate K :=
  if p.coeffs.isEmpty then zero else ⟨p.coeffs ++ [0]⟩

def scaleInner (coefficient : Polynomial K) (p : Bivariate K) : Bivariate K :=
  ⟨p.coeffs.map (coefficient * ·)⟩

def mul (p q : Bivariate K) : Bivariate K :=
  p.coeffs.foldl
    (fun accumulator coefficient =>
      add (shiftOuter accumulator) (scaleInner coefficient q)) zero

/-- Evaluate the inner variable first and the outer variable second. -/
def eval (p : Bivariate K) (outer inner : K) : K :=
  p.coeffs.foldl
    (fun accumulator coefficient =>
      accumulator * outer + coefficient.eval inner) 0

omit [DecidableEq K] in
@[simp] theorem eval_zero (outer inner : K) :
    eval zero outer inner = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem eval_constant (a outer inner : K) :
    eval (constant a) outer inner = a := by
  simp [eval, constant]

omit [DecidableEq K] in
@[simp] theorem eval_outerX (outer inner : K) :
    eval outerX outer inner = outer := by
  simp [eval, outerX]

omit [DecidableEq K] in
@[simp] theorem eval_innerX (outer inner : K) :
    eval innerX outer inner = inner := by
  rw [eval, innerX]
  change [(⟨[1, 0]⟩ : Polynomial K)].foldl
      (fun accumulator coefficient => accumulator * outer +
        coefficient.eval inner) 0 = inner
  simp [RFAP.ComputablePolynomial.DensePolynomial.eval, evalCoeffs]

omit [DecidableEq K] in
private theorem eval_foldl_append_zero (outer inner : K)
    (coefficients : List (Polynomial K)) (accumulator : K) :
    (coefficients ++ [0]).foldl
        (fun value (coefficient : Polynomial K) =>
          value * outer + coefficient.eval inner)
        accumulator =
      coefficients.foldl
        (fun value (coefficient : Polynomial K) =>
          value * outer + coefficient.eval inner)
        accumulator * outer := by
  rw [QuotientFreeList.foldl_append]
  let result := coefficients.foldl
    (fun value (coefficient : Polynomial K) =>
      value * outer + coefficient.eval inner) accumulator
  change result * outer + 0 = result * outer
  exact add_zero _

omit [DecidableEq K] in
@[simp] theorem eval_shiftOuter (p : Bivariate K) (outer inner : K) :
    eval (shiftOuter p) outer inner = eval p outer inner * outer := by
  rw [shiftOuter]
  split
  · rename_i empty
    have coefficientsEmpty : p.coeffs = [] := List.isEmpty_iff.mp empty
    simp [eval, zero, coefficientsEmpty]
  · exact eval_foldl_append_zero outer inner p.coeffs 0

private theorem eval_foldl_map_scaleInner
    (coefficient : Polynomial K) (outer inner : K) :
    ∀ (coefficients : List (Polynomial K)) (accumulator : K),
      (coefficients.map (coefficient * ·)).foldl
          (fun value a => value * outer + a.eval inner)
          (coefficient.eval inner * accumulator) =
        coefficient.eval inner *
          coefficients.foldl
            (fun value a => value * outer + a.eval inner) accumulator
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.map_cons, List.foldl_cons, eval_mul]
      rw [show coefficient.eval inner * accumulator * outer +
          coefficient.eval inner * a.eval inner =
        coefficient.eval inner * (accumulator * outer + a.eval inner) by
          ring1]
      exact eval_foldl_map_scaleInner coefficient outer inner remaining
        (accumulator * outer + a.eval inner)

@[simp] theorem eval_scaleInner (coefficient : Polynomial K) (p : Bivariate K)
    (outer inner : K) :
    eval (scaleInner coefficient p) outer inner =
      coefficient.eval inner * eval p outer inner := by
  change (p.coeffs.map (coefficient * ·)).foldl
      (fun value a => value * outer + a.eval inner) 0 =
    coefficient.eval inner * p.coeffs.foldl
      (fun value a => value * outer + a.eval inner) 0
  simpa only [show coefficient.eval inner * (0 : K) = 0 by ring1] using
    eval_foldl_map_scaleInner coefficient outer inner p.coeffs 0

omit [DecidableEq K] in
private theorem eval_foldl_replicate_zero (outer inner : K)
    (n : Nat) (coefficients : List (Polynomial K)) :
    (List.replicate n 0 ++ coefficients).foldl
        (fun value (a : Polynomial K) => value * outer + a.eval inner) 0 =
      coefficients.foldl
        (fun value (a : Polynomial K) => value * outer + a.eval inner) 0 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [List.replicate_succ, List.cons_append, List.foldl_cons]
      have zeroStep : (0 : K) * outer + (0 : Polynomial K).eval inner = 0 :=
        calc
          (0 : K) * outer + (0 : Polynomial K).eval inner =
              0 + (0 : Polynomial K).eval inner :=
            congrArg (fun value => value + (0 : Polynomial K).eval inner)
              (zero_mul outer)
          _ = 0 + 0 := congrArg (fun value => 0 + value)
            (RFAP.ComputablePolynomial.DensePolynomial.eval_zero inner)
          _ = 0 := zero_add 0
      rw [zeroStep]
      exact inductionHypothesis

private theorem eval_foldl_zipWith_add (outer inner : K) :
    ∀ (as bs : List (Polynomial K)) (first second : K),
      as.length = bs.length →
      (List.zipWith (fun a b => a + b) as bs).foldl
          (fun value a => value * outer + a.eval inner) (first + second) =
        as.foldl (fun value a => value * outer + a.eval inner) first +
          bs.foldl (fun value a => value * outer + a.eval inner) second
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      exact Nat.noConfusion equal
  | _ :: _, [], _, _, equal => by
      exact Nat.noConfusion equal
  | a :: as, b :: bs, first, second, equal => by
      have tailsEqual : as.length = bs.length := Nat.succ.inj equal
      simp only [List.zipWith_cons_cons, List.foldl_cons, eval_add]
      rw [show (first + second) * outer + (a.eval inner + b.eval inner) =
          (first * outer + a.eval inner) +
            (second * outer + b.eval inner) by ring1]
      exact eval_foldl_zipWith_add outer inner as bs
        (first * outer + a.eval inner) (second * outer + b.eval inner) tailsEqual

@[simp] theorem eval_add (p q : Bivariate K) (outer inner : K) :
    eval (add p q) outer inner = eval p outer inner + eval q outer inner := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have pLe : p.coeffs.length ≤ n := le_max_left _ _
  have qLe : q.coeffs.length ≤ n := le_max_right _ _
  have pLength : ps.length = n := by
    simp [ps, padLeft, Nat.sub_add_cancel pLe]
  have qLength : qs.length = n := by
    simp [qs, padLeft, Nat.sub_add_cancel qLe]
  change (List.zipWith (fun a b => a + b) ps qs).foldl
      (fun value a => value * outer + a.eval inner) 0 = _
  rw [show (0 : K) = 0 + 0 by ring1,
    eval_foldl_zipWith_add outer inner ps qs 0 0 (pLength.trans qLength.symm)]
  dsimp only [ps, qs, padLeft]
  rw [eval_foldl_replicate_zero, eval_foldl_replicate_zero]
  rfl

private theorem eval_foldl_map_neg (outer inner : K) :
    ∀ (coefficients : List (Polynomial K)) (accumulator : K),
      (coefficients.map (-·)).foldl
          (fun value a => value * outer + a.eval inner) (-accumulator) =
        -coefficients.foldl
          (fun value a => value * outer + a.eval inner) accumulator
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.map_cons, List.foldl_cons, eval_neg]
      rw [show -accumulator * outer + -a.eval inner =
          -(accumulator * outer + a.eval inner) by ring1]
      exact eval_foldl_map_neg outer inner remaining
        (accumulator * outer + a.eval inner)

@[simp] theorem eval_neg (p : Bivariate K) (outer inner : K) :
    eval (neg p) outer inner = -eval p outer inner := by
  change (p.coeffs.map (-·)).foldl
      (fun value a => value * outer + a.eval inner) 0 =
    -p.coeffs.foldl (fun value a => value * outer + a.eval inner) 0
  simpa only [neg_zero] using
    eval_foldl_map_neg outer inner p.coeffs 0

@[simp] theorem eval_sub (p q : Bivariate K) (outer inner : K) :
    eval (sub p q) outer inner = eval p outer inner - eval q outer inner := by
  rw [sub, eval_add, eval_neg]
  ring1

private theorem eval_foldl_mul (q : Bivariate K) (outer inner : K) :
    ∀ (coefficients : List (Polynomial K)) (accumulator : Bivariate K),
      eval (coefficients.foldl
          (fun value a => add (shiftOuter value) (scaleInner a q))
          accumulator) outer inner =
        coefficients.foldl
          (fun value a => value * outer + a.eval inner * eval q outer inner)
          (eval accumulator outer inner)
  | [], _ => rfl
  | a :: remaining, accumulator => by
      simp only [List.foldl_cons]
      rw [eval_foldl_mul q outer inner remaining, eval_add,
        eval_shiftOuter, eval_scaleInner]

@[simp] theorem eval_mul (p q : Bivariate K) (outer inner : K) :
    eval (mul p q) outer inner = eval p outer inner * eval q outer inner := by
  rw [mul, eval_foldl_mul]
  have scaled : ∀ (coefficients : List (Polynomial K))
      (accumulator : K),
      coefficients.foldl
          (fun value a => value * outer + a.eval inner * eval q outer inner)
          (accumulator * eval q outer inner) =
        coefficients.foldl
          (fun value a => value * outer + a.eval inner) accumulator *
          eval q outer inner := by
    intro coefficients accumulator
    induction coefficients generalizing accumulator with
    | nil => rfl
    | cons a remaining inductionHypothesis =>
        simp only [List.foldl_cons]
        rw [show accumulator * eval q outer inner * outer +
            a.eval inner * eval q outer inner =
          (accumulator * outer + a.eval inner) * eval q outer inner by ring1,
          inductionHypothesis]
  change p.coeffs.foldl
      (fun value a => value * outer + a.eval inner * eval q outer inner) 0 =
    p.coeffs.foldl (fun value a => value * outer + a.eval inner) 0 *
      eval q outer inner
  have zeroMul : (0 : K) * eval q outer inner = 0 := zero_mul _
  simpa only [zeroMul] using scaled p.coeffs 0

/-! ## Gaussian coordinate construction -/

def coordinateStep (xVariable yVariable : Bivariate Coordinate)
    (state : Bivariate Coordinate × Bivariate Coordinate)
    (coefficient : Gaussian) :
    Bivariate Coordinate × Bivariate Coordinate :=
  (add (sub (mul state.1 xVariable) (mul state.2 yVariable))
      (constant coefficient.re),
    add (add (mul state.1 yVariable) (mul state.2 xVariable))
      (constant coefficient.im))

def coordinatePolynomials (p : GaussianPolynomial)
    (xVariable yVariable : Bivariate Coordinate) :
    Bivariate Coordinate × Bivariate Coordinate :=
  p.normalize.coeffs.foldl (coordinateStep xVariable yVariable) (zero, zero)

/-- `Y` is outer and `X` is inner. -/
def verticalCoordinates (p : GaussianPolynomial) :
    Bivariate Coordinate × Bivariate Coordinate :=
  coordinatePolynomials p innerX outerX

/-- `X` is outer and `Y` is inner. -/
def horizontalCoordinates (p : GaussianPolynomial) :
    Bivariate Coordinate × Bivariate Coordinate :=
  coordinatePolynomials p outerX innerX

private theorem eval_coordinateFold_from
    (xVariable yVariable : Bivariate Coordinate)
    (outer inner x y : Coordinate)
    (xEval : eval xVariable outer inner = x)
    (yEval : eval yVariable outer inner = y)
    (coefficients : List Gaussian)
    (real imag : Bivariate Coordinate) (z : Gaussian)
    (realEval : eval real outer inner = z.re)
    (imagEval : eval imag outer inner = z.im) :
    let result := coefficients.foldl
      (coordinateStep xVariable yVariable) (real, imag)
    eval result.1 outer inner =
        (coefficients.foldl
          (fun value coefficient => value * ⟨x, y⟩ + coefficient) z).re ∧
      eval result.2 outer inner =
        (coefficients.foldl
          (fun value coefficient => value * ⟨x, y⟩ + coefficient) z).im := by
  induction coefficients generalizing real imag z with
  | nil => exact ⟨realEval, imagEval⟩
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · simp only [eval_add, eval_sub, eval_mul,
          eval_constant, xEval, yEval, realEval, imagEval, mul_re, add_re]
      · simp only [eval_add, eval_mul, eval_constant,
          xEval, yEval, realEval, imagEval, mul_im, add_im]

theorem eval_verticalCoordinates (p : GaussianPolynomial) (x y : Coordinate) :
    eval (verticalCoordinates p).1 y x = (p.eval ⟨x, y⟩).re ∧
      eval (verticalCoordinates p).2 y x = (p.eval ⟨x, y⟩).im := by
  rw [← eval_normalize p ⟨x, y⟩]
  have evaluated := eval_coordinateFold_from innerX outerX y x x y
    (by simp) (by simp) p.normalize.coeffs zero zero 0 (by simp) (by simp)
  simpa only [verticalCoordinates, coordinatePolynomials, eval,
    RFAP.ComputablePolynomial.DensePolynomial.eval, evalCoeffs, zero_re,
    zero_im] using evaluated

theorem eval_horizontalCoordinates (p : GaussianPolynomial) (x y : Coordinate) :
    eval (horizontalCoordinates p).1 x y = (p.eval ⟨x, y⟩).re ∧
      eval (horizontalCoordinates p).2 x y = (p.eval ⟨x, y⟩).im := by
  rw [← eval_normalize p ⟨x, y⟩]
  have evaluated := eval_coordinateFold_from outerX innerX x y x y
    (by simp) (by simp) p.normalize.coeffs zero zero 0 (by simp) (by simp)
  simpa only [horizontalCoordinates, coordinatePolynomials, eval,
    RFAP.ComputablePolynomial.DensePolynomial.eval, evalCoeffs, zero_re,
    zero_im] using evaluated

/-! ## Finite specialization and outer normalization -/

/-- Evaluate every inner coefficient, leaving a dense polynomial in the outer
variable. -/
def atInner (inner : K) (p : Bivariate K) : Polynomial K :=
  ⟨p.coeffs.map (fun coefficient => coefficient.eval inner)⟩

omit [DecidableEq K] in
@[simp] theorem eval_atInner (p : Bivariate K) (outer inner : K) :
    (atInner inner p).eval outer = eval p outer inner := by
  have mapped : ∀ (coefficients : List (Polynomial K))
      (accumulator : K),
      (coefficients.map (fun coefficient => coefficient.eval inner)).foldl
          (fun value coefficient => value * outer + coefficient) accumulator =
        coefficients.foldl
          (fun value coefficient => value * outer + coefficient.eval inner)
          accumulator := by
    intro coefficients accumulator
    induction coefficients generalizing accumulator with
    | nil => rfl
    | cons coefficient remaining inductionHypothesis =>
        simp only [List.map_cons, List.foldl_cons]
        exact inductionHypothesis _
  exact mapped p.coeffs 0

/-- Remove representation-only zero outer coefficients. -/
def normalizeOuter (p : Bivariate K) : Bivariate K :=
  ⟨p.coeffs.dropWhile (fun coefficient => coefficient.isZero)⟩

private theorem eval_foldl_dropWhile_zero
    (coefficients : List (Polynomial K)) (outer inner : K) :
    (coefficients.dropWhile (fun coefficient => coefficient.isZero)).foldl
        (fun value coefficient => value * outer + coefficient.eval inner) 0 =
      coefficients.foldl
        (fun value coefficient => value * outer + coefficient.eval inner) 0 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      by_cases zeroCoefficient : coefficient.isZero = true
      · rw [List.dropWhile_cons_of_pos zeroCoefficient, List.foldl_cons,
          RFAP.ComputablePolynomial.DensePolynomial.eval_eq_zero_of_isZero
            zeroCoefficient]
        rw [show (0 : K) * outer + 0 = 0 by ring1]
        exact inductionHypothesis
      · rw [List.dropWhile_cons_of_neg zeroCoefficient]

@[simp] theorem eval_normalizeOuter (p : Bivariate K)
    (outer inner : K) :
    eval (normalizeOuter p) outer inner = eval p outer inner :=
  eval_foldl_dropWhile_zero p.coeffs outer inner

/-- The outer degree of the normalized finite coefficient list. -/
def outerNatDegree (p : Bivariate K) : Nat :=
  (normalizeOuter p).coeffs.length - 1

/-! ## Finite Laplace determinant and Sylvester output -/

def outerCoeff (p : Bivariate K) (n : Nat) : Polynomial K :=
  p.coeffs.reverse.getD n 0

def sylvester (f g : Bivariate K) (m n : Nat) :
    Matrix (Polynomial K) (m + n) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    QuotientFreeFin.addCases
    (fun left =>
      if (left : Nat) ≤ (row : Nat) ∧ (row : Nat) ≤ (left : Nat) + n
      then outerCoeff g ((row : Nat) - left) else 0)
    (fun right =>
      if (right : Nat) ≤ (row : Nat) ∧ (row : Nat) ≤ (right : Nat) + m
      then outerCoeff f ((row : Nat) - right) else 0) column

omit [RFAP.ExplicitField K] [DecidableEq K] in
/-- A displayed entry in the left Sylvester block, without identifying the
two branch functions passed to the finite index splitter. -/
theorem sylvester_left_apply (f g : Bivariate K) (m n : Nat)
    (row : Fin (m + n)) (column : Fin m) :
    sylvester f g m n row (Fin.castAdd n column) =
      if (column : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (column : Nat) + n then
        outerCoeff g ((row : Nat) - column)
      else 0 := by
  unfold sylvester
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    QuotientFreeFin.addCases_left]

omit [RFAP.ExplicitField K] [DecidableEq K] in
/-- A displayed entry in the right Sylvester block. -/
theorem sylvester_right_apply (f g : Bivariate K) (m n : Nat)
    (row : Fin (m + n)) (column : Fin n) :
    sylvester f g m n row (Fin.natAdd m column) =
      if (column : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (column : Nat) + m then
        outerCoeff f ((row : Nat) - column)
      else 0 := by
  unfold sylvester
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    QuotientFreeFin.addCases_right]

def skipIndex {n : Nat} (removed : Fin (n + 1)) (index : Fin n) :
    Fin (n + 1) :=
  if index.val < removed.val then
    ⟨index.val, index.isLt.trans (Nat.lt_succ_self n)⟩
  else ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩

def firstColumnMinor {n : Nat}
    (matrix : Matrix (Polynomial K) (n + 1))
    (row : Fin (n + 1)) : Matrix (Polynomial K) n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun minorRow column =>
    matrix (skipIndex row minorRow) column.succ

def scalarFirstColumnMinor {n : Nat}
    (matrix : Matrix K (n + 1))
    (row : Fin (n + 1)) : Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun minorRow column =>
    matrix (skipIndex row minorRow) column.succ

/-- Explicit determinant over dense coordinate polynomials. -/
def determinant : (n : Nat) →
    Matrix (Polynomial K) n → Polynomial K
  | 0, _ => RFAP.ComputablePolynomial.DensePolynomial.constant 1
  | n + 1, matrix =>
      (List.ofFn fun row : Fin (n + 1) =>
        scale ((-1 : K) ^ (row : Nat))
          (matrix row 0 * determinant n (firstColumnMinor matrix row))).foldl
        (fun a b => a + b) 0

/-- The same recursion after evaluating every matrix entry. -/
def scalarDeterminant : (n : Nat) →
    Matrix K n → K
  | 0, _ => 1
  | n + 1, matrix =>
      (List.ofFn fun row : Fin (n + 1) =>
        (-1 : K) ^ (row : Nat) * matrix row 0 *
          scalarDeterminant n (scalarFirstColumnMinor matrix row)).foldl
        (fun a b => a + b) 0

omit [DecidableEq K] in
/-- Entrywise equality is sufficient for equality of the recursively
computed scalar determinants; no equality of matrix-valued functions is
needed. -/
theorem scalarDeterminant_congr : ∀ {n : Nat} (left right : Matrix K n),
    (∀ row column, left row column = right row column) →
      scalarDeterminant n left = scalarDeterminant n right
  | 0, left, right, equal => rfl
  | n + 1, left, right, equal => by
      rw [scalarDeterminant, scalarDeterminant]
      apply congrArg (fun values : List K =>
        values.foldl (fun a b => a + b) 0)
      apply QuotientFreeList.ofFn_congr
      intro row
      have minorEqual :
          scalarDeterminant n (scalarFirstColumnMinor left row) =
            scalarDeterminant n (scalarFirstColumnMinor right row) :=
        scalarDeterminant_congr _ _ (fun minorRow column => by
          simp only [scalarFirstColumnMinor,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
          exact equal (skipIndex row minorRow) column.succ)
      calc
        (-1 : K) ^ (row : Nat) * left row 0 *
              scalarDeterminant n (scalarFirstColumnMinor left row) =
            (-1 : K) ^ (row : Nat) * right row 0 *
              scalarDeterminant n (scalarFirstColumnMinor left row) :=
          congrArg (fun value =>
            (-1 : K) ^ (row : Nat) * value *
              scalarDeterminant n (scalarFirstColumnMinor left row))
            (equal row 0)
        _ = (-1 : K) ^ (row : Nat) * right row 0 *
              scalarDeterminant n (scalarFirstColumnMinor right row) :=
          congrArg (fun value =>
            (-1 : K) ^ (row : Nat) * right row 0 * value) minorEqual

private theorem eval_foldl_add (t : K)
    (polynomials : List (Polynomial K)) (accumulator : Polynomial K) :
    (polynomials.foldl (fun a b => a + b) accumulator).eval t =
      (polynomials.map (fun p => p.eval t)).foldl
        (fun a b => a + b) (accumulator.eval t) := by
  induction polynomials generalizing accumulator with
  | nil => rfl
  | cons p remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      rw [inductionHypothesis,
        RFAP.ComputablePolynomial.DensePolynomial.eval_add]

theorem eval_determinant (t : K) : ∀ (n : Nat)
    (matrix : Matrix (Polynomial K) n),
    (determinant n matrix).eval t =
      scalarDeterminant n
        (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
          (matrix row column).eval t)
  | 0, _ => by
      change (RFAP.ComputablePolynomial.DensePolynomial.constant 1).eval t = 1
      exact RFAP.ComputablePolynomial.DensePolynomial.eval_constant 1 t
  | n + 1, matrix => by
      rw [determinant, scalarDeterminant, eval_foldl_add,
        RFAP.ComputablePolynomial.DensePolynomial.eval_zero,
        QuotientFreeList.map_ofFn]
      apply congrArg (fun values : List K =>
        values.foldl (fun a b => a + b) 0)
      apply QuotientFreeList.ofFn_congr
      intro row
      simp only [Function.comp_apply,
        RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
      change
        (scale ((-1 : K) ^ (row : Nat))
            (matrix row 0 * determinant n
              (firstColumnMinor matrix row))).eval t =
          (-1 : K) ^ (row : Nat) * (matrix row 0).eval t *
            scalarDeterminant n
              (scalarFirstColumnMinor
                (RFAP.ConstructiveFiniteMatrix.matrixOfFn
                  fun matrixRow column =>
                    (matrix matrixRow column).eval t) row)
      rw [RFAP.ComputablePolynomial.DensePolynomial.eval_scale,
        RFAP.ComputablePolynomial.DensePolynomial.eval_mul]
      rw [eval_determinant t n (firstColumnMinor matrix row)]
      have minorDeterminantEqual := scalarDeterminant_congr
        (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun minorRow column =>
          (firstColumnMinor matrix row minorRow column).eval t)
        (scalarFirstColumnMinor
          (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun matrixRow column =>
            (matrix matrixRow column).eval t) row)
        (fun minorRow column => by
          rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
            firstColumnMinor, scalarFirstColumnMinor,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply])
      rw [minorDeterminantEqual]
      ring1

def resultant (f g : Bivariate K) (m n : Nat) : Polynomial K :=
  determinant (m + n) (sylvester f g m n)

theorem eval_resultant (f g : Bivariate K) (m n : Nat) (t : K) :
    (resultant f g m n).eval t =
      scalarDeterminant (m + n)
        (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
          (sylvester f g m n row column).eval t) :=
  eval_determinant t (m + n) (sylvester f g m n)

end RFAP.ConstructiveBivariate
