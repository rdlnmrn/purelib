import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ExplicitField
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic

/-!
# Executable dense polynomials and finite Euclidean division

Mathlib's sparse `Polynomial` arithmetic is intended for specifications at the
representation level.  The FTA algorithms therefore use this separate dense
coefficient program.  Coefficients are stored highest-degree first; leading
zeros are removed by a finite `dropWhile` pass.
-/

namespace RFAP.ComputablePolynomial

/-- A finite high-to-low coefficient list. -/
structure DensePolynomial (K : Type*) where
  coeffs : List K
deriving DecidableEq, Repr

namespace DensePolynomial

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

omit [DecidableEq K] in
theorem mul_ne_zero_direct {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := RFAP.ExplicitField.mul_ne_zero ha hb

omit [DecidableEq K] in
theorem div_ne_zero_direct {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b ≠ 0 := RFAP.ExplicitField.div_ne_zero ha hb

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[ext] theorem ext {p q : DensePolynomial K} (h : p.coeffs = q.coeffs) : p = q := by
  cases p
  cases q
  simpa using h

instance : Zero (DensePolynomial K) := ⟨⟨[]⟩⟩

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[simp] theorem zero_coeffs : (0 : DensePolynomial K).coeffs = [] := rfl

/-- Constant dense polynomial. -/
def constant (a : K) : DensePolynomial K := ⟨[a]⟩

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[simp] theorem constant_coeffs (a : K) : (constant a).coeffs = [a] := rfl

/-- Remove representation-only leading zero coefficients. -/
def normalize (p : DensePolynomial K) : DensePolynomial K :=
  ⟨p.coeffs.dropWhile (· = 0)⟩

@[simp] theorem normalize_normalize (p : DensePolynomial K) :
    p.normalize.normalize = p.normalize := by
  apply ext
  change (p.coeffs.dropWhile (· = 0)).dropWhile (· = 0) =
    p.coeffs.dropWhile (· = 0)
  induction p.coeffs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · simp [List.dropWhile, ha, ih]
      · simp [List.dropWhile, ha]

@[simp] theorem normalize_zero : normalize (0 : DensePolynomial K) = 0 := rfl

theorem normalize_constant_of_ne {a : K} (ha : a ≠ 0) :
    normalize (constant a) = constant a := by
  apply ext
  simp [normalize, constant, ha]

@[simp] theorem normalize_constant_zero :
    normalize (constant (0 : K)) = 0 := by
  apply ext
  simp [normalize, constant]

theorem normalize_linear_of_leading_ne_zero {leading trailing : K}
    (leadingNonzero : leading ≠ 0) :
    normalize ⟨[leading, trailing]⟩ = ⟨[leading, trailing]⟩ := by
  apply ext
  simp [normalize, leadingNonzero]

@[simp] theorem normalize_coeffs (p : DensePolynomial K) :
    p.normalize.coeffs = p.coeffs.dropWhile (· = 0) := rfl

/-- Exact zero test on normalized finite coefficients. -/
def isZero (p : DensePolynomial K) : Bool := p.normalize.coeffs.isEmpty

@[simp] theorem isZero_zero : isZero (0 : DensePolynomial K) = true := rfl

@[simp] theorem isZero_normalize (p : DensePolynomial K) :
    p.normalize.isZero = p.isZero := by
  simp [isZero]

/-- Number of nonzero degree slots; zero has degree count zero and a degree
`d` polynomial has degree count `d+1`. -/
def degreeCount (p : DensePolynomial K) : ℕ := p.normalize.coeffs.length

theorem degreeCount_eq_zero_of_isZero {p : DensePolynomial K} (hp : p.isZero = true) :
    p.degreeCount = 0 := by
  simpa [degreeCount, isZero] using hp

theorem isZero_true_of_degreeCount_eq_zero {p : DensePolynomial K}
    (count : p.degreeCount = 0) : p.isZero = true := by
  simpa [degreeCount, isZero] using count

theorem normalize_eq_zero_of_isZero {p : DensePolynomial K}
    (hp : p.isZero = true) : p.normalize = 0 := by
  apply ext
  change p.normalize.coeffs = []
  simpa [isZero] using hp

theorem degreeCount_pos_of_isZero_false {p : DensePolynomial K} (hp : p.isZero = false) :
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

@[simp] theorem degreeCount_normalize (p : DensePolynomial K) :
    p.normalize.degreeCount = p.degreeCount := by
  simp [degreeCount]

/-- Natural degree, with the conventional junk value zero for the zero polynomial. -/
def natDegree (p : DensePolynomial K) : ℕ := p.degreeCount - 1

@[simp] theorem natDegree_normalize (p : DensePolynomial K) :
    p.normalize.natDegree = p.natDegree := by
  simp [natDegree]

theorem natDegree_add_one_eq_degreeCount {p : DensePolynomial K} (hp : p.isZero = false) :
    p.natDegree + 1 = p.degreeCount := by
  dsimp only [natDegree]
  have := degreeCount_pos_of_isZero_false hp
  omega

/-- Leading coefficient, or zero for the zero polynomial. -/
def leadingCoeff (p : DensePolynomial K) : K := p.normalize.coeffs.headD 0

private theorem dropWhile_headD_ne_zero (cs : List K)
    (h : (cs.dropWhile (· = 0)).isEmpty = false) :
    (cs.dropWhile (· = 0)).headD 0 ≠ 0 := by
  induction cs with
  | nil => simp at h
  | cons a as ih =>
      by_cases ha : a = 0
      · rw [List.dropWhile_cons_of_pos (by simp [ha])] at h ⊢
        exact ih h
      · rw [List.dropWhile_cons_of_neg (by simp [ha])]
        simpa using ha

theorem leadingCoeff_ne_zero {p : DensePolynomial K} (hp : p.isZero = false) :
    p.leadingCoeff ≠ 0 := by
  change (p.coeffs.dropWhile (· = 0)).headD 0 ≠ 0
  apply dropWhile_headD_ne_zero
  exact hp

/-- Exact finite normalized coefficient shape of a represented nonzero
polynomial. -/
theorem normalized_coeffs_shape {p : DensePolynomial K}
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
        simp only [List.headD_cons]
      · change tail.length = p.normalize.coeffs.length - 1
        rw [coefficients]
        simp

/-- A represented nonzero polynomial of natural degree zero normalizes to its
single displayed leading coefficient.  The proof inspects the finite list;
it does not identify polynomials from values on a carrier. -/
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
      simp only [List.length_nil] at count
      exact (Nat.succ_ne_zero 0 count).elim
  | cons leading tail =>
      cases tail with
      | nil =>
          apply ext
          change p.normalize.coeffs = [p.leadingCoeff]
          rw [coefficients]
          unfold leadingCoeff
          rw [coefficients]
          simp only [List.headD_cons]
      | cons next remaining =>
          change 0 + 1 = p.normalize.coeffs.length at count
          rw [coefficients] at count
          simp only [List.length_cons] at count
          have impossible : 0 = remaining.length + 1 := Nat.succ.inj count
          exact Nat.noConfusion impossible

/-- Horner evaluation is a recursion over the finite coefficient list. -/
def evalCoeffs (x : K) (cs : List K) : K :=
  cs.foldl (fun acc a => acc * x + a) 0

def eval (p : DensePolynomial K) (x : K) : K := evalCoeffs x p.coeffs

omit [DecidableEq K] in
@[simp] theorem eval_constant (a x : K) : (constant a).eval x = a := by
  simp [constant, eval, evalCoeffs]

omit [DecidableEq K] in
@[simp] theorem eval_zero (x : K) : (0 : DensePolynomial K).eval x = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem evalCoeffs_nil (x : K) : evalCoeffs x [] = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem evalCoeffs_cons (x a : K) (as : List K) :
    evalCoeffs x (a :: as) = as.foldl (fun acc b => acc * x + b) a := by
  simp [evalCoeffs]

omit [DecidableEq K] in
theorem evalCoeffs_cons_zero (x : K) (as : List K) :
    evalCoeffs x (0 :: as) = evalCoeffs x as := by
  simp [evalCoeffs]

omit [DecidableEq K] in
private theorem foldl_horner_expansion (x : K) :
    ∀ (coefficients : List K) (accumulator : K),
      coefficients.foldl (fun value coefficient => value * x + coefficient)
          accumulator =
        accumulator * x ^ coefficients.length +
          evalCoeffs x coefficients
  | [], accumulator => by
      simp [evalCoeffs]
  | coefficient :: coefficients, accumulator => by
      rw [List.foldl_cons,
        foldl_horner_expansion x coefficients
          (accumulator * x + coefficient)]
      have coefficientExpansion :
          evalCoeffs x (coefficient :: coefficients) =
            coefficient * x ^ coefficients.length +
              evalCoeffs x coefficients := by
        unfold evalCoeffs
        simp only [List.foldl_cons, zero_mul, zero_add]
        exact foldl_horner_expansion x coefficients coefficient
      rw [coefficientExpansion]
      simp only [List.length_cons, pow_succ]
      ring1

omit [DecidableEq K] in
/-- Exact finite monomial expansion of one high-to-low Horner list step. -/
theorem evalCoeffs_cons_expansion (x a : K) (as : List K) :
    evalCoeffs x (a :: as) =
      a * x ^ as.length + evalCoeffs x as := by
  unfold evalCoeffs
  simp only [List.foldl_cons, zero_mul, zero_add]
  exact foldl_horner_expansion x as a

theorem evalCoeffs_dropWhile_zero (x : K) (cs : List K) :
    evalCoeffs x (cs.dropWhile (· = 0)) = evalCoeffs x cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        rw [List.dropWhile_cons_of_pos (by simp), evalCoeffs_cons_zero]
        exact ih
      · rw [List.dropWhile_cons_of_neg (by simpa using ha)]

@[simp] theorem eval_normalize (p : DensePolynomial K) (x : K) :
    p.normalize.eval x = p.eval x := evalCoeffs_dropWhile_zero x p.coeffs

/-- Left zero padding aligns two high-to-low coefficient lists. -/
def padLeft (n : ℕ) (cs : List K) : List K := List.replicate n 0 ++ cs

omit [DecidableEq K] in
theorem evalCoeffs_replicate_zero_append (x : K) (n : ℕ) (cs : List K) :
    evalCoeffs x (List.replicate n 0 ++ cs) = evalCoeffs x cs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, evalCoeffs_cons_zero, ih]

omit [DecidableEq K] in
private theorem foldl_zipWith_add (x : K) :
    ∀ (as bs : List K) (accA accB : K), as.length = bs.length →
      (List.zipWith (· + ·) as bs).foldl (fun acc a => acc * x + a) (accA + accB) =
        as.foldl (fun acc a => acc * x + a) accA +
          bs.foldl (fun acc b => acc * x + b) accB
  | [], [], accA, accB, _ => rfl
  | [], _ :: _, _, _, h => by exact Nat.noConfusion h
  | _ :: _, [], _, _, h => by exact Nat.noConfusion h
  | a :: as, b :: bs, accA, accB, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.zipWith_cons_cons, List.foldl_cons]
      have hacc : (accA + accB) * x + (a + b) =
          (accA * x + a) + (accB * x + b) := by ring1
      rw [hacc]
      exact foldl_zipWith_add x as bs (accA * x + a) (accB * x + b) h

omit [DecidableEq K] in
theorem evalCoeffs_zipWith_add (x : K) (as bs : List K) (h : as.length = bs.length) :
    evalCoeffs x (List.zipWith (· + ·) as bs) =
      evalCoeffs x as + evalCoeffs x bs := by
  simpa only [evalCoeffs, zero_add] using foldl_zipWith_add x as bs 0 0 h

/-- Coefficientwise addition after finite left-padding. -/
def add (p q : DensePolynomial K) : DensePolynomial K :=
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  normalize ⟨List.zipWith (· + ·) ps qs⟩

instance : Add (DensePolynomial K) := ⟨add⟩

@[simp] theorem normalize_add (p q : DensePolynomial K) :
    (p + q).normalize = p + q := by
  exact normalize_normalize _

omit [DecidableEq K] in
private theorem zipWith_add_comm : ∀ first second : List K,
    List.zipWith (· + ·) first second =
      List.zipWith (· + ·) second first
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | left :: leftTail, right :: rightTail => by
      simp only [List.zipWith_cons_cons]
      rw [_root_.add_comm left right,
        zipWith_add_comm leftTail rightTail]

/-- Coefficientwise addition is commutative by a direct finite-list proof. -/
theorem add_comm_direct (p q : DensePolynomial K) : p + q = q + p := by
  apply ext
  change (add p q).coeffs = (add q p).coeffs
  simp only [add]
  rw [max_comm]
  change (List.zipWith (· + ·)
      (padLeft (max q.coeffs.length p.coeffs.length - p.coeffs.length) p.coeffs)
      (padLeft (max q.coeffs.length p.coeffs.length - q.coeffs.length) q.coeffs)).dropWhile
        (· = 0) =
    (List.zipWith (· + ·)
      (padLeft (max q.coeffs.length p.coeffs.length - q.coeffs.length) q.coeffs)
      (padLeft (max q.coeffs.length p.coeffs.length - p.coeffs.length) p.coeffs)).dropWhile
        (· = 0)
  exact congrArg
    (fun coefficients : List K =>
      coefficients.dropWhile (fun coefficient => decide (coefficient = 0)))
    (zipWith_add_comm _ _)

/-- Adding the represented zero constant changes only normalization. -/
@[simp] theorem add_constant_zero (p : DensePolynomial K) :
    p + constant 0 = p.normalize := by
  cases p with
  | mk coefficients =>
      apply ext
      change (add ⟨coefficients⟩ (constant 0)).coeffs =
        (normalize ⟨coefficients⟩).coeffs
      cases coefficients with
      | nil => simp [add, padLeft, normalize, constant]
      | cons a as =>
          simp only [add, padLeft, normalize, constant,
            List.length_cons, List.length_nil]
          have maximum : max (as.length + 1) (0 + 1) = as.length + 1 := by
            exact max_eq_left
              (Nat.succ_le_succ (Nat.zero_le as.length))
          have selfSub : as.length + 1 - (as.length + 1) = 0 :=
            Nat.sub_self _
          have oneSub : as.length + 1 - (0 + 1) = as.length := by
            exact Nat.add_sub_cancel as.length 1
          simp only [maximum, selfSub, oneSub, List.replicate_zero,
            List.nil_append]
          have zipZeros : ∀ (head : K) (tail : List K),
              List.zipWith (· + ·) (head :: tail)
                (List.replicate tail.length 0 ++ [0]) = head :: tail := by
            intro head tail
            induction tail generalizing head with
            | nil => simp
            | cons value values inductionHypothesis =>
                simp only [List.length_cons, List.replicate_succ,
                  List.cons_append, List.zipWith_cons_cons, add_zero]
                rw [inductionHypothesis]
          rw [zipZeros a as]

theorem constant_add_linear {leading : K} (trailing : K)
    (leadingNonzero : leading ≠ 0) :
    constant trailing + ⟨[leading, 0]⟩ = ⟨[leading, trailing]⟩ := by
  apply ext
  change (add (constant trailing) ⟨[leading, 0]⟩).coeffs =
    [leading, trailing]
  simp [add, padLeft, normalize, constant, leadingNonzero]

/-- Adding a constant to an exact nonconstant linear coefficient list only
changes its trailing coefficient. -/
theorem linear_add_constant {leading : K} (trailing constantTerm : K)
    (leadingNonzero : leading ≠ 0) :
    ⟨[leading, trailing]⟩ + constant constantTerm =
      ⟨[leading, trailing + constantTerm]⟩ := by
  apply ext
  change (add ⟨[leading, trailing]⟩ (constant constantTerm)).coeffs =
    [leading, trailing + constantTerm]
  simp [add, padLeft, normalize, constant, leadingNonzero]

@[simp] theorem eval_add (p q : DensePolynomial K) (x : K) :
    (p + q).eval x = p.eval x + q.eval x := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := le_max_left _ _
  have hq : q.coeffs.length ≤ n := le_max_right _ _
  have hps : ps.length = n := by
    dsimp [ps, padLeft]
    simp [Nat.sub_add_cancel hp]
  have hqs : qs.length = n := by
    dsimp [qs, padLeft]
    simp [Nat.sub_add_cancel hq]
  change (normalize ⟨List.zipWith (· + ·) ps qs⟩).eval x = _
  rw [eval_normalize]
  change evalCoeffs x (List.zipWith (· + ·) ps qs) = _
  rw [evalCoeffs_zipWith_add x ps qs (hps.trans hqs.symm)]
  dsimp only [eval, ps, qs, padLeft]
  rw [evalCoeffs_replicate_zero_append, evalCoeffs_replicate_zero_append]

def neg (p : DensePolynomial K) : DensePolynomial K :=
  normalize ⟨p.coeffs.map (-·)⟩

instance : Neg (DensePolynomial K) := ⟨neg⟩

private theorem dropWhile_map_neg (cs : List K) :
    (cs.map (-·)).dropWhile (· = 0) =
      (cs.dropWhile (· = 0)).map (-·) := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        simpa using ih
      · have hneg : -a ≠ 0 := neg_ne_zero.mpr ha
        simp [List.dropWhile_cons_of_neg, ha, hneg]

@[simp] theorem neg_coeffs (p : DensePolynomial K) :
    (-p).coeffs = p.normalize.coeffs.map (-·) := by
  exact dropWhile_map_neg p.coeffs

@[simp] theorem normalize_neg (p : DensePolynomial K) :
    (-p).normalize = -p := by
  exact normalize_normalize ⟨p.coeffs.map (-·)⟩

@[simp] theorem neg_normalize (p : DensePolynomial K) :
    -p.normalize = -p := by
  apply ext
  simp

omit [DecidableEq K] in
private theorem map_neg_neg : ∀ coefficients : List K,
    (coefficients.map (-·)).map (-·) = coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      rw [List.map_cons, List.map_cons, neg_neg,
        map_neg_neg coefficients]

@[simp] theorem neg_neg (p : DensePolynomial K) : - -p = p.normalize := by
  apply ext
  rw [neg_coeffs, normalize_neg, neg_coeffs]
  exact map_neg_neg p.normalize.coeffs

@[simp] theorem isZero_neg (p : DensePolynomial K) : (-p).isZero = p.isZero := by
  simp [isZero]

@[simp] theorem degreeCount_neg (p : DensePolynomial K) :
    (-p).degreeCount = p.degreeCount := by
  simp [degreeCount]

@[simp] theorem natDegree_neg (p : DensePolynomial K) :
    (-p).natDegree = p.natDegree := by
  simp [natDegree]

@[simp] theorem leadingCoeff_neg (p : DensePolynomial K) :
    (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leadingCoeff, normalize_neg, neg_coeffs]
  change (p.normalize.coeffs.map (-·)).headD 0 = -p.normalize.coeffs.headD 0
  cases p.normalize.coeffs <;> simp

omit [DecidableEq K] in
private theorem foldl_map_neg (x : K) : ∀ (cs : List K) (acc : K),
    (cs.map (-·)).foldl (fun value a => value * x + a) (-acc) =
      -cs.foldl (fun value a => value * x + a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      have hacc : -acc * x + -a = -(acc * x + a) := by ring1
      rw [hacc]
      exact foldl_map_neg x as (acc * x + a)

@[simp] theorem eval_neg (p : DensePolynomial K) (x : K) :
    (-p).eval x = -p.eval x := by
  rw [show -p = normalize ⟨p.coeffs.map (-·)⟩ from rfl, eval_normalize]
  dsimp only [eval, evalCoeffs]
  simpa only [neg_zero] using foldl_map_neg x p.coeffs 0

def sub (p q : DensePolynomial K) : DensePolynomial K := p + -q

instance : Sub (DensePolynomial K) := ⟨sub⟩

omit [DecidableEq K] in
private theorem padLeft_map_neg (n : Nat) (coefficients : List K) :
    padLeft n (coefficients.map (-·)) =
      (padLeft n coefficients).map (-·) := by
  simp only [padLeft, List.map_append, List.map_replicate, neg_zero]

omit [DecidableEq K] in
private theorem zipWith_neg_add : ∀ first second : List K,
    List.zipWith (· + ·) (first.map (-·)) second =
      (List.zipWith (· + ·) first (second.map (-·))).map (-·)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | first :: restFirst, second :: restSecond => by
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [zipWith_neg_add restFirst restSecond]
      exact congrArg₂ List.cons (by ring1) rfl

private theorem dropWhile_zero_idempotent (coefficients : List K) :
    (coefficients.dropWhile (· = 0)).dropWhile (· = 0) =
      coefficients.dropWhile (· = 0) := by
  have normalized := congrArg DensePolynomial.coeffs
    (normalize_normalize (K := K) ⟨coefficients⟩)
  exact normalized

@[simp] theorem normalize_sub (p q : DensePolynomial K) :
    (p - q).normalize = p - q := by
  exact normalize_add p (-q)

@[simp] theorem eval_sub (p q : DensePolynomial K) (x : K) :
    (p - q).eval x = p.eval x - q.eval x := by
  change (p + -q).eval x = _
  rw [eval_add, eval_neg, sub_eq_add_neg]

omit [DecidableEq K] in
private theorem zipWith_trailing_cancel (second c : K) :
    ∀ rest : List K,
      List.zipWith (· + ·) (List.replicate rest.length 0 ++ [c])
          (List.zipWith (· + ·) (second :: rest)
            (List.replicate rest.length 0 ++ [-c])) =
        second :: rest := by
  intro rest
  induction rest generalizing second with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.nil_append,
        List.zipWith]
      apply congrArg (fun value : K => [value])
      ring1
  | cons next rest inductionHypothesis =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, zero_add]
      rw [inductionHypothesis next, add_zero]

/-- Adding back a nonzero constant after subtracting it restores the exact
finite normalized coefficient list of a positive-degree polynomial. -/
theorem constant_add_sub_constant_of_normalized
    {p : DensePolynomial K} {c : K}
    (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false)
    (degreePositive : 0 < p.natDegree)
    (cNonzero : c ≠ 0) :
    constant c + (p - constant c) = p := by
  obtain ⟨tail, coefficients, tailLength⟩ := normalized_coeffs_shape pNonzero
  have leadingNonzero := leadingCoeff_ne_zero pNonzero
  rw [pNormalized] at coefficients
  cases tail with
  | nil =>
      simp only [List.length_nil] at tailLength
      rw [← tailLength] at degreePositive
      exact (Nat.not_lt_zero 0 degreePositive).elim
  | cons trailing rest =>
      have pShape : p = ⟨p.leadingCoeff :: trailing :: rest⟩ :=
        ext coefficients
      rw [pShape] at ⊢
      have negConstantCoeffs : (neg (constant c)).coeffs = [-c] := by
        simp [neg, normalize, constant, cNonzero]
      have negConstant : neg (constant c) = ⟨[-c]⟩ :=
        ext negConstantCoeffs
      let tailDifference := List.zipWith (· + ·) (trailing :: rest)
        (List.replicate rest.length 0 ++ [-c])
      have tailDifferenceLength : tailDifference.length = rest.length + 1 := by
        dsimp only [tailDifference]
        rw [List.length_zipWith, List.length_cons, List.length_append,
          List.length_replicate, List.length_singleton]
        simp only [min_self]
      let difference := add ⟨p.leadingCoeff :: trailing :: rest⟩
        (neg (constant c))
      have differenceCoeffs : difference.coeffs =
          p.leadingCoeff :: tailDifference := by
        dsimp only [difference]
        rw [negConstant]
        simp only [add, List.length_cons, List.length_nil]
        have maximum : max (rest.length + 1 + 1) 1 =
            rest.length + 1 + 1 :=
          max_eq_left (Nat.succ_le_succ (Nat.zero_le (rest.length + 1)))
        have padding : rest.length + 1 + 1 - 1 = rest.length + 1 := by
          exact Nat.add_sub_cancel (rest.length + 1) 1
        simp only [maximum, Nat.sub_self, padding, padLeft,
          List.replicate_zero, List.nil_append]
        rw [List.replicate_succ, List.cons_append,
          List.zipWith_cons_cons, add_zero]
        change (p.leadingCoeff ::
          List.zipWith (· + ·) (trailing :: rest)
            (List.replicate rest.length 0 ++ [-c])).dropWhile (· = 0) = _
        rw [List.dropWhile_cons_of_neg (by simpa using leadingNonzero)]
      have differenceShape : difference =
          ⟨p.leadingCoeff :: tailDifference⟩ := ext differenceCoeffs
      apply ext
      change (add (constant c) difference).coeffs = _
      rw [differenceShape]
      simp only [add, constant, List.length_cons, List.length_nil,
        tailDifferenceLength]
      have maximum : max 1 (rest.length + 1 + 1) =
          rest.length + 1 + 1 :=
        max_eq_right (Nat.succ_le_succ (Nat.zero_le (rest.length + 1)))
      have padding : rest.length + 1 + 1 - 1 = rest.length + 1 := by
        exact Nat.add_sub_cancel (rest.length + 1) 1
      simp only [maximum, Nat.sub_self, padding, padLeft,
        List.replicate_zero, List.nil_append]
      rw [List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, zero_add]
      change (p.leadingCoeff ::
        List.zipWith (· + ·) (List.replicate rest.length 0 ++ [c])
          tailDifference).dropWhile (· = 0) = _
      rw [List.dropWhile_cons_of_neg (by simpa using leadingNonzero)]
      apply congrArg (List.cons p.leadingCoeff)
      dsimp only [tailDifference]
      exact zipWith_trailing_cancel trailing c rest

omit [DecidableEq K] in
private theorem zipWith_two_trailing_cancel (s t : K) :
  ∀ coefficients : List K, 2 ≤ coefficients.length →
      List.zipWith (· + ·)
          (List.replicate (coefficients.length - 2) 0 ++ [s, t])
          (List.zipWith (· + ·) coefficients
            (List.replicate (coefficients.length - 2) 0 ++ [-s, -t])) =
        coefficients
  | [], length => by simp at length
  | _ :: [], length => by simp at length
  | first :: second :: rest, _ => by
      cases rest with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.replicate_zero, List.nil_append,
            List.zipWith_cons_cons, List.zipWith]
          apply congrArg₂ List.cons (by ring1)
          apply congrArg₂ List.cons (by ring1) rfl
      | cons third remaining =>
          have inductionHypothesis := zipWith_two_trailing_cancel s t
            (second :: third :: remaining) (by simp)
          have exponent :
              (first :: second :: third :: remaining).length - 2 =
                ((second :: third :: remaining).length - 2) + 1 := by
            simp only [List.length_cons]
            omega
          rw [exponent, List.replicate_succ]
          change List.zipWith (· + ·)
              (0 :: (List.replicate
                ((second :: third :: remaining).length - 2) 0 ++ [s, t]))
              (List.zipWith (· + ·) (first :: second :: third :: remaining)
                (0 :: (List.replicate
                  ((second :: third :: remaining).length - 2) 0 ++
                    [-s, -t]))) =
            first :: second :: third :: remaining
          rw [List.zipWith_cons_cons, List.zipWith_cons_cons,
            add_zero, zero_add, inductionHypothesis]

/-- Adding back an exact nonzero linear coefficient list after subtracting it
restores any normalized polynomial of degree at least two.  The proof scans
only the displayed finite lists. -/
theorem linear_add_sub_linear_of_normalized
    {p : DensePolynomial K} {s t : K}
    (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (sNonzero : s ≠ 0) :
    ⟨[s, t]⟩ + (p - ⟨[s, t]⟩) = p := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    normalized_coeffs_shape pNonzero
  have leadingNonzero := leadingCoeff_ne_zero pNonzero
  rw [pNormalized] at coefficients
  have tailLong : 2 ≤ tail.length := by
    rw [tailLength]
    exact degreeAtLeastTwo
  have pShape : p = ⟨p.leadingCoeff :: tail⟩ := ext coefficients
  rw [pShape] at ⊢
  have negLinear : neg ⟨[s, t]⟩ = ⟨[-s, -t]⟩ := by
    apply ext
    change (normalize ⟨[-s, -t]⟩).coeffs = [-s, -t]
    rw [normalize_linear_of_leading_ne_zero
      (neg_ne_zero.mpr sNonzero)]
  let tailDifference := List.zipWith (· + ·) tail
    (List.replicate (tail.length - 2) 0 ++ [-s, -t])
  have tailDifferenceLength : tailDifference.length = tail.length := by
    dsimp only [tailDifference]
    rw [List.length_zipWith, List.length_append, List.length_replicate]
    simp only [List.length_cons, List.length_nil]
    omega
  let difference := add ⟨p.leadingCoeff :: tail⟩ (neg ⟨[s, t]⟩)
  have differenceCoeffs : difference.coeffs =
      p.leadingCoeff :: tailDifference := by
    dsimp only [difference]
    rw [negLinear]
    simp only [add, List.length_cons]
    simp only [List.length_nil, Nat.zero_add, Nat.reduceAdd]
    have maximum : max (tail.length + 1) 2 = tail.length + 1 := by
      omega
    have firstPadding : tail.length + 1 - 2 = tail.length - 1 := by omega
    have paddingSucc : tail.length - 1 = (tail.length - 2) + 1 := by omega
    rw [maximum, Nat.sub_self, firstPadding]
    simp only [padLeft, List.replicate_zero, List.nil_append]
    rw [paddingSucc, List.replicate_succ, List.cons_append,
      List.zipWith_cons_cons, add_zero]
    change (p.leadingCoeff ::
      List.zipWith (· + ·) tail
        (List.replicate (tail.length - 2) 0 ++ [-s, -t])).dropWhile
          (· = 0) = _
    rw [List.dropWhile_cons_of_neg (by simpa using leadingNonzero)]
  have differenceShape : difference =
      ⟨p.leadingCoeff :: tailDifference⟩ := ext differenceCoeffs
  apply ext
  change (add ⟨[s, t]⟩ difference).coeffs = _
  rw [differenceShape]
  simp only [add, List.length_cons, tailDifferenceLength]
  simp only [List.length_nil, Nat.zero_add, Nat.reduceAdd]
  have maximum : max 2 (tail.length + 1) = tail.length + 1 := by omega
  have firstPadding : tail.length + 1 - 2 = tail.length - 1 := by omega
  have paddingSucc : tail.length - 1 = (tail.length - 2) + 1 := by omega
  rw [maximum, Nat.sub_self, firstPadding]
  simp only [padLeft, List.replicate_zero, List.nil_append]
  rw [paddingSucc, List.replicate_succ, List.cons_append,
    List.zipWith_cons_cons, zero_add]
  change (p.leadingCoeff ::
    List.zipWith (· + ·)
      (List.replicate (tail.length - 2) 0 ++ [s, t])
      tailDifference).dropWhile (· = 0) = _
  rw [List.dropWhile_cons_of_neg (by simpa using leadingNonzero)]
  apply congrArg (List.cons p.leadingCoeff)
  dsimp only [tailDifference]
  exact zipWith_two_trailing_cancel s t tail tailLong

/-- Simultaneous negation distributes through subtraction once both displayed
representatives are normalized. -/
theorem neg_sub_neg_of_normalized (p q : DensePolynomial K)
    (pNormalized : p.normalize = p) (qNormalized : q.normalize = q) :
    (-p) - (-q) = -(p - q) := by
  change add (-p) (-(-q)) = neg (add p (-q))
  rw [neg_neg, qNormalized]
  have pCoefficients : p.normalize.coeffs = p.coeffs := by
    exact congrArg DensePolynomial.coeffs pNormalized
  have qCoefficients : q.normalize.coeffs = q.coeffs := by
    exact congrArg DensePolynomial.coeffs qNormalized
  change p.coeffs.dropWhile (· = 0) = p.coeffs at pCoefficients
  change q.coeffs.dropWhile (· = 0) = q.coeffs at qCoefficients
  apply ext
  simp only [add, neg, normalize_coeffs, neg_coeffs,
    pCoefficients, qCoefficients, List.length_map]
  rw [padLeft_map_neg, padLeft_map_neg, zipWith_neg_add]
  rw [dropWhile_map_neg, dropWhile_map_neg,
    dropWhile_zero_idempotent]

/-- Scalar multiplication of every coefficient. -/
def scale (c : K) (p : DensePolynomial K) : DensePolynomial K :=
  normalize ⟨p.coeffs.map (c * ·)⟩

@[simp] theorem normalize_scale (c : K) (p : DensePolynomial K) :
    (scale c p).normalize = scale c p := by
  exact normalize_normalize _

private theorem dropWhile_map_mul_left {c : K} (hc : c ≠ 0) (cs : List K) :
    (cs.map (c * ·)).dropWhile (· = 0) =
      (cs.dropWhile (· = 0)).map (c * ·) := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        simpa using ih
      · have hmul : c * a ≠ 0 := mul_ne_zero_direct hc ha
        simp [List.dropWhile_cons_of_neg, ha, hmul]

theorem scale_coeffs_of_ne_zero {c : K} (hc : c ≠ 0) (p : DensePolynomial K) :
    (scale c p).coeffs = p.normalize.coeffs.map (c * ·) := by
  exact dropWhile_map_mul_left hc p.coeffs

@[simp] theorem scale_zero_left (p : DensePolynomial K) : scale 0 p = 0 := by
  apply ext
  change (p.coeffs.map (0 * ·)).dropWhile (· = 0) = []
  induction p.coeffs with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons]
      change (0 * a :: as.map (0 * ·)).dropWhile (· = 0) = []
      rw [zero_mul, List.dropWhile_cons_of_pos (by exact decide_eq_true rfl)]
      exact ih

omit [DecidableEq K] in
private theorem map_one_mul : ∀ coefficients : List K,
    coefficients.map (1 * ·) = coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      rw [List.map_cons, one_mul, map_one_mul coefficients]

@[simp] theorem scale_one_left (p : DensePolynomial K) :
    scale 1 p = p.normalize := by
  apply ext
  change (p.coeffs.map (1 * ·)).dropWhile (· = 0) =
    p.coeffs.dropWhile (· = 0)
  rw [map_one_mul]

theorem scale_constant (c a : K) :
    scale c (constant a) = normalize (constant (c * a)) := by
  apply ext
  simp [scale, normalize, constant]

/-- Scaling a negated polynomial by the oppositely signed quotient leaves the
normalized dense representation unchanged. -/
theorem scale_div_neg_neg {a b : K} (hb : b ≠ 0) (p : DensePolynomial K) :
    scale (a / -b) (-p) = scale (a / b) p := by
  by_cases ha : a = 0
  · subst a
    rw [RFAP.ExplicitField.zero_div, RFAP.ExplicitField.zero_div,
      scale_zero_left, scale_zero_left]
  · have hab : a / b ≠ 0 := div_ne_zero_direct ha hb
    have hanegb : a / -b ≠ 0 := div_ne_zero_direct ha (neg_ne_zero.mpr hb)
    apply ext
    rw [scale_coeffs_of_ne_zero hanegb, scale_coeffs_of_ne_zero hab]
    rw [normalize_neg, neg_coeffs]
    change (p.normalize.coeffs.map (-·)).map ((a / -b) * ·) =
      p.normalize.coeffs.map ((a / b) * ·)
    rw [List.map_map]
    apply QuotientFreeList.map_congr_left
    intro x hx
    change (a / -b) * (-x) = (a / b) * x
    rw [RFAP.ExplicitField.div_neg, neg_mul, mul_neg]
    exact _root_.neg_neg (a / b * x)

omit [DecidableEq K] in
private theorem foldl_map_scale (c x : K) : ∀ (cs : List K) (acc : K),
    (cs.map (c * ·)).foldl (fun value a => value * x + a) (c * acc) =
      c * cs.foldl (fun value a => value * x + a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      have hacc : c * acc * x + c * a = c * (acc * x + a) := by ring1
      rw [hacc]
      exact foldl_map_scale c x as (acc * x + a)

@[simp] theorem eval_scale (c : K) (p : DensePolynomial K) (x : K) :
    (scale c p).eval x = c * p.eval x := by
  rw [scale, eval_normalize]
  dsimp only [eval, evalCoeffs]
  simpa only [mul_zero] using foldl_map_scale c x p.coeffs 0

theorem scale_normalize (c : K) (p : DensePolynomial K) :
    scale c p.normalize = scale c p := by
  by_cases hc : c = 0
  · subst c
    rw [scale_zero_left, scale_zero_left]
  · apply ext
    rw [scale_coeffs_of_ne_zero hc, scale_coeffs_of_ne_zero hc,
      normalize_normalize]

theorem scale_eq_zero_of_isZero (c : K) {p : DensePolynomial K}
    (hp : p.isZero = true) : scale c p = 0 := by
  rw [← scale_normalize c p, normalize_eq_zero_of_isZero hp]
  rfl

@[simp] theorem scale_zero_right (c : K) :
    scale c (0 : DensePolynomial K) = 0 :=
  scale_eq_zero_of_isZero c isZero_zero

@[simp] theorem scale_neg_left (c : K) (p : DensePolynomial K) :
    scale (-c) p = -scale c p := by
  by_cases cZero : c = 0
  · subst c
    simp only [neg_zero, scale_zero_left]
    rfl
  · have negNonzero : -c ≠ 0 := neg_ne_zero.mpr cZero
    apply ext
    rw [scale_coeffs_of_ne_zero negNonzero,
      neg_coeffs, normalize_scale, scale_coeffs_of_ne_zero cZero,
      List.map_map]
    apply QuotientFreeList.map_congr_left
    intro x _
    exact neg_mul c x

@[simp] theorem scale_neg_right (c : K) (p : DensePolynomial K) :
    scale c (-p) = -scale c p := by
  by_cases cZero : c = 0
  · subst c
    simp only [scale_zero_left]
    rfl
  · apply ext
    rw [scale_coeffs_of_ne_zero cZero, normalize_neg, neg_coeffs,
      neg_coeffs, normalize_scale, scale_coeffs_of_ne_zero cZero,
      List.map_map]
    simp only [List.map_map]
    apply QuotientFreeList.map_congr_left
    intro x _
    exact mul_neg c x

/-- Multiplication by `X^n`, implemented by appending `n` zero coefficients. -/
def shift (n : ℕ) (p : DensePolynomial K) : DensePolynomial K :=
  if p.isZero then 0 else ⟨p.normalize.coeffs ++ List.replicate n 0⟩

@[simp] theorem shift_zero (n : ℕ) : shift n (0 : DensePolynomial K) = 0 := by
  simp [shift]

@[simp] theorem normalize_shift (n : ℕ) (p : DensePolynomial K) :
    (shift n p).normalize = shift n p := by
  by_cases pZero : p.isZero = true
  · rw [shift, if_pos pZero]
    rfl
  · have pNonzero : p.isZero = false := by simpa using pZero
    obtain ⟨tail, coefficients, _⟩ := normalized_coeffs_shape pNonzero
    apply ext
    rw [shift, if_neg (by simpa using pNonzero)]
    change
      ((p.normalize.coeffs ++ List.replicate n 0).dropWhile (· = 0)) =
        p.normalize.coeffs ++ List.replicate n 0
    rw [coefficients]
    simp only [List.cons_append]
    rw [List.dropWhile_cons_of_neg (by
      simp [leadingCoeff_ne_zero pNonzero])]

/-- Shifting by `n` adds at most `n` finite coefficient slots. -/
theorem degreeCount_shift_le (n : ℕ) (p : DensePolynomial K) :
    (shift n p).degreeCount ≤ p.degreeCount + n := by
  by_cases zero : p.isZero = true
  · rw [shift, if_pos zero, degreeCount]
    exact Nat.zero_le _
  · have nonzero : p.isZero = false := by simpa using zero
    rw [degreeCount, normalize_shift, shift, if_neg (by simpa using nonzero),
      List.length_append, List.length_replicate]
    rfl

/-- A displayed constant occupies at most one normalized coefficient slot. -/
theorem degreeCount_constant_le_one (a : K) :
    (constant a).degreeCount ≤ 1 := by
  by_cases zero : a = 0
  · subst a
    change (normalize (constant (0 : K))).coeffs.length ≤ 1
    rw [normalize_constant_zero]
    exact Nat.zero_le _
  · rw [degreeCount, normalize_constant_of_ne zero]
    rfl

@[simp] theorem shift_neg (n : ℕ) (p : DensePolynomial K) :
    shift n (-p) = -shift n p := by
  by_cases pZero : p.isZero = true
  · have negZero : (-p).isZero = true := by simpa using pZero
    rw [shift, if_pos negZero, shift, if_pos pZero]
    rfl
  · have pNonzero : p.isZero = false := by simpa using pZero
    have negNonzero : (-p).isZero = false := by simpa using pNonzero
    apply ext
    rw [shift, if_neg (by simpa using negNonzero), normalize_neg,
      neg_coeffs]
    rw [neg_coeffs, normalize_shift, shift,
      if_neg (by simpa using pNonzero)]
    simp only [List.map_append, List.map_replicate, neg_zero]

theorem shift_one_constant_of_ne {a : K} (ha : a ≠ 0) :
    shift 1 (constant a) = ⟨[a, 0]⟩ := by
  simp [shift, isZero, normalize, constant, ha]

omit [DecidableEq K] in
private theorem foldl_replicate_zero (x : K) (n : ℕ) (acc : K) :
    (List.replicate n 0).foldl (fun value a => value * x + a) acc = acc * x ^ n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, add_zero, ih, pow_succ]
      ring1

omit [DecidableEq K] in
theorem evalCoeffs_append_replicate_zero (x : K) (cs : List K) (n : ℕ) :
    evalCoeffs x (cs ++ List.replicate n 0) = evalCoeffs x cs * x ^ n := by
  simp only [evalCoeffs, QuotientFreeList.foldl_append]
  exact foldl_replicate_zero x n _

theorem eval_eq_zero_of_isZero {p : DensePolynomial K} (hp : p.isZero = true) (x : K) :
    p.eval x = 0 := by
  have hempty : p.normalize.coeffs = [] := by
    simpa [isZero] using hp
  rw [← eval_normalize p x]
  change evalCoeffs x p.normalize.coeffs = 0
  rw [hempty]
  rfl

theorem isZero_false_of_eval_ne {p : DensePolynomial K} {x : K}
    (hp : p.eval x ≠ 0) : p.isZero = false := by
  cases zero : p.isZero with
  | false => rfl
  | true => exact (hp (eval_eq_zero_of_isZero zero x)).elim

@[simp] theorem eval_shift (n : ℕ) (p : DensePolynomial K) (x : K) :
    (shift n p).eval x = p.eval x * x ^ n := by
  rw [shift]
  split
  · rename_i hp
    rw [eval_zero, eval_eq_zero_of_isZero hp, zero_mul]
  · change evalCoeffs x (p.normalize.coeffs ++ List.replicate n 0) =
        evalCoeffs x p.coeffs * x ^ n
    rw [evalCoeffs_append_replicate_zero]
    change evalCoeffs x (p.coeffs.dropWhile (· = 0)) * x ^ n =
      evalCoeffs x p.coeffs * x ^ n
    rw [evalCoeffs_dropWhile_zero]

/-- The one-term quotient used to cancel the current leading coefficient. -/
def leadQuotient (p q : DensePolynomial K) : DensePolynomial K :=
  let exponent := p.natDegree - q.natDegree
  shift exponent ⟨[p.leadingCoeff / q.leadingCoeff]⟩

/-- One exact long-division cancellation step. -/
def cancelLead (p q : DensePolynomial K) : DensePolynomial K :=
  p - shift (p.natDegree - q.natDegree)
    (scale (p.leadingCoeff / q.leadingCoeff) q)

@[simp] theorem normalize_cancelLead (p q : DensePolynomial K) :
    (cancelLead p q).normalize = cancelLead p q := by
  exact normalize_sub _ _

/-- Negating a nonzero divisor changes the one-term quotient sign but leaves
the long-division cancellation polynomial unchanged. -/
theorem cancelLead_neg_right (p q : DensePolynomial K) (hq : q.isZero = false) :
    cancelLead p (-q) = cancelLead p q := by
  rw [cancelLead, cancelLead, natDegree_neg, leadingCoeff_neg,
    scale_div_neg_neg (leadingCoeff_ne_zero hq)]

/-- Simultaneously negating dividend and divisor negates the exact
long-division cancellation remainder. -/
theorem cancelLead_neg_both (p q : DensePolynomial K)
    (pNormalized : p.normalize = p) :
    cancelLead (-p) (-q) = -cancelLead p q := by
  have quotient : (-p.leadingCoeff) / (-q.leadingCoeff) =
      p.leadingCoeff / q.leadingCoeff := by
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.inv_neg, neg_mul_neg,
      ← RFAP.ExplicitField.div_eq_mul_inv]
  rw [cancelLead, cancelLead, natDegree_neg, natDegree_neg,
    leadingCoeff_neg, leadingCoeff_neg, quotient,
    scale_neg_right, shift_neg]
  exact neg_sub_neg_of_normalized p
    (shift (p.natDegree - q.natDegree)
      (scale (p.leadingCoeff / q.leadingCoeff) q))
    pNormalized (normalize_shift _ _)

theorem eval_leadQuotient (p q : DensePolynomial K) (x : K) :
    (leadQuotient p q).eval x =
      (p.leadingCoeff / q.leadingCoeff) * x ^ (p.natDegree - q.natDegree) := by
  rw [leadQuotient, eval_shift]
  simp [eval, evalCoeffs]

theorem eval_cancelLead (p q : DensePolynomial K) (x : K) :
    (cancelLead p q).eval x =
      p.eval x - q.eval x * (leadQuotient p q).eval x := by
  rw [cancelLead, eval_sub, eval_shift, eval_scale, eval_leadQuotient]
  let c := p.leadingCoeff / q.leadingCoeff
  let y := x ^ (p.natDegree - q.natDegree)
  change p.eval x - c * q.eval x * y =
    p.eval x - q.eval x * (c * y)
  ring1

private theorem length_dropWhile_le_direct (as : List K) :
    (as.dropWhile (· = 0)).length ≤ as.length := by
  induction as with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
      by_cases ha : a = 0
      · rw [List.dropWhile_cons_of_pos (by simp [ha])]
        exact ih.trans (Nat.le_succ as.length)
      · rw [List.dropWhile_cons_of_neg (by simp [ha])]

private theorem length_dropWhile_lt_cons_zero (as : List K) :
    ((0 :: as).dropWhile (· = 0)).length < (0 :: as).length := by
  rw [List.dropWhile_cons_of_pos (by simp)]
  exact (length_dropWhile_le_direct as).trans_lt
    (Nat.lt_succ_self as.length)

theorem cancelLead_degreeCount_lt {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hpNormalized : p.normalize = p) (hqNormalized : q.normalize = q)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).degreeCount < p.degreeCount := by
  obtain ⟨a, as, hpcoeffs, ha⟩ :
      ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 := by
    cases hpcase : p.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpNormalized, hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hpNormalized] at hlead
        simpa only [hpcase, List.headD_cons] using hlead
  obtain ⟨b, bs, hqcoeffs, hb⟩ :
      ∃ b bs, q.coeffs = b :: bs ∧ b ≠ 0 := by
    cases hqcase : q.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqNormalized, hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons b bs =>
        refine ⟨b, bs, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hqNormalized] at hlead
        simpa only [hqcase, List.headD_cons] using hlead
  have hpCount : p.degreeCount = as.length + 1 := by
    simp [degreeCount, hpNormalized, hpcoeffs]
  have hqCount : q.degreeCount = bs.length + 1 := by
    simp [degreeCount, hqNormalized, hqcoeffs]
  have hlength : bs.length ≤ as.length := by
    have hpDegree := natDegree_add_one_eq_degreeCount hp
    have hqDegree := natDegree_add_one_eq_degreeCount hq
    omega
  have hleadP : p.leadingCoeff = a := by
    simp [leadingCoeff, hpNormalized, hpcoeffs]
  have hleadQ : q.leadingCoeff = b := by
    simp [leadingCoeff, hqNormalized, hqcoeffs]
  let c : K := a / b
  have hc : c ≠ 0 := div_ne_zero_direct ha hb
  have hcb : c * b = a := by
    dsimp [c]
    exact RFAP.ExplicitField.div_mul_cancel a hb
  have hscaleCoeffs : (scale c q).coeffs =
      c * b :: bs.map (c * ·) := by
    rw [scale_coeffs_of_ne_zero hc, hqNormalized, hqcoeffs]
    rfl
  have hscaleZero : (scale c q).isZero = false := by
    simp [isZero, normalize, hscaleCoeffs, hcb, ha]
  have hexponent : p.natDegree - q.natDegree = as.length - bs.length := by
    have hpDegree := natDegree_add_one_eq_degreeCount hp
    have hqDegree := natDegree_add_one_eq_degreeCount hq
    omega
  let shifted := shift (p.natDegree - q.natDegree) (scale c q)
  have hshiftCoeffs : shifted.coeffs =
      c * b :: (bs.map (c * ·) ++ List.replicate (as.length - bs.length) 0) := by
    dsimp [shifted]
    rw [shift, if_neg (by simpa using hscaleZero), normalize_scale,
      hscaleCoeffs, hexponent]
    rfl
  have hshiftLength : shifted.coeffs.length = p.coeffs.length := by
    rw [hshiftCoeffs, hpcoeffs]
    simp only [List.length_append, List.length_cons, List.length_map,
      List.length_replicate]
    omega
  have hshiftHead : shifted.coeffs.headD 0 = a := by
    rw [hshiftCoeffs]
    simp [hcb]
  have hshiftNormalized : shifted.normalize = shifted := by
    apply ext
    simp [normalize, hshiftCoeffs, hcb, ha]
  have hnegCoeffs : (-shifted).coeffs = shifted.coeffs.map (-·) := by
    rw [neg_coeffs, hshiftNormalized]
  rw [cancelLead, hleadP, hleadQ]
  change (p + -shifted).degreeCount < p.degreeCount
  rw [degreeCount, normalize_add, hpCount]
  change (add p (-shifted)).coeffs.length < as.length + 1
  simp only [add]
  rw [hnegCoeffs, List.length_map, hshiftLength, max_self, Nat.sub_self,
    hpcoeffs]
  simp only [padLeft, List.replicate_zero, List.nil_append]
  rw [hshiftCoeffs]
  simp only [List.map_cons, List.zipWith_cons_cons, hcb, add_neg_cancel]
  let out := List.zipWith (· + ·) as
    ((bs.map (c * ·) ++ List.replicate (as.length - bs.length) 0).map (-·))
  have houtLength : out.length = as.length := by
    dsimp only [out]
    rw [List.length_zipWith, List.length_map, List.length_append,
      List.length_map, List.length_replicate]
    omega
  change ((0 :: out).dropWhile (· = 0)).length < (0 :: as).length
  simpa only [List.length_cons, houtLength] using
    (length_dropWhile_lt_cons_zero (K := K) out)

/-- Normalization can only shorten a finite coefficient list. -/
private theorem degreeCount_le_coeffs_length (p : DensePolynomial K) :
    p.degreeCount ≤ p.coeffs.length :=
  length_dropWhile_le_direct p.coeffs

private theorem coeffs_length_add_le (p q : DensePolynomial K) :
    (p + q).coeffs.length ≤ max p.coeffs.length q.coeffs.length := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := le_max_left _ _
  have hq : q.coeffs.length ≤ n := le_max_right _ _
  have hps : ps.length = n := by
    simp [ps, padLeft, Nat.sub_add_cancel hp]
  have hqs : qs.length = n := by
    simp [qs, padLeft, Nat.sub_add_cancel hq]
  change ((List.zipWith (· + ·) ps qs).dropWhile (· = 0)).length ≤ n
  exact (length_dropWhile_le_direct _).trans (by
    rw [List.length_zipWith, hps, hqs, min_self])

theorem degreeCount_add_le_of_normalized {p q : DensePolynomial K}
    (hp : p.normalize = p) (hq : q.normalize = q) :
    (p + q).degreeCount ≤ max p.degreeCount q.degreeCount := by
  change (p + q).normalize.coeffs.length ≤ _
  rw [normalize_add]
  apply (coeffs_length_add_le p q).trans
  change max p.coeffs.length q.coeffs.length ≤
    max p.normalize.coeffs.length q.normalize.coeffs.length
  rw [hp, hq]

theorem degreeCount_sub_le_of_normalized {p q : DensePolynomial K}
    (hp : p.normalize = p) :
    (p - q).degreeCount ≤ max p.degreeCount q.degreeCount := by
  change (p + -q).degreeCount ≤ _
  have hneg : (-q).normalize = -q := normalize_neg q
  have hbound := degreeCount_add_le_of_normalized hp hneg
  rw [degreeCount_neg] at hbound
  exact hbound

private theorem coeffs_length_scale_le (c : K) (p : DensePolynomial K) :
    (scale c p).coeffs.length ≤ p.degreeCount := by
  by_cases hc : c = 0
  · subst c
    rw [scale_zero_left]
    exact Nat.zero_le _
  · rw [scale_coeffs_of_ne_zero hc, List.length_map]
    rfl

private theorem coeffs_length_shift_le (p : DensePolynomial K) :
    (shift 1 p).coeffs.length ≤ p.degreeCount + 1 := by
  rw [shift]
  split
  · exact Nat.zero_le _
  · simp [degreeCount]

private theorem coeffs_length_mulFold_le (q : DensePolynomial K) :
    ∀ (coefficients : List K) (acc : DensePolynomial K) (bound : Nat),
      q.degreeCount ≤ bound + 1 →
      acc.coeffs.length ≤ bound →
      (coefficients.foldl
        (fun value a => shift 1 value + scale a q) acc).coeffs.length ≤
          bound + coefficients.length
  | [], _, _, _, hacc => by simpa using hacc
  | a :: remaining, acc, bound, hq, hacc => by
      simp only [List.foldl_cons, List.length_cons]
      have hnext : (shift 1 acc + scale a q).coeffs.length ≤ bound + 1 := by
        apply (coeffs_length_add_le _ _).trans
        apply max_le
        · exact (coeffs_length_shift_le acc).trans (by
            have := degreeCount_le_coeffs_length acc
            omega)
        · exact (coeffs_length_scale_le a q).trans hq
      have hrecursive := coeffs_length_mulFold_le q remaining
        (shift 1 acc + scale a q) (bound + 1) (by omega) hnext
      omega

/-- Polynomial multiplication as a finite Horner fold over the left factor. -/
def mulPolynomial (p q : DensePolynomial K) : DensePolynomial K :=
  p.coeffs.foldl (fun acc a => shift 1 acc + scale a q) 0

instance : Mul (DensePolynomial K) := ⟨mulPolynomial⟩

omit [DecidableEq K] in
theorem zipWith_replicate_zero_add (cs : List K) :
    List.zipWith (· + ·) (List.replicate cs.length 0) cs = cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons]
      rw [List.replicate_succ, List.zipWith_cons_cons, zero_add, ih]

theorem zero_add_normalize (p : DensePolynomial K) :
    (0 : DensePolynomial K) + p = p.normalize := by
  apply ext
  change (add 0 p).coeffs = p.normalize.coeffs
  rw [show (0 : DensePolynomial K) = ⟨[]⟩ from rfl]
  simp [add, padLeft, normalize, zipWith_replicate_zero_add]

omit [DecidableEq K] in
private theorem zipWith_add_replicate_zero (cs : List K) :
    List.zipWith (· + ·) cs (List.replicate cs.length 0) = cs := by
  induction cs with
  | nil => rfl
  | cons a as inductionHypothesis =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, add_zero]
      rw [inductionHypothesis]

/-- Adding the represented zero on the right changes only normalization. -/
theorem add_zero_normalize (p : DensePolynomial K) :
    p + (0 : DensePolynomial K) = p.normalize := by
  apply ext
  change (add p 0).coeffs = p.normalize.coeffs
  rw [show (0 : DensePolynomial K) = ⟨[]⟩ from rfl]
  simp [add, padLeft, normalize, zipWith_add_replicate_zero]

/-- When the left input is strictly longer and has a nonzero leading
coefficient, finite left-padded addition preserves that leading coefficient
and length. -/
private theorem add_coeffs_of_left_longer
    {p q : DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0)
    (hlen : q.coeffs.length < p.coeffs.length) :
    ∃ bs, (p + q).coeffs = a :: bs ∧ bs.length = as.length := by
  have hle : q.coeffs.length ≤ p.coeffs.length := Nat.le_of_lt hlen
  have hmax : max p.coeffs.length q.coeffs.length = p.coeffs.length :=
    max_eq_left hle
  have hsubpos : 0 < p.coeffs.length - q.coeffs.length :=
    Nat.sub_pos_of_lt hlen
  cases hsub : p.coeffs.length - q.coeffs.length with
  | zero => simp [hsub] at hsubpos
  | succ d =>
      refine ⟨List.zipWith (· + ·) as
        (List.replicate d 0 ++ q.coeffs), ?_, ?_⟩
      · change (add p q).coeffs = _
        simp only [add]
        rw [hmax]
        simp only [Nat.sub_self, padLeft, List.replicate_zero, List.nil_append]
        rw [hsub, hp]
        simp only [List.replicate_succ, List.cons_append,
          List.zipWith_cons_cons, add_zero, normalize]
        rw [List.dropWhile_cons_of_neg (by simp [ha])]
      · rw [List.length_zipWith]
        simp only [List.length_append, List.length_replicate]
        have hlength : p.coeffs.length = as.length + 1 := by simp [hp]
        have rearranged : (d + q.coeffs.length) + 1 =
            (d + 1) + q.coeffs.length := by
          rw [Nat.add_assoc, Nat.add_comm q.coeffs.length 1,
            ← Nat.add_assoc]
        have equalSuccessors : (d + q.coeffs.length) + 1 =
            as.length + 1 := by
          calc
            (d + q.coeffs.length) + 1 =
                (d + 1) + q.coeffs.length := rearranged
            _ = (p.coeffs.length - q.coeffs.length) +
                q.coeffs.length := by rw [hsub]
            _ = p.coeffs.length := Nat.sub_add_cancel hle
            _ = as.length + 1 := hlength
        have heq : as.length = d + q.coeffs.length :=
          (Nat.add_right_cancel equalSuccessors).symm
        rw [← heq, Nat.min_self]

/-- One multiplication Horner step preserves a displayed nonzero leading
coefficient and adds exactly one coefficient slot. -/
private theorem mulStep_preserves_leading_shape
    (q : DensePolynomial K) {acc : DensePolynomial K} {a : K} {as : List K}
    (hcoeffs : acc.coeffs = a :: as) (ha : a ≠ 0)
    (hlength : q.normalize.coeffs.length ≤ acc.coeffs.length) (b : K) :
  ∃ out,
      (shift 1 acc + scale b q).coeffs = a :: out ∧
        out.length = as.length + 1 := by
  have hzero : acc.isZero = false := by
    simp [isZero, normalize, hcoeffs, List.dropWhile_cons_of_neg,
      show ¬decide (a = 0) = true by simp [ha]]
  have hnormalize : acc.normalize = acc := by
    apply ext
    simp [normalize, hcoeffs, List.dropWhile_cons_of_neg,
      show ¬decide (a = 0) = true by simp [ha]]
  have hshift : (shift 1 acc).coeffs = a :: (as ++ [0]) := by
    rw [shift, if_neg (by simpa using hzero), hnormalize, hcoeffs]
    rfl
  have hscale : (scale b q).coeffs.length ≤ q.normalize.coeffs.length := by
    by_cases hb : b = 0
    · subst b
      rw [scale_zero_left]
      change [].length ≤ q.normalize.coeffs.length
      exact Nat.zero_le _
    · rw [scale_coeffs_of_ne_zero hb]
      simp
  have hlt : (scale b q).coeffs.length < (shift 1 acc).coeffs.length := by
    have haccLength : acc.coeffs.length = as.length + 1 := by simp [hcoeffs]
    have shiftLonger : acc.coeffs.length <
        (shift 1 acc).coeffs.length := by
      rw [haccLength, hshift]
      simp only [List.length_cons, List.length_append]
      exact Nat.lt_succ_self _
    exact (hscale.trans hlength).trans_lt shiftLonger
  obtain ⟨out, hout, houtLength⟩ :=
    add_coeffs_of_left_longer hshift ha hlt
  refine ⟨out, hout, ?_⟩
  rw [houtLength]
  simp

/-- Repeated multiplication Horner steps retain the same displayed leading
coefficient while growing by exactly the number of scanned coefficients. -/
private theorem foldl_mulStep_preserves_leading_shape
    (q : DensePolynomial K) :
    ∀ (coefficients : List K) (acc : DensePolynomial K)
      (a : K) (as : List K),
      acc.coeffs = a :: as → a ≠ 0 →
      q.normalize.coeffs.length ≤ acc.coeffs.length →
      ∃ out,
        (coefficients.foldl
          (fun value coefficient =>
            shift 1 value + scale coefficient q) acc).coeffs = a :: out ∧
          out.length = as.length + coefficients.length
  | [], _, _, as, hcoeffs, _, _ => ⟨as, hcoeffs, by simp⟩
  | coefficient :: remaining, acc, a, as, hcoeffs, ha, hlength => by
      obtain ⟨next, hnext, hnextLength⟩ :=
        mulStep_preserves_leading_shape q hcoeffs ha hlength coefficient
      have hnextBound : q.normalize.coeffs.length ≤
          (shift 1 acc + scale coefficient q).coeffs.length := by
        rw [hnext, List.length_cons]
        have haccLength : acc.coeffs.length = as.length + 1 := by
          simp [hcoeffs]
        have accumulatorNext : acc.coeffs.length = next.length :=
          haccLength.trans hnextLength.symm
        exact hlength.trans
          (accumulatorNext.le.trans (Nat.le_add_right _ _))
      obtain ⟨out, hout, houtLength⟩ :=
        foldl_mulStep_preserves_leading_shape q remaining
          (shift 1 acc + scale coefficient q) a next hnext ha hnextBound
      refine ⟨out, ?_, ?_⟩
      · simpa only [List.foldl_cons] using hout
      · rw [houtLength, hnextLength]
        simp only [List.length_cons]
        calc
          (as.length + 1) + remaining.length =
              as.length + (1 + remaining.length) :=
            Nat.add_assoc _ _ _
          _ = as.length + (remaining.length + 1) :=
            congrArg (as.length + ·) (Nat.add_comm 1 remaining.length)

private theorem normalize_eq_self_of_coeffs_cons
    {p : DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0) : p.normalize = p := by
  apply ext
  simp [normalize, hp, List.dropWhile_cons_of_neg,
    show ¬decide (a = 0) = true by simp [ha]]

private theorem isZero_false_of_coeffs_cons
    {p : DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0) : p.isZero = false := by
  simp [isZero, normalize, hp, List.dropWhile_cons_of_neg,
    show ¬decide (a = 0) = true by simp [ha]]

/-- Subtracting a strictly shorter normalized polynomial preserves the
displayed leading coefficient and the exact coefficient count of the left
polynomial. -/
theorem sub_coeffs_shape_of_degreeCount_lt
    {p q : DensePolynomial K} (hp : p.isZero = false)
    (hpNormalized : p.normalize = p)
    (hlength : q.degreeCount < p.degreeCount) :
    ∃ out,
      (p - q).coeffs = p.leadingCoeff :: out ∧
        out.length + 1 = p.degreeCount := by
  obtain ⟨a, as, hpcoeffs, ha⟩ :
      ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 := by
    cases hpcase : p.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpNormalized, hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hpNormalized, hpcase] at hlead
        simpa only [List.headD_cons] using hlead
  have hpLeading : p.leadingCoeff = a := by
    change p.normalize.coeffs.headD 0 = a
    rw [hpNormalized, hpcoeffs]
    rfl
  have hpCount : p.coeffs.length = p.degreeCount := by
    change p.coeffs.length = p.normalize.coeffs.length
    rw [hpNormalized]
  have hqCount : (-q).coeffs.length = q.degreeCount := by
    rw [neg_coeffs, List.length_map]
    rfl
  have hshort : (-q).coeffs.length < p.coeffs.length := by
    rw [hqCount, hpCount]
    exact hlength
  obtain ⟨out, hout, houtLength⟩ :=
    add_coeffs_of_left_longer hpcoeffs ha hshort
  refine ⟨out, ?_, ?_⟩
  · change (p + -q).coeffs = _
    rw [hout, hpLeading]
  · rw [houtLength]
    have hpLength : p.coeffs.length = as.length + 1 := by simp [hpcoeffs]
    exact hpLength.symm.trans hpCount

/-- A finite Horner accumulator has a nonzero leading coefficient and is at
least as long as the normalized right factor. -/
private def HasLeadingAtLeast (q p : DensePolynomial K) : Prop :=
  ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 ∧
    q.normalize.coeffs.length ≤ p.coeffs.length

private theorem mulStep_preserves_hasLeadingAtLeast (q : DensePolynomial K)
    {acc : DensePolynomial K} (hacc : HasLeadingAtLeast q acc) (b : K) :
    HasLeadingAtLeast q (shift 1 acc + scale b q) := by
  rcases hacc with ⟨a, as, hcoeffs, ha, hlength⟩
  have hzero : acc.isZero = false :=
    isZero_false_of_coeffs_cons hcoeffs ha
  have hnormalize : acc.normalize = acc :=
    normalize_eq_self_of_coeffs_cons hcoeffs ha
  have hshift : (shift 1 acc).coeffs = a :: (as ++ [0]) := by
    rw [shift, if_neg (by simpa using hzero), hnormalize, hcoeffs]
    rfl
  have hscale : (scale b q).coeffs.length ≤ q.normalize.coeffs.length := by
    by_cases hb : b = 0
    · subst b
      rw [scale_zero_left]
      change [].length ≤ q.normalize.coeffs.length
      simp
    · rw [scale_coeffs_of_ne_zero hb]
      simp
  have hlt : (scale b q).coeffs.length < (shift 1 acc).coeffs.length := by
    have haccLength : acc.coeffs.length = as.length + 1 := by simp [hcoeffs]
    have shiftLonger : acc.coeffs.length <
        (shift 1 acc).coeffs.length := by
      rw [haccLength, hshift]
      simp only [List.length_cons, List.length_append]
      exact Nat.lt_succ_self _
    exact (hscale.trans hlength).trans_lt shiftLonger
  obtain ⟨out, hout, houtLength⟩ :=
    add_coeffs_of_left_longer hshift ha hlt
  refine ⟨a, out, hout, ha, ?_⟩
  rw [hout]
  simp only [List.length_cons]
  rw [houtLength]
  have haccLength : acc.coeffs.length = as.length + 1 := by simp [hcoeffs]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [← haccLength]
  exact hlength.trans (Nat.le_add_right _ _)

private theorem foldl_mulStep_preserves_hasLeadingAtLeast
    (q : DensePolynomial K) (cs : List K) {acc : DensePolynomial K}
    (hacc : HasLeadingAtLeast q acc) :
    HasLeadingAtLeast q
      (cs.foldl (fun value a => shift 1 value + scale a q) acc) := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih (mulStep_preserves_hasLeadingAtLeast q hacc a)

private theorem foldl_mulStep_dropWhile_zero (q : DensePolynomial K)
    (cs : List K) :
    (cs.dropWhile (· = 0)).foldl
        (fun value a => shift 1 value + scale a q) 0 =
      cs.foldl (fun value a => shift 1 value + scale a q) 0 := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        rw [List.dropWhile_cons_of_pos (by simp)]
        simp only [List.foldl_cons]
        rw [show shift 1 (0 : DensePolynomial K) + scale 0 q = 0 by
          rw [scale_zero_left]
          change add (shift 1 0) 0 = 0
          rw [shift, if_pos (show (0 : DensePolynomial K).isZero = true by rfl)]
          rfl]
        exact ih
      · rw [List.dropWhile_cons_of_neg (by simp [ha])]

theorem mul_eq_zero_of_isZero_left {p q : DensePolynomial K}
    (hp : p.isZero = true) : p * q = 0 := by
  rw [show p * q = mulPolynomial p q from rfl, mulPolynomial]
  rw [← foldl_mulStep_dropWhile_zero q p.coeffs]
  change p.normalize.coeffs.foldl
      (fun value a => shift 1 value + scale a q) 0 = 0
  rw [normalize_eq_zero_of_isZero hp]
  rfl

theorem mul_eq_zero_of_isZero_right {p q : DensePolynomial K}
    (hq : q.isZero = true) : p * q = 0 := by
  rw [show p * q = mulPolynomial p q from rfl, mulPolynomial]
  rw [← foldl_mulStep_dropWhile_zero q p.coeffs]
  change p.normalize.coeffs.foldl
      (fun value a => shift 1 value + scale a q) 0 = 0
  induction p.normalize.coeffs with
  | nil => rfl
  | cons a remaining inductionHypothesis =>
      rw [List.foldl_cons, scale_eq_zero_of_isZero a hq]
      rw [shift, if_pos (show (0 : DensePolynomial K).isZero = true by rfl)]
      change remaining.foldl
        (fun value a => shift 1 value + scale a q) 0 = 0
      exact inductionHypothesis

theorem degreeCount_mul_le (p q : DensePolynomial K) :
    (p * q).degreeCount ≤ p.degreeCount + q.degreeCount - 1 := by
  by_cases hp : p.isZero = true
  · rw [mul_eq_zero_of_isZero_left hp,
      degreeCount_eq_zero_of_isZero (p := (0 : DensePolynomial K)) rfl]
    exact Nat.zero_le _
  · have hpFalse : p.isZero = false := Bool.eq_false_of_not_eq_true hp
    by_cases hq : q.isZero = true
    · rw [mul_eq_zero_of_isZero_right hq,
        degreeCount_eq_zero_of_isZero (p := (0 : DensePolynomial K)) rfl]
      exact Nat.zero_le _
    · have hqFalse : q.isZero = false := Bool.eq_false_of_not_eq_true hq
      have hpPositive := degreeCount_pos_of_isZero_false hpFalse
      have hqPositive := degreeCount_pos_of_isZero_false hqFalse
      have hfold := coeffs_length_mulFold_le q p.normalize.coeffs 0
        (q.degreeCount - 1) (by omega)
        (show (0 : DensePolynomial K).coeffs.length ≤ q.degreeCount - 1 by
          exact Nat.zero_le _)
      have hcoeffs : (p * q).coeffs.length ≤
          q.degreeCount - 1 + p.degreeCount := by
        have hproduct : p * q = p.normalize.coeffs.foldl
            (fun value a => shift 1 value + scale a q) 0 := by
          rw [show p * q = mulPolynomial p q from rfl, mulPolynomial]
          rw [← foldl_mulStep_dropWhile_zero q p.coeffs]
          rfl
        rw [hproduct]
        exact hfold
      exact (degreeCount_le_coeffs_length (p * q)).trans (by omega)

/-- Exact finite coefficient shape of a product of two nonzero dense
polynomials.  In particular, the displayed head is the product of the two
displayed leading coefficients and the tail has the sum of the input natural
degrees. -/
theorem mul_coeffs_shape {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    ∃ out,
      (p * q).coeffs = p.leadingCoeff * q.leadingCoeff :: out ∧
        out.length = p.natDegree + q.natDegree := by
  obtain ⟨pa, pas, hpcoeffs, hpa⟩ :
      ∃ pa pas, p.normalize.coeffs = pa :: pas ∧ pa ≠ 0 := by
    cases hpcase : p.normalize.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hpcase, List.headD_cons] using hlead
  obtain ⟨qa, qas, hqcoeffs, hqa⟩ :
      ∃ qa qas, q.normalize.coeffs = qa :: qas ∧ qa ≠ 0 := by
    cases hqcase : q.normalize.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hqcase, List.headD_cons] using hlead
  have hpLeading : p.leadingCoeff = pa := by
    change p.normalize.coeffs.headD 0 = pa
    rw [hpcoeffs]
    rfl
  have hqLeading : q.leadingCoeff = qa := by
    change q.normalize.coeffs.headD 0 = qa
    rw [hqcoeffs]
    rfl
  have hpDegree : p.natDegree = pas.length := by
    change p.normalize.coeffs.length - 1 = pas.length
    rw [hpcoeffs]
    simp
  have hqDegree : q.natDegree = qas.length := by
    change q.normalize.coeffs.length - 1 = qas.length
    rw [hqcoeffs]
    simp
  let base := shift 1 (0 : DensePolynomial K) + scale pa q
  have hbase : base = scale pa q := by
    dsimp only [base]
    rw [shift, if_pos (show (0 : DensePolynomial K).isZero = true by rfl),
      zero_add_normalize, normalize_scale]
  have hbaseCoeffs : base.coeffs =
      pa * qa :: qas.map (pa * ·) := by
    rw [hbase, scale_coeffs_of_ne_zero hpa, hqcoeffs]
    rfl
  have hbaseBound : q.normalize.coeffs.length ≤ base.coeffs.length := by
    rw [hqcoeffs, hbaseCoeffs]
    simp
  obtain ⟨out, hout, houtLength⟩ :=
    foldl_mulStep_preserves_leading_shape q pas base (pa * qa)
      (qas.map (pa * ·)) hbaseCoeffs (mul_ne_zero_direct hpa hqa) hbaseBound
  have hmul : p * q =
      pas.foldl (fun value a => shift 1 value + scale a q) base := by
    rw [show p * q = mulPolynomial p q from rfl, mulPolynomial]
    rw [← foldl_mulStep_dropWhile_zero q p.coeffs]
    change p.normalize.coeffs.foldl
        (fun value a => shift 1 value + scale a q) 0 = _
    rw [hpcoeffs]
    rfl
  refine ⟨out, ?_, ?_⟩
  · rw [hmul, hout, hpLeading, hqLeading]
  · rw [houtLength, List.length_map, hpDegree, hqDegree]
    exact Nat.add_comm _ _

theorem natDegree_mul {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  obtain ⟨out, hcoeffs, hout⟩ := mul_coeffs_shape hp hq
  have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
    mul_ne_zero_direct (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
  have hnormalized : (p * q).normalize.coeffs =
      p.leadingCoeff * q.leadingCoeff :: out := by
    change (p * q).coeffs.dropWhile (· = 0) = _
    rw [hcoeffs, List.dropWhile_cons_of_neg (by simp [hleading])]
  change (p * q).normalize.coeffs.length - 1 = _
  rw [hnormalized]
  simp [hout]

theorem leadingCoeff_mul {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  obtain ⟨out, hcoeffs, _⟩ := mul_coeffs_shape hp hq
  have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
    mul_ne_zero_direct (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
  change (p * q).normalize.coeffs.headD 0 = _
  change ((p * q).coeffs.dropWhile (· = 0)).headD 0 = _
  rw [hcoeffs, List.dropWhile_cons_of_neg (by simp [hleading])]
  rfl

theorem normalize_mul (p q : DensePolynomial K) :
    (p * q).normalize = p * q := by
  by_cases hp : p.isZero = true
  · rw [mul_eq_zero_of_isZero_left hp]
    rfl
  · have hpFalse : p.isZero = false := Bool.eq_false_of_not_eq_true hp
    by_cases hq : q.isZero = true
    · rw [mul_eq_zero_of_isZero_right hq]
      rfl
    · have hqFalse : q.isZero = false := Bool.eq_false_of_not_eq_true hq
      obtain ⟨out, hcoeffs, _⟩ := mul_coeffs_shape hpFalse hqFalse
      have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
        mul_ne_zero_direct (leadingCoeff_ne_zero hpFalse)
          (leadingCoeff_ne_zero hqFalse)
      apply ext
      change (p * q).coeffs.dropWhile (· = 0) = (p * q).coeffs
      rw [hcoeffs, List.dropWhile_cons_of_neg (by simp [hleading])]

/-- The finite dense Horner product of two nonzero polynomials is nonzero.
This proof tracks its leading coefficient directly and does not pass through
Mathlib's sparse-polynomial finite-support representation. -/
theorem isZero_mul_eq_false {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false := by
  obtain ⟨pa, pas, hpcoeffs, hpa⟩ :
      ∃ pa pas, p.normalize.coeffs = pa :: pas ∧ pa ≠ 0 := by
    cases hpcase : p.normalize.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hpcase, List.headD_cons] using hlead
  obtain ⟨qa, qas, hqcoeffs, hqa⟩ :
      ∃ qa qas, q.normalize.coeffs = qa :: qas ∧ qa ≠ 0 := by
    cases hqcase : q.normalize.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hqcase, List.headD_cons] using hlead
  have hbase : HasLeadingAtLeast q
      (shift 1 (0 : DensePolynomial K) + scale pa q) := by
    rw [show shift 1 (0 : DensePolynomial K) + scale pa q = scale pa q by
      rw [shift, if_pos (show (0 : DensePolynomial K).isZero = true by rfl),
        zero_add_normalize, normalize_scale]]
    refine ⟨pa * qa, qas.map (pa * ·), ?_, mul_ne_zero_direct hpa hqa, ?_⟩
    · rw [scale_coeffs_of_ne_zero hpa, hqcoeffs]
      rfl
    · rw [scale_coeffs_of_ne_zero hpa, List.length_map]
  have hfold := foldl_mulStep_preserves_hasLeadingAtLeast q pas hbase
  rcases hfold with ⟨a, as, hcoeffs, ha, _⟩
  have hmul : p * q =
      pas.foldl (fun value a => shift 1 value + scale a q)
        (shift 1 0 + scale pa q) := by
    rw [show p * q = mulPolynomial p q from rfl, mulPolynomial]
    rw [← foldl_mulStep_dropWhile_zero q p.coeffs]
    change p.normalize.coeffs.foldl
        (fun value a => shift 1 value + scale a q) 0 = _
    rw [hpcoeffs]
    rfl
  rw [hmul]
  exact isZero_false_of_coeffs_cons hcoeffs ha

private theorem eval_foldl_mulPolynomial (x : K) (q : DensePolynomial K)
    (cs : List K) (acc : DensePolynomial K) :
    (cs.foldl (fun value a => shift 1 value + scale a q) acc).eval x =
      cs.foldl (fun value a => value * x + a * q.eval x) (acc.eval x) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, eval_add, eval_shift, eval_scale]
      simp [pow_one]

omit [DecidableEq K] in
private theorem foldl_scaled_horner (x c : K) (cs : List K) (acc : K) :
    cs.foldl (fun value a => value * x + a * c) (acc * c) =
      cs.foldl (fun value a => value * x + a) acc * c := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [show acc * c * x + a * c = (acc * x + a) * c by ring1, ih]

@[simp] theorem eval_mul (p q : DensePolynomial K) (x : K) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [show p * q = mulPolynomial p q from rfl, mulPolynomial,
    eval_foldl_mulPolynomial]
  rw [eval_zero]
  simpa only [zero_mul, eval, evalCoeffs] using
    foldl_scaled_horner x (q.eval x) p.coeffs 0

/-- Finite output of dense long division. -/
structure DivResult (p q : DensePolynomial K) where
  quotient : DensePolynomial K
  remainder : DensePolynomial K
  steps : ℕ

/-- Fuel-bounded long division.  The initial fuel is coefficient-computable;
each call consumes one natural number regardless of coefficient values. -/
def divLoop : ℕ → (p q quotient : DensePolynomial K) → DivResult p q
  := Nat.rec
    (fun p _q quotient => ⟨quotient, p, 0⟩)
    (fun _ recursive p q quotient =>
      if q.isZero || p.isZero || p.natDegree < q.natDegree then
        ⟨quotient, p, 0⟩
      else
        let term := leadQuotient p q
        let next := cancelLead p q
        let result := recursive next q (quotient + term)
        ⟨result.quotient, result.remainder, result.steps + 1⟩)

@[simp] theorem divLoop_zero (p q quotient : DensePolynomial K) :
    divLoop 0 p q quotient = ⟨quotient, p, 0⟩ := rfl

theorem divLoop_succ (fuel : Nat) (p q quotient : DensePolynomial K) :
    divLoop (fuel + 1) p q quotient =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then
        ⟨quotient, p, 0⟩
      else
        let term := leadQuotient p q
        let next := cancelLead p q
        let result := divLoop fuel next q (quotient + term)
        ⟨result.quotient, result.remainder, result.steps + 1⟩ := rfl

theorem divLoop_succ_remainder
    (fuel : Nat) (p q quotient : DensePolynomial K) :
    (divLoop (fuel + 1) p q quotient).remainder =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then p
      else (divLoop fuel (cancelLead p q) q
        (quotient + leadQuotient p q)).remainder := by
  rw [divLoop_succ]
  split <;> rfl

theorem divLoop_succ_remainder_degreeCount
    (fuel : Nat) (p q quotient : DensePolynomial K) :
    (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then p.degreeCount
      else (divLoop fuel (cancelLead p q) q
        (quotient + leadQuotient p q)).remainder.degreeCount := by
  by_cases stopping :
      (q.isZero || p.isZero || p.natDegree < q.natDegree) = true
  · rw [if_pos stopping]
    apply congrArg degreeCount
    have remainder := divLoop_succ_remainder fuel p q quotient
    rw [if_pos stopping] at remainder
    exact remainder
  · rw [if_neg stopping]
    apply congrArg degreeCount
    have remainder := divLoop_succ_remainder fuel p q quotient
    rw [if_neg stopping] at remainder
    exact remainder

/-- Executable Euclidean division with a displayed finite fuel bound. -/
def divMod (p q : DensePolynomial K) : DivResult p q :=
  let result := divLoop (p.degreeCount + 1) p.normalize q.normalize 0
  ⟨result.quotient, result.remainder, result.steps⟩

/-- Long division stops immediately when the dividend has smaller degree than
the divisor.  In particular, its quotient is zero and its remainder is the
normalized dividend. -/
theorem divMod_of_natDegree_lt {p q : DensePolynomial K}
    (hdegree : p.natDegree < q.natDegree) :
    (divMod p q).quotient = 0 ∧
      (divMod p q).remainder = p.normalize := by
  simp [divMod, divLoop_succ, hdegree]

/-- At every fuel depth, negating a nonzero divisor leaves the long-division
remainder unchanged.  Quotients are deliberately generalized away because
the remainder recursion does not inspect them. -/
theorem divLoop_remainder_neg_right (fuel : ℕ) (p q quotientNeg quotient : DensePolynomial K)
    (hq : q.isZero = false) :
    (divLoop fuel p (-q) quotientNeg).remainder =
      (divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotientNeg quotient with
  | zero => rfl
  | succ fuel ih =>
      rw [divLoop_succ, divLoop_succ]
      simp only [isZero_neg, natDegree_neg]
      split
      · rfl
      · dsimp only
        rw [cancelLead_neg_right p q hq]
        exact ih (cancelLead p q)
          (quotientNeg + leadQuotient p (-q))
          (quotient + leadQuotient p q)

/-- Negating both inputs negates the finite long-division remainder at every
fuel depth. -/
theorem divLoop_remainder_neg_both
    (fuel : ℕ) (p q quotientNeg quotient : DensePolynomial K)
    (pNormalized : p.normalize = p) :
    (divLoop fuel (-p) (-q) quotientNeg).remainder =
      -(divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotientNeg quotient with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [divLoop_succ, divLoop_succ]
      simp only [isZero_neg, natDegree_neg]
      split
      · rfl
      · dsimp only
        rw [cancelLead_neg_both p q pNormalized]
        exact inductionHypothesis (cancelLead p q)
          (quotientNeg + leadQuotient (-p) (-q))
          (quotient + leadQuotient p q)
          (normalize_cancelLead p q)

/-- Executable division has the same remainder after negating a nonzero
divisor. -/
theorem divMod_remainder_neg_right (p q : DensePolynomial K)
    (hq : q.isZero = false) :
    (divMod p (-q)).remainder = (divMod p q).remainder := by
  have h := divLoop_remainder_neg_right (p.degreeCount + 1) p.normalize q.normalize 0 0
    (by simpa using hq)
  rw [divMod, divMod, normalize_neg]
  rw [neg_normalize q] at h
  exact h

/-- Simultaneously negating both inputs negates the executable division
remainder. -/
theorem divMod_remainder_neg_both_direct (p q : DensePolynomial K) :
    (divMod (-p) (-q)).remainder = -(divMod p q).remainder := by
  have result := divLoop_remainder_neg_both
    (p.degreeCount + 1) p.normalize q.normalize 0 0
      (normalize_normalize p)
  rw [divMod, divMod, degreeCount_neg, normalize_neg, normalize_neg,
    ← neg_normalize p, ← neg_normalize q]
  exact result

theorem divLoop_remainder_normalized (fuel : ℕ)
    (p q quotient : DensePolynomial K) (hp : p.normalize = p) :
    (divLoop fuel p q quotient).remainder.normalize =
      (divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotient with
  | zero => exact hp
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · exact hp
      · dsimp only
        exact ih (cancelLead p q) (quotient + leadQuotient p q)
          (normalize_cancelLead p q)

private theorem divLoop_remainder_degreeCount_le
    (fuel : ℕ) (p q quotient : DensePolynomial K)
    (pNormalized : p.normalize = p) (qNormalized : q.normalize = q) :
    (divLoop fuel p q quotient).remainder.degreeCount ≤ p.degreeCount := by
  induction fuel generalizing p quotient with
  | zero => exact le_rfl
  | succ fuel inductionHypothesis =>
      calc
        (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
            (if q.isZero || p.isZero || p.natDegree < q.natDegree then
              p.degreeCount
            else (divLoop fuel (cancelLead p q) q
              (quotient + leadQuotient p q)).remainder.degreeCount) :=
          divLoop_succ_remainder_degreeCount fuel p q quotient
        _ ≤ p.degreeCount := by
          split
          · exact le_rfl
          · rename_i continuing
            have qNonzero : q.isZero = false := by
              cases qZero : q.isZero with
              | false => rfl
              | true => exact (continuing (by simp [qZero])).elim
            have pNonzero : p.isZero = false := by
              cases pZero : p.isZero with
              | false => rfl
              | true => exact (continuing (by simp [qNonzero, pZero])).elim
            have degree : q.natDegree ≤ p.natDegree := by
              by_cases smaller : p.natDegree < q.natDegree
              · exact (continuing
                  (by simp [qNonzero, pNonzero, smaller])).elim
              · exact Nat.le_of_not_gt smaller
            exact (inductionHypothesis (cancelLead p q)
              (quotient + leadQuotient p q)
              (normalize_cancelLead p q)).trans
                (Nat.le_of_lt (cancelLead_degreeCount_lt pNonzero
                  qNonzero pNormalized qNormalized degree))

/-- Executable division never returns a remainder with more normalized
coefficient slots than its dividend. -/
theorem divMod_remainder_degreeCount_le (p q : DensePolynomial K) :
    (divMod p q).remainder.degreeCount ≤ p.degreeCount := by
  have bound := divLoop_remainder_degreeCount_le (p.degreeCount + 1)
    p.normalize q.normalize 0 (normalize_normalize p) (normalize_normalize q)
  simpa only [divMod, degreeCount_normalize] using bound

@[simp] theorem divMod_remainder_normalize (p q : DensePolynomial K) :
    (divMod p q).remainder.normalize = (divMod p q).remainder := by
  exact divLoop_remainder_normalized (p.degreeCount + 1) p.normalize q.normalize 0
    (normalize_normalize p)

theorem divLoop_steps_le (fuel : ℕ) (p q quotient : DensePolynomial K) :
    (divLoop fuel p q quotient).steps ≤ fuel := by
  induction fuel generalizing p quotient with
  | zero => simp
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · simp
      · dsimp only
        exact Nat.add_le_add_right
          (ih (p := cancelLead p q) (quotient := quotient + leadQuotient p q)) 1

/-- Exact evaluation invariant for every finite long-division run. -/
theorem divLoop_eval_equation (fuel : ℕ) (p q quotient : DensePolynomial K) (x : K) :
    let result := divLoop fuel p q quotient
    result.remainder.eval x + q.eval x * result.quotient.eval x =
      p.eval x + q.eval x * quotient.eval x := by
  induction fuel generalizing p quotient with
  | zero => simp
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · simp
      · dsimp only
        rw [ih, eval_cancelLead, eval_add]
        ring1

theorem divMod_steps_le (p q : DensePolynomial K) :
    (divMod p q).steps ≤ p.degreeCount + 1 :=
  by simpa [divMod] using divLoop_steps_le (p.degreeCount + 1) p.normalize q.normalize 0

/-- The executable quotient and remainder satisfy the exact evaluation
identity at every field element. -/
theorem divMod_eval_equation (p q : DensePolynomial K) (x : K) :
    (divMod p q).remainder.eval x + q.eval x * (divMod p q).quotient.eval x =
      p.eval x := by
  have h := divLoop_eval_equation (p.degreeCount + 1) p.normalize q.normalize 0 x
  simpa only [divMod, eval_normalize, eval_zero, mul_zero, add_zero] using h

private theorem divLoop_remainder_degreeCount_lt
    (fuel : ℕ) (p q quotient : DensePolynomial K)
    (hq : q.isZero = false) (hpNormalized : p.normalize = p)
    (hqNormalized : q.normalize = q) (hfuel : p.degreeCount < fuel) :
    (divLoop fuel p q quotient).remainder.degreeCount < q.degreeCount := by
  induction fuel generalizing p quotient with
  | zero => omega
  | succ fuel ih =>
      calc
        (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
            (if q.isZero || p.isZero || p.natDegree < q.natDegree then
              p.degreeCount
            else (divLoop fuel (cancelLead p q) q
              (quotient + leadQuotient p q)).remainder.degreeCount) :=
          divLoop_succ_remainder_degreeCount fuel p q quotient
        _ < q.degreeCount := by
          by_cases hp : p.isZero = true
          · simp only [hq, hp, Bool.false_or, Bool.true_or, if_true]
            rw [degreeCount_eq_zero_of_isZero hp]
            exact degreeCount_pos_of_isZero_false hq
          · have hpFalse : p.isZero = false := by simpa using hp
            by_cases hdegree : p.natDegree < q.natDegree
            · simp only [hq, hpFalse, Bool.false_or, decide_eq_true_eq,
                hdegree, if_pos]
              have hpCount := natDegree_add_one_eq_degreeCount hpFalse
              have hqCount := natDegree_add_one_eq_degreeCount hq
              omega
            · simp only [hq, hpFalse, Bool.false_or, decide_eq_true_eq,
                hdegree, if_false]
              apply ih (p := cancelLead p q)
              · exact normalize_cancelLead p q
              · have hcancel := cancelLead_degreeCount_lt hpFalse hq
                  hpNormalized hqNormalized (Nat.le_of_not_gt hdegree)
                omega

theorem divMod_remainder_degreeCount_lt (p q : DensePolynomial K)
    (hq : q.isZero = false) :
    (divMod p q).remainder.degreeCount < q.degreeCount := by
  have h := divLoop_remainder_degreeCount_lt (p.degreeCount + 1)
      p.normalize q.normalize 0 (by simpa using hq)
      (normalize_normalize p) (normalize_normalize q) (by
        rw [degreeCount_normalize]
        exact Nat.lt_succ_self p.degreeCount)
  simpa only [divMod, degreeCount_normalize] using h

end DensePolynomial

end RFAP.ComputablePolynomial
