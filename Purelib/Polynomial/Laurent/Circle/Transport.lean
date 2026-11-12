module

public import Purelib.Polynomial.Laurent.Circle
public import Purelib.Polynomial.Laurent.Transport
public import Purelib.Polynomial.Winding.Circle.Transport
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Data.Gaussian.Power
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent circle transports of original Laurent symbols

Each operation preserves the original ordered raw expression and computes
its own normalization and original circle comparison. Polynomial reversal
and coefficient conjugation determine the winding relation only after both
independent chart-event computations have been retained.
-/

public section

namespace Purelib.Polynomial.Laurent.Circle.Transport

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Polynomial.Laurent.Basic (LaurentPolynomial)
open Purelib.Polynomial.Laurent.Normalization (Normalized ZeroSymbol)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Gaussian.Basic (Canonical)

/-- A coordinate shift preserves the same original polynomial quadrance on the unit circle. -/
private theorem shifted_norm (polynomial : CoefficientPolynomial)
    (exponent : Nat) (point : Canonical) (unit : point.normSq = 1) :
    Norm.Basic.normSq ((DensePolynomial.shift exponent polynomial).eval point) =
      Norm.Basic.normSq (polynomial.eval point) := by
  rewrite [DensePolynomial.eval_shift, Norm.Basic.normSq_mul, Purelib.Data.Gaussian.Power.normSq_pow,
    Norm.Basic.normSq_eq_canonical point, unit, one_pow, Rat.Fraction.Field.mul_one_direct]
  rfl

/-- The actual coefficient-conjugate normalization retains the original complete-circle payment. -/
@[expose] def conjugateMargin {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.conjugate) :
    Certificate target.polynomial :=
  { bound := margin.bound
    positive := margin.positive
    lower := by
      intro point unit
      rewrite [normalized.conjugate_polynomial target]
      exact margin.conjugate.lower point unit }

/-- The actual reversed normalization retains the original complete-circle payment and zero-root compensation. -/
@[expose] def reverseMargin {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.reverse) :
    Certificate target.polynomial :=
  { bound := margin.bound
    positive := margin.positive
    lower := by
      intro point unit
      have same := congrArg (fun polynomial => Norm.Basic.normSq (polynomial.eval point))
        (normalized.reverse_commonShift target)
      rewrite [shifted_norm _ _ point unit, shifted_norm _ _ point unit] at same
      rewrite [same]
      exact margin.reversed.lower point unit }

/-- The actual adjoint retains the original complete-circle payment without an intermediate normalization. -/
@[expose] def adjointMargin {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.adjoint) :
    Certificate target.polynomial :=
  { bound := margin.bound
    positive := margin.positive
    lower := by
      intro point unit
      have same := congrArg (fun polynomial => Norm.Basic.normSq (polynomial.eval point))
        (normalized.adjoint_commonShift target)
      rewrite [shifted_norm _ _ point unit, shifted_norm _ _ point unit] at same
      rewrite [same]
      exact margin.conjugate.reversed.lower point unit }

/-- Independent coefficient-conjugate numerator windings agree for the actual original normalized tables. -/
theorem conjugate_raw {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.conjugate)
    (sourcePaths : Boundary.Substitutions normalized.polynomial)
    (targetPaths : Boundary.Substitutions target.polynomial) :
    Winding.Circle.raw targetPaths = Winding.Circle.raw sourcePaths := by
  let conjugatePaths := Boundary.Substitutions.prepare (Conjugate.polynomial normalized.polynomial)
  have same := Winding.Circle.Comparison.raw_eq_of_eval_eq margin.conjugate conjugatePaths targetPaths
    (fun point _ => congrArg (fun polynomial => polynomial.eval point) (normalized.conjugate_polynomial target))
  exact same.trans (Winding.Circle.raw_conjugate margin sourcePaths conjugatePaths)

/-- The independently computed reversed numerator winding retains both actual pole orders.

The degree powers in the exact common-shift identity cancel against the
original reciprocal winding complement. Extra original zero roots therefore
remain in the actual numerator and denominator computations until cancellation.
-/
theorem reverse_raw {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.reverse)
    (sourcePaths : Boundary.Substitutions normalized.polynomial)
    (targetPaths : Boundary.Substitutions target.polynomial) :
    Winding.Circle.raw targetPaths = 4 * ((normalized.poleOrder : Int) + (target.poleOrder : Int)) -
      Winding.Circle.raw sourcePaths := by
  let reciprocalPaths := Boundary.Substitutions.prepare (Reciprocal.reversed normalized.polynomial)
  let leftPaths := Boundary.Substitutions.prepare
    (DensePolynomial.shift normalized.polynomial.natDegree target.polynomial)
  let rightPaths := Boundary.Substitutions.prepare
    (DensePolynomial.shift (normalized.poleOrder + target.poleOrder) (Reciprocal.reversed normalized.polynomial))
  have same := Winding.Circle.Comparison.raw_eq_of_eval_eq
    ((reverseMargin normalized margin target).shift normalized.polynomial.natDegree) leftPaths rightPaths
    (fun point _ => congrArg (fun polynomial => polynomial.eval point) (normalized.reverse_commonShift target).symm)
  have left := Winding.Circle.raw_shift (reverseMargin normalized margin target)
    targetPaths normalized.polynomial.natDegree leftPaths
  have right := Winding.Circle.raw_shift margin.reversed reciprocalPaths
    (normalized.poleOrder + target.poleOrder) rightPaths
  have reciprocal := Winding.Circle.raw_reversed margin sourcePaths reciprocalPaths
  rewrite [reciprocal] at right
  omega0

/-- The independently computed adjoint numerator winding retains both actual pole orders.

The same conjugate and reciprocal polynomial winding transports apply to
the exact common-shift identity. No intermediate Laurent expression or
normalization is executed by this comparison.
-/
theorem adjoint_raw {source : LaurentPolynomial} (normalized : Normalized source)
    (margin : Certificate normalized.polynomial) (target : Normalized source.adjoint)
    (sourcePaths : Boundary.Substitutions normalized.polynomial)
    (targetPaths : Boundary.Substitutions target.polynomial) :
    Winding.Circle.raw targetPaths = 4 * ((normalized.poleOrder : Int) + (target.poleOrder : Int)) -
      Winding.Circle.raw sourcePaths := by
  let conjugatePaths := Boundary.Substitutions.prepare (Conjugate.polynomial normalized.polynomial)
  let reciprocalPaths := Boundary.Substitutions.prepare
    (Reciprocal.reversed (Conjugate.polynomial normalized.polynomial))
  let leftPaths := Boundary.Substitutions.prepare
    (DensePolynomial.shift normalized.polynomial.natDegree target.polynomial)
  let rightPaths := Boundary.Substitutions.prepare
    (DensePolynomial.shift (normalized.poleOrder + target.poleOrder)
      (Reciprocal.reversed (Conjugate.polynomial normalized.polynomial)))
  have same := Winding.Circle.Comparison.raw_eq_of_eval_eq
    ((adjointMargin normalized margin target).shift normalized.polynomial.natDegree) leftPaths rightPaths
    (fun point _ => congrArg (fun polynomial => polynomial.eval point) (normalized.adjoint_commonShift target).symm)
  have left := Winding.Circle.raw_shift (adjointMargin normalized margin target)
    targetPaths normalized.polynomial.natDegree leftPaths
  have right := Winding.Circle.raw_shift margin.conjugate.reversed reciprocalPaths
    (normalized.poleOrder + target.poleOrder) rightPaths
  have reciprocal := Winding.Circle.raw_reversed margin.conjugate conjugatePaths reciprocalPaths
  have conjugate := Winding.Circle.raw_conjugate margin sourcePaths conjugatePaths
  rewrite [Conjugate.natDegree, conjugate] at reciprocal
  rewrite [reciprocal] at right
  omega0

set_option genInjectivity false in
/-- The two fixed orientations of an original circle-winding transport. -/
inductive Orientation where
  /-- The independently computed winding is preserved. -/
  | preserving
  /-- The independently computed winding is negated. -/
  | reversing

constructive_injectivity Orientation

/-- The integer multiplier of one retained finite orientation. -/
@[expose] def Orientation.value : Orientation → Int
  | .preserving => 1
  | .reversing => -1

variable {source : LaurentPolynomial} {normalized : Normalized source}
variable {sourcePaths : Boundary.Substitutions normalized.polynomial}
variable {sourceClearance : Boundary.Clearance sourcePaths}

/-- The original independent Laurent phase reads the original numerator raw value minus its actual pole power. -/
private theorem winding_raw (comparison : Circle.Comparison normalized sourcePaths sourceClearance) :
    4 * comparison.reading.winding = Winding.Circle.raw sourcePaths - 4 * (normalized.poleOrder : Int) :=
  (comparison.reading.raw_eq.symm.trans
    (Purelib.RationalFunctions.Winding.Circle.raw_eq_sub comparison.paths.quotient
      sourceClearance comparison.paths.denominatorClearance)).trans
    (congrArg₂ (fun numerator denominator : Int => numerator - denominator)
      (Eq.refl _) comparison.paths.denominator_raw)

/-- Actual coefficient-conjugate Laurent comparisons have the same independent winding. -/
private theorem conjugate_winding (original : Circle.Comparison normalized sourcePaths sourceClearance)
    (target : Normalized source.conjugate) (paths : Boundary.Substitutions target.polynomial)
    (clearance : Boundary.Clearance paths) (comparison : Circle.Comparison target paths clearance) :
    comparison.reading.winding = original.reading.winding := by
  have first := winding_raw original
  have second := winding_raw comparison
  have raw := conjugate_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
  have poles := normalized.conjugate_poleOrder target
  omega0

/-- Actual reversed Laurent comparisons have opposite independent winding. -/
private theorem reverse_winding (original : Circle.Comparison normalized sourcePaths sourceClearance)
    (target : Normalized source.reverse) (paths : Boundary.Substitutions target.polynomial)
    (clearance : Boundary.Clearance paths) (comparison : Circle.Comparison target paths clearance) :
    comparison.reading.winding = -original.reading.winding := by
  have first := winding_raw original
  have second := winding_raw comparison
  have raw := reverse_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
  omega0

/-- Actual adjoint Laurent comparisons have opposite independent winding. -/
private theorem adjoint_winding (original : Circle.Comparison normalized sourcePaths sourceClearance)
    (target : Normalized source.adjoint) (paths : Boundary.Substitutions target.polynomial)
    (clearance : Boundary.Clearance paths) (comparison : Circle.Comparison target paths clearance) :
    comparison.reading.winding = -original.reading.winding := by
  have first := winding_raw original
  have second := winding_raw comparison
  have raw := adjoint_raw normalized original.polynomial.margin.toCertificate target sourcePaths paths
  omega0

set_option genInjectivity false in
/-- An actual transformed Laurent comparison retaining its original source and fixed orientation.

The actual raw target, original normalization, complete numerator paths,
quantitative payment and independent original circle constructor are retained
once. The winding relation is proved between the two actual computations;
neither a target integer nor a root count is an input to the construction.
-/
structure Comparison (original : Circle.Comparison normalized sourcePaths sourceClearance)
    (target : LaurentPolynomial) (orientation : Orientation) where
  /-- The once-computed actual ordered raw target expression. -/
  symbol : LaurentPolynomial
  /-- The target retains the specified original raw operation. -/
  symbol_eq : symbol = target
  /-- The original preparation's actual retained nonzero normalization. -/
  normalized : Normalized symbol
  /-- The same computed raw target succeeds in the original total preparation. -/
  normalized_eq : symbol.prepare = .normalized normalized
  /-- The once-computed actual numerator chart substitutions. -/
  paths : Boundary.Substitutions normalized.polynomial
  /-- The original chart constructor consumes the same retained polynomial. -/
  paths_eq : paths = Boundary.Substitutions.prepare normalized.polynomial
  /-- The original whole-circle payment transported to the same actual target polynomial. -/
  margin : Certificate normalized.polynomial
  /-- The actual target certificate retains the complete original source payment. -/
  margin_bound : margin.bound = original.polynomial.margin.toCertificate.bound
  /-- Both actual target charts consume the same stored margin. -/
  clearance : Boundary.Clearance paths
  /-- The original chart-clearance constructor consumes these same cached inputs. -/
  clearance_eq : clearance = margin.onBoundary paths
  /-- The target's actual independent original phase and complete multiplicity inventory. -/
  result : Circle.Comparison normalized paths clearance
  /-- The same original automatic comparison consumes these retained target caches. -/
  result_eq : result = Circle.Comparison.prepare normalized paths clearance
  /-- The two actual independent windings satisfy this fixed finite orientation. -/
  winding_eq : result.reading.winding = orientation.value * original.reading.winding

constructive_injectivity Comparison

/-- Retain the original nonzero preparation of an actual target whose zero obstruction is impossible. -/
private def normalize (symbol : LaurentPolynomial) (excluded : ZeroSymbol symbol → False) : Normalized symbol :=
  match symbol.prepare with
  | .zero obstruction => False.elim (excluded obstruction)
  | .normalized retained => retained

/-- The retained normalization is the actual success branch of the same original target preparation. -/
private theorem normalize_eq (symbol : LaurentPolynomial) (excluded : ZeroSymbol symbol → False) :
    symbol.prepare = .normalized (normalize symbol excluded) := by
  unfold normalize
  split
  · exact (excluded ‹_›).elim
  · assumption

/-- Materialize one actual target's original paths, clearance and independent circle comparison exactly once. -/
private def complete (original : Circle.Comparison normalized sourcePaths sourceClearance)
    {target : LaurentPolynomial} {orientation : Orientation} (symbol : LaurentPolynomial) (symbol_eq : symbol = target)
    (retained : Normalized symbol) (retained_eq : symbol.prepare = .normalized retained)
    (margin : Certificate retained.polynomial)
    (payment : margin.bound = original.polynomial.margin.toCertificate.bound)
    (winding : ∀ (paths : Boundary.Substitutions retained.polynomial) (clearance : Boundary.Clearance paths)
      (result : Circle.Comparison retained paths clearance),
        result.reading.winding = orientation.value * original.reading.winding) :
    Comparison original target orientation :=
  let paths := Boundary.Substitutions.prepare retained.polynomial
  let clearance := margin.onBoundary paths
  let result := Circle.Comparison.prepare retained paths clearance
  { symbol, symbol_eq, normalized := retained, normalized_eq := retained_eq
    paths, paths_eq := rfl, margin, margin_bound := payment, clearance, clearance_eq := rfl
    result, result_eq := rfl, winding_eq := winding paths clearance result }

namespace Comparison

/-- Construct the actual coefficient-conjugate comparison with preserved independent winding.

The raw map and original normalization each execute once. The same source
margin supplies the target's complete original chart and argument-principle
comparison, without a new boundary search or supplied target reading.
-/
def conjugate (original : Circle.Comparison normalized sourcePaths sourceClearance) :
    Comparison original source.conjugate .preserving :=
  let symbol := source.conjugate
  let excluded : ZeroSymbol symbol → False := by
    intro obstruction
    exact normalized.conjugate.zero_impossible obstruction
  let retained := normalize symbol excluded
  let margin := conjugateMargin normalized original.polynomial.margin.toCertificate retained
  complete original symbol rfl retained (normalize_eq symbol excluded) margin rfl (by
    intro paths clearance result
    exact (conjugate_winding original retained paths clearance result).trans
      (show original.reading.winding = Orientation.preserving.value * original.reading.winding by
        change _ = 1 * _
        ring1))

/-- Construct the actual exponent-reversed comparison with opposite independent winding.

The original target expression, normalization, numerator substitutions and
same-payment margin are retained before the original independent phase and
multiplicity comparison is run. All actual zero and pole powers remain.
-/
def reverse (original : Circle.Comparison normalized sourcePaths sourceClearance) :
    Comparison original source.reverse .reversing :=
  let symbol := source.reverse
  let excluded : ZeroSymbol symbol → False := by
    intro obstruction
    exact normalized.reverse.zero_impossible obstruction
  let retained := normalize symbol excluded
  let margin := reverseMargin normalized original.polynomial.margin.toCertificate retained
  complete original symbol rfl retained (normalize_eq symbol excluded) margin rfl (by
    intro paths clearance result
    exact (reverse_winding original retained paths clearance result).trans
      (show -original.reading.winding = Orientation.reversing.value * original.reading.winding by
        change _ = (-1) * _
        ring1))

/-- Construct the actual combined-adjoint comparison in one raw traversal and one original normalization.

The target retains its independent original circle constructor and the same
complete source payment. Its opposite winding follows from the proved raw
transports rather than any chosen target integer or geometric root labels.
-/
def adjoint (original : Circle.Comparison normalized sourcePaths sourceClearance) :
    Comparison original source.adjoint .reversing :=
  let symbol := source.adjoint
  let excluded : ZeroSymbol symbol → False := by
    intro obstruction
    exact normalized.adjoint.zero_impossible obstruction
  let retained := normalize symbol excluded
  let margin := adjointMargin normalized original.polynomial.margin.toCertificate retained
  complete original symbol rfl retained (normalize_eq symbol excluded) margin rfl (by
    intro paths clearance result
    exact (adjoint_winding original retained paths clearance result).trans
      (show -original.reading.winding = Orientation.reversing.value * original.reading.winding by
        change _ = (-1) * _
        ring1))

/-- The actual pole-minus-inside index follows the retained fixed orientation of the independent windings. -/
theorem index_eq {original : Circle.Comparison normalized sourcePaths sourceClearance}
    {target : LaurentPolynomial} {orientation : Orientation} (retained : Comparison original target orientation) :
    (retained.normalized.poleOrder : Int) - (retained.result.polynomial.inventory.insideCount : Int) =
      orientation.value *
        ((normalized.poleOrder : Int) - (original.polynomial.inventory.insideCount : Int)) := by
  rewrite [retained.result.index_eq_neg_winding, original.index_eq_neg_winding, retained.winding_eq]
  ring1

end Comparison

end Purelib.Polynomial.Laurent.Circle.Transport

end
