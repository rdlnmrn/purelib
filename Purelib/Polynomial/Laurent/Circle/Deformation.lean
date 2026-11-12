module

public import Purelib.Polynomial.Laurent.Path
public import Purelib.Polynomial.Laurent.Circle
public import Purelib.Data.Rat.SmallWidth
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Rounding.Floor.Bounds
public import Purelib.Data.Rat.Grid.Index
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Power
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite Laurent deformation under one whole-boundary margin

The original ordered coefficient-polynomial path may change its minimal
support, degree and root multiplicities. A single positive rational boundary
margin and the cached original Horner variation determine a finite mesh.
Every comparison uses that same margin and the original independent chart
winding; mesh certificates do not execute root isolation at proof vertices.
-/

namespace Purelib.Polynomial.Laurent.Circle.Deformation

open Purelib.Data
open Purelib.Data.Rat
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Basic (LaurentPolynomial)
open Path (Parameter)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order
open Purelib.Polynomial.Clearance.Circle (Certificate)

set_option genInjectivity false in
/-- A common positive original-symbol margin on every rational parameter and unit-boundary point. -/
public structure Uniform (path : Path) where
  /-- The same rational quadrance payment is retained throughout the entire cell. -/
  bound : Rational
  /-- The common whole-boundary payment is strictly positive. -/
  positive : 0 < bound
  /-- The original guarded symbol satisfies the payment at every rational cell parameter. -/
  lower : ∀ parameter, Parameter parameter → ∀ point : Canonical, point.normSq = 1 →
    bound ≤ Gaussian.Norm.Basic.normSq ((path.symbol parameter).eval point)

constructive_injectivity Uniform

namespace Uniform

/-- The same original margin certifies the common polynomialization, with no root or degree hypothesis. -/
public def atParameter {path : Path} (uniform : Uniform path) (prepared : Path.Prepared path)
    (parameter : Rational) (inside : Parameter parameter) :
    Certificate ((path.symbol parameter).polynomialize prepared.shift) :=
  { bound := uniform.bound
    positive := uniform.positive
    lower := by
      intro point unit
      have sufficient : (path.symbol parameter).rawShift ≤ prepared.shift := by
        rewrite [path.rawShift_symbol, prepared.shift_eq]
        exact Nat.le_refl _
      rewrite [(path.symbol parameter).eval_polynomialize prepared.shift sufficient point
        ((path.symbol parameter).definedAt_of_nonzero (Substitutions.unit_ne_zero unit)),
        Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow,
        Gaussian.Norm.Basic.normSq_eq_canonical, unit, one_pow, Rat.Fraction.Field.one_mul]
      exact uniform.lower parameter inside point unit }

end Uniform

set_option genInjectivity false in
/-- A computed finite deformation schedule using one cached original coefficient-path budget.

The width is the original shrinking-width payment and the positive interval
count is one above its reciprocal ceiling. These data certify a sufficient
finite proof schedule; chart or root constructors at every mesh vertex are
not retained as executable work.
-/
public structure Prepared {path : Path} (uniform : Uniform path) where
  /-- The once-prepared original coefficient path and its retained Horner folds. -/
  path : Path.Prepared path
  /-- The path cache is the complete original preparation result. -/
  path_eq : path = Path.prepare _
  /-- The computed positive width paying the original variation coefficient. -/
  width : Rational
  /-- The width uses the original finite rational shrinking-width constructor. -/
  width_eq : width = SmallWidth.shrinkingWidth path.coefficient (uniform.bound / 16)
  /-- The actual finite number of equal mesh intervals. -/
  intervals : Nat
  /-- The interval count is computed without caller-supplied sufficient fuel. -/
  intervals_eq : intervals = Rounding.Floor.ceilNat (1 / width) + 1

constructive_injectivity Prepared

/-- Prepare the original coefficient-path cache and its computed finite sufficient mesh once. -/
@[expose] public def prepare {path : Path} (uniform : Uniform path) : Prepared uniform :=
  let path := Path.prepare path
  let width := SmallWidth.shrinkingWidth path.coefficient (uniform.bound / 16)
  { path, path_eq := rfl, width, width_eq := rfl
    intervals := Rounding.Floor.ceilNat (1 / width) + 1, intervals_eq := rfl }

namespace Prepared

/-- The computed width is positive because its original coefficient and margin payments are valid. -/
public theorem width_positive {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    0 < prepared.width := by
  rewrite [prepared.width_eq]
  exact SmallWidth.shrinkingWidth_pos prepared.path.nonnegative
    (Field.div_pos_direct uniform.positive (by decide))

/-- The computed finite mesh always contains at least one interval. -/
public theorem intervals_positive {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    0 < prepared.intervals := by
  rewrite [prepared.intervals_eq]
  exact Nat.zero_lt_succ _

/-- The actual mesh width is the reciprocal of the same retained interval count. -/
@[expose] public def side {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) : Rational :=
  1 / (prepared.intervals : Rational)

/-- The actual finite mesh width is positive. -/
public theorem side_positive {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    0 < prepared.side :=
  Field.div_pos_direct (by decide) (Rat.Fraction.Cast.Order.natCast_pos_direct prepared.intervals_positive)

/-- The computed reciprocal ceiling makes each actual mesh side strictly smaller than the paid width. -/
public theorem side_lt_width {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    prepared.side < prepared.width := by
  change 1 / (prepared.intervals : Rational) < prepared.width
  rw [prepared.intervals_eq]
  exact Rounding.Floor.Bounds.reciprocal_ceilNat_lt prepared.width prepared.width_positive

/-- The same original variation coefficient pays every full mesh side below one sixteenth of the common margin. -/
public theorem variation_side {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    prepared.path.coefficient * prepared.side ^ 2 < uniform.bound / 16 := by
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt prepared.path.nonnegative
    (Field.div_pos_direct uniform.positive (by decide : (0 : Rational) < 16))
  rewrite [← prepared.width_eq] at paid
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct prepared.side_positive.le prepared.side_lt_width.le 2)
    prepared.path.nonnegative).trans_lt paid

/-- Two ordered parameters within one actual mesh side have close original common numerators. -/
public theorem close {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right)
    (ordered : left ≤ right) (distance : right - left ≤ prepared.side) :
    (uniform.atParameter prepared.path left leftInside).Close
      ((path.symbol right).polynomialize prepared.path.shift) := by
  intro point unit
  have variation := prepared.path.variation rightInside leftInside point
    ((Gaussian.Norm.Basic.normSq_eq_canonical point).trans unit) prepared.path.shift
  have square := Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct ordered) distance 2
  exact variation.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct square
    prepared.path.nonnegative).trans prepared.variation_side.le)

/-- Read an actual rational mesh vertex from its natural index and the same retained side. -/
@[expose] public def vertex {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    (index : Nat) : Rational := (index : Rational) * prepared.side

/-- The initial computed mesh vertex is the original parameter zero. -/
public theorem vertex_zero {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    prepared.vertex 0 = 0 := Rat.Fraction.Field.zero_mul_direct _

/-- The last actual mesh vertex is the original parameter one. -/
public theorem vertex_last {path : Path} {uniform : Uniform path} (prepared : Prepared uniform) :
    prepared.vertex prepared.intervals = 1 := by
  unfold vertex side
  rewrite [Rat.Fraction.Field.mul_comm]
  exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _
    (Rat.Fraction.Cast.Order.natCast_pos_direct prepared.intervals_positive).ne'

/-- Every bounded mesh vertex lies in the same original unit parameter cell. -/
public theorem vertex_inside {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {index : Nat} (bounded : index ≤ prepared.intervals) : Parameter (prepared.vertex index) := by
  constructor
  · exact Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index)) prepared.side_positive.le
  · exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Cast.Order.natCast_le_direct bounded) prepared.side_positive.le).trans_eq
        prepared.vertex_last

/-- A successive actual mesh vertex adds exactly the same retained side. -/
public theorem vertex_succ {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    (index : Nat) : prepared.vertex (index + 1) = prepared.vertex index + prepared.side := by
  unfold vertex
  rewrite [Nat.cast_succ]
  ring1

/-- Select the original finite grid cell containing a queried rational parameter. -/
@[expose] public def cell {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    (parameter : Rational) : Fin (prepared.intervals + 1) :=
  Grid.Index.coordinateIndex 0 prepared.side parameter prepared.intervals

/-- The original finite grid scan retains both actual bounds of the queried cell. -/
public theorem cell_contains {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {parameter : Rational} (inside : Parameter parameter) :
    prepared.vertex (prepared.cell parameter).val ≤ parameter ∧
      parameter ≤ prepared.vertex (prepared.cell parameter).val + prepared.side := by
  have upper : parameter ≤ 0 + (prepared.intervals : Rational) * prepared.side := by
    rewrite [Rat.Fraction.Field.zero_add]
    exact inside.2.trans_eq prepared.vertex_last.symm
  have contains := Grid.Index.coordinateIndex_mem prepared.side_positive prepared.intervals inside.1 upper
  constructor
  · have lower := contains.1
    change 0 + prepared.vertex (prepared.cell parameter).val ≤ parameter at lower
    rewrite [Rat.Fraction.Field.zero_add] at lower
    exact lower
  · have upper := contains.2
    change parameter ≤ 0 + (((prepared.cell parameter).val : Rational) + 1) * prepared.side at upper
    exact upper.trans_eq (by unfold vertex; ring1)

/-- The selected actual cell's lower endpoint is a valid parameter no farther than one retained side from its query. -/
public theorem cell_distance {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {parameter : Rational} (inside : Parameter parameter) :
    Parameter (prepared.vertex (prepared.cell parameter).val) ∧
      parameter - prepared.vertex (prepared.cell parameter).val ≤ prepared.side := by
  have contains := prepared.cell_contains inside
  constructor
  · exact prepared.vertex_inside (Nat.le_of_lt_succ (prepared.cell parameter).isLt)
  · exact (Arithmetic.sub_le_sub_right_direct contains.2
      (prepared.vertex (prepared.cell parameter).val)).trans_eq (by ring1)

/-- Every bounded proof-mesh vertex has the same original independent winding as its initial vertex.

Induction uses the same uniform margin at every adjacent comparison. The
intermediate substitutions occur only in this proof; no executable family
of root isolations or phase readings is constructed by the mesh schedule.
-/
public theorem vertex_raw_eq {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    (initial : Boundary.Substitutions ((path.symbol 0).polynomialize prepared.path.shift)) :
    ∀ index, index ≤ prepared.intervals →
      ∀ paths : Boundary.Substitutions ((path.symbol (prepared.vertex index)).polynomialize prepared.path.shift),
        Winding.Circle.raw paths = Winding.Circle.raw initial := by
  intro index
  induction index with
  | zero =>
      intro _ paths
      apply Winding.Circle.Comparison.raw_eq_of_eval_eq
        (uniform.atParameter prepared.path 0 ⟨by decide, by decide⟩) initial paths
      intro point _
      rewrite [prepared.vertex_zero]
      rfl
  | succ index inductionHypothesis =>
      intro bounded paths
      have previousBounded := Nat.le_trans (Nat.le_succ index) bounded
      have previousInside := prepared.vertex_inside previousBounded
      have nextInside := prepared.vertex_inside bounded
      let previous := Boundary.Substitutions.prepare
        ((path.symbol (prepared.vertex index)).polynomialize prepared.path.shift)
      have ordered : prepared.vertex index ≤ prepared.vertex (index + 1) := by
        rewrite [prepared.vertex_succ]
        have translated := Arithmetic.add_le_add_right_direct prepared.side_positive.le (prepared.vertex index)
        rewrite [Rat.Fraction.Field.zero_add, Rat.Fraction.Field.add_comm prepared.side] at translated
        exact translated
      have distance : prepared.vertex (index + 1) - prepared.vertex index ≤ prepared.side := by
        rewrite [prepared.vertex_succ, show prepared.vertex index + prepared.side - prepared.vertex index =
          prepared.side by ring1]
        exact Rat.Fraction.Order.Basic.le_refl _
      exact (Winding.Circle.Comparison.raw_eq_of_close
        (uniform.atParameter prepared.path _ previousInside) previous paths
        (prepared.close previousInside nextInside ordered distance)).trans
          (inductionHypothesis previousBounded previous)

/-- Every rational parameter has the same actual independent common-numerator winding as the initial parameter. -/
public theorem raw_eq_initial {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {parameter : Rational} (inside : Parameter parameter)
    (initial : Boundary.Substitutions ((path.symbol 0).polynomialize prepared.path.shift))
    (paths : Boundary.Substitutions ((path.symbol parameter).polynomialize prepared.path.shift)) :
    Winding.Circle.raw paths = Winding.Circle.raw initial := by
  let index := prepared.cell parameter
  let previous := Boundary.Substitutions.prepare
    ((path.symbol (prepared.vertex index.val)).polynomialize prepared.path.shift)
  have contains := prepared.cell_contains inside
  have distance := prepared.cell_distance inside
  exact (Winding.Circle.Comparison.raw_eq_of_close
    (uniform.atParameter prepared.path _ distance.1) previous paths
    (prepared.close distance.1 inside contains.1 distance.2)).trans
      (prepared.vertex_raw_eq initial index.val (Nat.le_of_lt_succ index.isLt) previous)

/-- Any two original rational cell parameters have equal independent common-numerator windings. -/
public theorem raw_eq {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right)
    (leftPaths : Boundary.Substitutions ((path.symbol left).polynomialize prepared.path.shift))
    (rightPaths : Boundary.Substitutions ((path.symbol right).polynomialize prepared.path.shift)) :
    Winding.Circle.raw rightPaths = Winding.Circle.raw leftPaths := by
  let initial := Boundary.Substitutions.prepare ((path.symbol 0).polynomialize prepared.path.shift)
  exact (prepared.raw_eq_initial rightInside initial rightPaths).trans
    (prepared.raw_eq_initial leftInside initial leftPaths).symm

end Prepared

namespace Uniform

/-- The common original-symbol margin pays its actual normalized polynomial without a new boundary search. -/
public def normalizedMargin {path : Path} (uniform : Uniform path)
    (parameter : Rational) (inside : Parameter parameter)
    (normalized : Normalization.Normalized (path.symbol parameter)) : Certificate normalized.polynomial :=
  { bound := uniform.bound, positive := uniform.positive
    lower := fun point unit => (uniform.lower parameter inside point unit).trans_eq
      (normalized.polynomial_normSq point unit).symm }

end Uniform

set_option genInjectivity false in
/-- One original parameter symbol with its actual cached normalization and independent circle comparison.

The whole-boundary margin excludes the zero preparation obstruction. The
same retained polynomialization supplies the original chart substitutions,
clearance, independent phase reading and complete root inventory exactly
once; it is not replaced by a common-shift table or a supplied final index.
-/
public structure Evaluation {path : Path} (uniform : Uniform path) (parameter : Rational)
    (inside : Parameter parameter) where
  /-- The original symbol's once-computed minimal polynomialization. -/
  normalized : Normalization.Normalized (path.symbol parameter)
  /-- The cache comes from the original typed preparation procedure on this same symbol. -/
  preparation_eq : (path.symbol parameter).prepare = .normalized normalized
  /-- The actual original numerator chart substitutions, materialized once. -/
  paths : Boundary.Substitutions normalized.polynomial
  /-- The paths are the original complete-boundary substitution result. -/
  paths_eq : paths = Boundary.Substitutions.prepare normalized.polynomial
  /-- The original common-symbol margin transported to the same cached normalized polynomial. -/
  margin : Certificate normalized.polynomial
  /-- The payment uses the same original uniform certificate and normalized cache. -/
  margin_eq : margin = uniform.normalizedMargin parameter inside normalized
  /-- The original complete chart clearances from the same retained paths and margin. -/
  clearance : Boundary.Clearance paths
  /-- The original clearance constructor reads these same stored parents. -/
  clearance_eq : clearance = margin.onBoundary paths
  /-- The independently computed original Laurent winding and complete polynomial root inventory. -/
  result : Circle.Comparison normalized paths clearance
  /-- The comparison is the original automatic builder on the same retained parents. -/
  result_eq : result = Circle.Comparison.prepare normalized paths clearance

constructive_injectivity Evaluation

namespace Evaluation

/-- Prepare the actual original parameter symbol once and construct its independent comparison automatically. -/
@[expose] public def prepare {path : Path} (uniform : Uniform path)
    (parameter : Rational) (inside : Parameter parameter) : Evaluation uniform parameter inside := by
  match equation : (path.symbol parameter).prepare with
  | .zero obstruction =>
      have lower := uniform.lower parameter inside 1 Gaussian.Basic.Canonical.normSq_one
      rewrite [obstruction.boundary_contact, Gaussian.Norm.Basic.normSq_zero] at lower
      exact ((not_lt_of_ge lower) uniform.positive).elim
  | .normalized normalized =>
      let paths := Boundary.Substitutions.prepare normalized.polynomial
      let margin := uniform.normalizedMargin parameter inside normalized
      let clearance := margin.onBoundary paths
      let result := Circle.Comparison.prepare normalized paths clearance
      exact
        { normalized, preparation_eq := equation, paths, paths_eq := rfl
          margin, margin_eq := rfl, clearance, clearance_eq := rfl, result, result_eq := rfl }

/-- The actual common numerator's independent winding accounts for the original symbol winding plus the common shift. -/
public theorem common_raw {path : Path} {uniform : Uniform path}
    {parameter : Rational} {inside : Parameter parameter} (evaluation : Evaluation uniform parameter inside)
    (prepared : Prepared uniform)
    (common : Boundary.Substitutions ((path.symbol parameter).polynomialize prepared.path.shift)) :
    Winding.Circle.raw common = 4 * (evaluation.result.reading.winding + (prepared.path.shift : Int)) := by
  have sufficient : (path.symbol parameter).rawShift ≤ prepared.path.shift := by
    rewrite [path.rawShift_symbol, prepared.path.shift_eq]
    exact Nat.le_refl _
  have poleBound : evaluation.normalized.poleOrder ≤ prepared.path.shift := by
    rewrite [evaluation.normalized.poleOrder_spec, evaluation.normalized.rawShift_spec]
    exact (Nat.sub_le _ _).trans sufficient
  let extra := prepared.path.shift - evaluation.normalized.poleOrder
  let shifted := Boundary.Substitutions.prepare
    (Dense.Basic.DensePolynomial.shift extra evaluation.normalized.polynomial)
  have same := Winding.Circle.Comparison.raw_eq_of_eval_eq
    (uniform.atParameter prepared.path parameter inside) common shifted (fun point _ => by
      rewrite [← evaluation.normalized.polynomialize_eq_shift prepared.path.shift sufficient,
        Dense.Basic.DensePolynomial.eval_normalize]
      rfl)
  have shiftedRaw := Winding.Circle.raw_shift evaluation.margin evaluation.paths extra shifted
  have castBalance : (extra : Int) + (evaluation.normalized.poleOrder : Int) =
      (prepared.path.shift : Int) := by
    rewrite [← _root_.Int.natCast_add, Nat.sub_add_cancel poleBound]
    rfl
  calc
    Winding.Circle.raw common = Winding.Circle.raw evaluation.paths + 4 * (extra : Int) :=
      same.symm.trans shiftedRaw
    _ = 4 * (evaluation.result.polynomial.inventory.insideCount : Int) + 4 * (extra : Int) := by
      rewrite [evaluation.result.polynomial.raw_eq]
      rfl
    _ = 4 * (evaluation.result.reading.winding + (prepared.path.shift : Int)) := by
      rewrite [evaluation.result.winding_eq, ← castBalance]
      ring1

/-- Actual original parameter comparisons have equal independent winding through collisions and support changes. -/
public theorem winding_eq {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {left right : Rational} {leftInside : Parameter left} {rightInside : Parameter right}
    (first : Evaluation uniform left leftInside) (last : Evaluation uniform right rightInside) :
    last.result.reading.winding = first.result.reading.winding := by
  let firstCommon := Boundary.Substitutions.prepare ((path.symbol left).polynomialize prepared.path.shift)
  let lastCommon := Boundary.Substitutions.prepare ((path.symbol right).polynomialize prepared.path.shift)
  have common := prepared.raw_eq leftInside rightInside firstCommon lastCommon
  have scaled := (last.common_raw prepared lastCommon).symm.trans
    (common.trans (first.common_raw prepared firstCommon))
  exact Int.Arithmetic.add_right_cancel
    (Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0) scaled)

/-- The actual pole-minus-inside index stays constant although its two separate finite counts may change. -/
public theorem index_eq {path : Path} {uniform : Uniform path} (prepared : Prepared uniform)
    {left right : Rational} {leftInside : Parameter left} {rightInside : Parameter right}
    (first : Evaluation uniform left leftInside) (last : Evaluation uniform right rightInside) :
    (last.normalized.poleOrder : Int) - (last.result.polynomial.inventory.insideCount : Int) =
      (first.normalized.poleOrder : Int) - (first.result.polynomial.inventory.insideCount : Int) := by
  rewrite [last.result.index_eq_neg_winding, first.result.index_eq_neg_winding,
    winding_eq prepared first last]
  rfl

end Evaluation

set_option genInjectivity false in
/-- A finite deformation comparison retaining the actual original endpoint constructions and sufficient schedule. -/
public structure Comparison {path : Path} (uniform : Uniform path) where
  /-- The once-prepared finite Horner and mesh payments. -/
  schedule : Prepared uniform
  /-- The stored schedule is the original deterministic sufficient constructor. -/
  schedule_eq : schedule = prepare uniform
  /-- The actual original initial symbol normalization, chart reading and complete inventory. -/
  initial : Evaluation uniform 0 ⟨by decide, by decide⟩
  /-- The initial construction is computed once by the same original automatic parameter builder. -/
  initial_eq : initial = Evaluation.prepare uniform 0 ⟨by decide, by decide⟩
  /-- The actual original terminal symbol normalization, chart reading and complete inventory. -/
  terminal : Evaluation uniform 1 ⟨by decide, by decide⟩
  /-- The terminal construction is computed once by the same original automatic parameter builder. -/
  terminal_eq : terminal = Evaluation.prepare uniform 1 ⟨by decide, by decide⟩
  /-- The actual independently computed endpoint windings agree. -/
  winding_eq : terminal.result.reading.winding = initial.result.reading.winding
  /-- The two actual endpoint pole-minus-inside indices agree despite changing support. -/
  index_eq : (terminal.normalized.poleOrder : Int) - (terminal.result.polynomial.inventory.insideCount : Int) =
    (initial.normalized.poleOrder : Int) - (initial.result.polynomial.inventory.insideCount : Int)

constructive_injectivity Comparison

namespace Comparison

/-- Compute the two actual original endpoint comparisons once and certify them with the retained finite schedule. -/
@[expose] public def prepare {path : Path} (uniform : Uniform path) : Comparison uniform :=
  let schedule := Deformation.prepare uniform
  let initial := Evaluation.prepare uniform 0 ⟨by decide, by decide⟩
  let terminal := Evaluation.prepare uniform 1 ⟨by decide, by decide⟩
  { schedule, schedule_eq := rfl, initial, initial_eq := rfl, terminal, terminal_eq := rfl
    winding_eq := Evaluation.winding_eq schedule initial terminal
    index_eq := Evaluation.index_eq schedule initial terminal }

/-- Construct one queried original parameter result without rebuilding either cached endpoint. -/
@[expose] public def evaluate {path : Path} {uniform : Uniform path} (_comparison : Comparison uniform)
    (parameter : Rational) (inside : Parameter parameter) : Evaluation uniform parameter inside :=
  Evaluation.prepare uniform parameter inside

/-- Every actual query has the same independently computed winding as the cached initial endpoint. -/
public theorem evaluation_winding_eq {path : Path} {uniform : Uniform path} (comparison : Comparison uniform)
    {parameter : Rational} {inside : Parameter parameter} (evaluation : Evaluation uniform parameter inside) :
    evaluation.result.reading.winding = comparison.initial.result.reading.winding :=
  Evaluation.winding_eq comparison.schedule comparison.initial evaluation

/-- Every actual queried original comparison has the same signed index as the cached initial endpoint. -/
public theorem evaluation_index_eq {path : Path} {uniform : Uniform path} (comparison : Comparison uniform)
    {parameter : Rational} {inside : Parameter parameter} (evaluation : Evaluation uniform parameter inside) :
    (evaluation.normalized.poleOrder : Int) - (evaluation.result.polynomial.inventory.insideCount : Int) =
      (comparison.initial.normalized.poleOrder : Int) -
        (comparison.initial.result.polynomial.inventory.insideCount : Int) :=
  Evaluation.index_eq comparison.schedule comparison.initial evaluation

end Comparison
end Purelib.Polynomial.Laurent.Circle.Deformation
