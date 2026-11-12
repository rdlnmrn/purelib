module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Requested
public import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Paid canonical/source model readings at one actual sample index

The original canonical parent movement mass fixes the comparison scale
before source completion or sampling. One original finite Selection can
therefore enlarge the existing endpoint constructor's minimum. At its
actual common index, the independently retained polynomial programmes are
read once and compared with the SAME forwarded source initial vector.
No output-name sample index is identified with a programme model index.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialValues

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply zipWith_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.LinearAlgebra.Gaussian
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {polynomialFloor : Nat}
    (values : PolynomialValues walk polynomialFloor)

/-- Read either actual retained numerator/work/programme cache without constructing a replacement. -/
abbrev entry (coordinate : Fin 2) : PolynomialValue walk values.1 polynomialFloor coordinate :=
  Fin.cases values.2.1
    (fun next => Fin.cases values.2.2.1 (fun impossible => Fin.elim0 impossible) next) coordinate

/-- Read both independent canonical programme models ONCE at the SAME actual stage.

The two scalar readings are bound before the structural vector is built.
Repeated vector-coordinate access therefore reads those retained scalars;
it never invokes either original programme's model callback again.
-/
def sampleValues (stage : Nat) : Vec Canonical 2 :=
  let first := ((values.entry 0).2.val.integral.model stage).integralSample
  let second := ((values.entry 1).2.val.integral.model stage).integralSample
  vectorOfFn (fun coordinate => Fin.cases first
    (fun next => Fin.cases second (fun impossible => Fin.elim0 impossible) next) coordinate)

/-- Every coordinate is the SAME retained original canonical programme's actual model reading. -/
theorem sampleValues_apply (stage : Nat) (coordinate : Fin 2) :
    values.sampleValues stage coordinate =
      ((values.entry coordinate).2.val.integral.model stage).integralSample := by
  refine Fin.cases ?_ ?_ coordinate
  · exact vectorOfFn_apply _ 0
  · intro next
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) next
    · exact vectorOfFn_apply _ 1

/-- Select the original finite stage paying a fixed nonnegative multiple of both model-coordinate errors.

The scale is twice that multiplier times the SAME original polynomial
movement-mass scale. It depends on the retained canonical parents before
any source completion or new model query. The subtype keeps the whole
original Selection factory rather than a retagged stage. Starting at the
old minimum retains its lower bound; the selected stage itself is a valid
enlarged minimum for the original source endpoint constructor.
-/
def sourceModelSelection (multiplier : Rational) (nonnegative : 0 ≤ multiplier)
    (minimum : Nat) (request : AccuracyRequest) :
    { selected : Selection (2 * multiplier * PolynomialWork.errorScale values.1.parents)
        minimum request.tolerance //
      selected = Selection.build (2 * multiplier * PolynomialWork.errorScale values.1.parents)
        (Order.Arithmetic.mul_nonneg_direct
          (Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 2 by decide +kernel) nonnegative)
          (PolynomialWork.errorScale_nonnegative (curve := Fibre.frameCurve frame)
            (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (parents := values.1.parents)))
        minimum request.tolerance request.positive } :=
  let selected := Selection.build (2 * multiplier * PolynomialWork.errorScale values.1.parents)
    (Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 2 by decide +kernel) nonnegative)
      (PolynomialWork.errorScale_nonnegative (curve := Fibre.frameCurve frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (parents := values.1.parents)))
    minimum request.tolerance request.positive
  ⟨selected, rfl⟩

variable {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : values.1.parents = parent :: parents) {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested (values.1.sourceCovered same) (values.1.sourceChain same) current floor rootStage accuracy)
    (completed : requested.attempt.OccurrenceFamily) (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (values.1.sourceCovered same) (values.1.sourceChain same) (fun stage => (completed stage).val))

include same requested completed factory in
/-- Both actual model-coordinate errors sum to twice the original SAME-index polynomial comparison radius.

The canonical vector and source initial vector are supplied retained
values with their actual factories. The original polynomial/source model
comparison and exact occurrence-jet readback derive every coordinate
bound; no numerical closeness, name-index identification or extra source
completion is an input.
-/
theorem source_models_difference_le (stage : Nat) (canonicalValues sourceValues : Vec Canonical 2)
    (canonicalFactory : canonicalValues = values.sampleValues stage)
    (sourceFactory : sourceValues = vectorOfFn (fun coordinate =>
      ((actual.value coordinate).integral.model stage).integralSample)) :
    Norm.vector (zipWith (fun first last => first - last) canonicalValues sourceValues) ≤
      2 * quarterRadius (PolynomialWork.errorScale values.1.parents) stage := by
  have coordinateBound (coordinate : Fin 2) : Norm.Basic.normSq
      (zipWith (fun first last => first - last) canonicalValues sourceValues coordinate) ≤
        quarterRadius (PolynomialWork.errorScale values.1.parents) stage := by
    let retained := values.entry coordinate
    have polynomialFactory : retained.2.val.integral = PolynomialWork.program retained.1 retained.1.models
        (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate) :=
      (congrArg (fun programme => programme.integral) retained.2.property).trans
      (PolynomialWork.fromWork_integral values.1.chain retained.1
        (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate))
    have bounded := PreparedParents.polynomial_samples_close
      (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (count := 1) (sourceFloor := floor) (polynomialFloor := polynomialFloor) (parents := values.1.parents)
      values.1.covered values.1.chain coordinate retained.1 retained.1.models
      (values.1.sourcePreparations same requested) retained.2.val.integral polynomialFactory stage
    have sourceReadback := values.1.source_value_sample (parameter := parameter) (frame := frame) (walk := walk)
      (parent := parent) (parents := parents) same requested completed actual factory coordinate stage
    have first := (congrArg (fun vector : Vec Canonical 2 => vector coordinate) canonicalFactory).trans
      (values.sampleValues_apply stage coordinate)
    have last := ((congrArg (fun vector : Vec Canonical 2 => vector coordinate) sourceFactory).trans
      (vectorOfFn_apply _ coordinate)).trans sourceReadback
    exact (congrArg Norm.Basic.normSq ((zipWith_apply _ _ _ coordinate).trans
      (congrArg₂ (fun first last : Canonical => first - last) first last))).trans_le bounded
  have finite := Order.Arithmetic.add_le_add_direct (coordinateBound 0) (coordinateBound 1)
  calc
    _ = Norm.Basic.normSq (zipWith (fun first last => first - last) canonicalValues sourceValues 0) +
        Norm.Basic.normSq (zipWith (fun first last => first - last) canonicalValues sourceValues 1) := by
      unfold Norm.vector
      rewrite [sumFin_succ, sumFin_succ]
      rewrite [show (0 : Fin 1).succ = (1 : Fin 2) from rfl]
      change _ + (_ + 0) = _
      ring1
    _ ≤ quarterRadius (PolynomialWork.errorScale values.1.parents) stage +
        quarterRadius (PolynomialWork.errorScale values.1.parents) stage := finite
    _ = 2 * quarterRadius (PolynomialWork.errorScale values.1.parents) stage := by ring1

include same requested completed factory in
/-- The actual retained original Selection pays every later SAME-model-index canonical/source vector error. -/
theorem source_models_difference_lt (multiplier : Rational) (nonnegative : 0 ≤ multiplier)
    {start : Nat} (request : AccuracyRequest)
    (selected : Selection (2 * multiplier * PolynomialWork.errorScale values.1.parents) start request.tolerance)
    (stage : Nat) (after : selected.stage ≤ stage) (canonicalValues sourceValues : Vec Canonical 2)
    (canonicalFactory : canonicalValues = values.sampleValues stage)
    (sourceFactory : sourceValues = vectorOfFn (fun coordinate =>
      ((actual.value coordinate).integral.model stage).integralSample)) :
    multiplier * Norm.vector (zipWith (fun first last => first - last) canonicalValues sourceValues) <
      request.tolerance := by
  have bounded := values.source_models_difference_le (parameter := parameter) (frame := frame) (walk := walk)
    (parent := parent) (parents := parents) same requested completed actual factory
    stage canonicalValues sourceValues canonicalFactory sourceFactory
  have radius : multiplier * (2 * quarterRadius (PolynomialWork.errorScale values.1.parents) stage) =
      quarterRadius (2 * multiplier * PolynomialWork.errorScale values.1.parents) stage := by
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded nonnegative).trans_lt
    (radius.trans_lt (selected.later_accurate after))

include same requested completed factory in
/-- Read the actual canonical vector once and retain its paid comparison with the SAME forwarded source initial value.

The selected floor must precede the actual common model index. The existing
endpoint constructor supplies that proof after its minimum is enlarged by
the selected stage. Only canonical model readings are executed here; the
supplied source family, initial vector and connection trace are not replayed.
-/
def readSource (multiplier : Rational) (nonnegative : 0 ≤ multiplier) {start : Nat} (request : AccuracyRequest)
    (selected : Selection (2 * multiplier * PolynomialWork.errorScale values.1.parents) start request.tolerance)
    (stage : Nat) (after : selected.stage ≤ stage) (sourceValues : Vec Canonical 2)
    (sourceFactory : sourceValues = vectorOfFn (fun coordinate =>
      ((actual.value coordinate).integral.model stage).integralSample)) :
    { canonicalValues : Vec Canonical 2 // canonicalValues = values.sampleValues stage ∧
      multiplier * Norm.vector (zipWith (fun first last => first - last) canonicalValues sourceValues) <
        request.tolerance } :=
  let canonicalValues := values.sampleValues stage
  ⟨canonicalValues, rfl, values.source_models_difference_lt (parameter := parameter) (frame := frame) (walk := walk)
    (parent := parent) (parents := parents) same requested completed actual factory multiplier nonnegative request
    selected stage after canonicalValues sourceValues rfl sourceFactory⟩

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialValues

end
