module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic
public import Purelib.Integration.Path.Primitive
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Integration.Program.Comparison.Add
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Taylor

/-!
# Closed primitive integration on retained rational circle quarters

The original bounded quarter table supplies every actual curve. One shared
boxed primitive preparation supplies every local error bound, transported
along the exact common box identity without rebuilding either cache. The
original primitive path composes the actual paid quarter comparisons.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Integration.Path.Primitive
open Purelib.Riemann.Periods
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Arithmetic

/-- Every original quarter uses the same actual centered circle box as its original circuit base. -/
theorem circleBox_quarterBase (base : Canonical) (quarter : Quarter.UnitCircuitQuarter) :
    circleBox (quarterBase base quarter) = circleBox base := by
  exact Geometry.Rational.Box.Square.Centered.normBox_congr _ _ (quarterBase_normSq base quarter)

/-- Every original quarter uses the same actual reciprocal box as its original guarded circuit base. -/
theorem reciprocalBox_quarterBase (base : Canonical) (nonzero : base ≠ 0)
    (quarter : Quarter.UnitCircuitQuarter) :
    reciprocalBox (quarterBase base quarter) (quarterBase_ne_zero base nonzero quarter) =
      reciprocalBox base nonzero := by
  exact Geometry.Rational.Box.Square.Centered.normBox_congr _ _
    (congrArg (fun value => value⁻¹) (quarterBase_normSq base quarter))

/-- Read the exact primitive at the original starting point of a retained quarter curve. -/
@[expose] def Entries.primitiveStart {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (primitive : Canonical → Canonical) (index : Fin quarters.length) :
    CoherentNamed :=
  PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive ((entries.get index).1.val.point 0)))

/-- Read the exact primitive at the original finishing point of a retained quarter curve. -/
@[expose] def Entries.primitiveFinish {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (primitive : Canonical → Canonical) (index : Fin quarters.length) :
    CoherentNamed :=
  PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive ((entries.get index).1.val.point 1)))

/-- The paid original primitive edges at all four original bounded curve occurrences.

The original dependent product retains the complete edge and its actual
program at each occurrence. Its indices keep both the supplied curve table
and the supplied primitive function unchanged.
-/
abbrev PrimitiveEdges {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (primitive : Canonical → Canonical) :=
  DependentProduct quarters (fun index =>
    PrimitiveEdge (entries.primitiveStart primitive index) (entries.primitiveFinish primitive index))

/-- Read one complete actual paid edge from the original bounded dependent product. -/
@[expose] def PrimitiveEdges.get {base : Canonical} {nonzero : base ≠ 0} {entries : Entries base nonzero}
    {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive) (index : Fin quarters.length) :
    PrimitiveEdge (entries.primitiveStart primitive index) (entries.primitiveFinish primitive index) :=
  DependentProduct.get quarters edges index

/-- Materialize all actual polynomial primitive edges using one supplied shared boxed preparation.

Each original quarter curve is read once. Exact equality of the original
circle boxes transports the same primitive and coefficient ceiling; no
antiderivative, box preparation or original curve is rebuilt.
-/
@[expose] def Entries.polynomialEdges {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base)) :
    PrimitiveEdges entries (Evaluation.eval retained.val) :=
  DependentProduct.ofFn quarters fun index =>
    let quarter := quarters[index.val]'index.isLt
    let curve := (entries.get index).1
    let actualPreparation := preparation.castBox (circleBox_quarterBase base quarter).symm
    Dyadic.polynomialEdge (quarterBase base quarter) curve source retained actualPreparation

/-- Materialize all actual polar primitive edges from the same retained numerator and antiderivative caches.

Every quarter consumes the supplied original reversal, antiderivative and
shared reciprocal-box preparation. The common nonzero floor and exact box
identity preserve those complete actual caches at every original index.
-/
@[expose] def Entries.reciprocalEdges {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    {source : CoefficientPolynomial} {order : Nat} (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero)) :
    PrimitiveEdges entries retained.value :=
  DependentProduct.ofFn quarters fun index =>
    let quarter := quarters[index.val]'index.isLt
    let curve := (entries.get index).1
    let actualPreparation := preparation.castBox (reciprocalBox_quarterBase base nonzero quarter).symm
    Dyadic.reciprocalEdge (quarterBase base quarter) (quarterBase_ne_zero base nonzero quarter)
      curve retained actualPreparation

/-- Lookup returns the complete actual polynomial edge constructed with the same supplied box caches. -/
theorem Entries.polynomialEdges_get {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base)) (index : Fin quarters.length) :
    (entries.polynomialEdges source retained preparation).get index =
      Dyadic.polynomialEdge (quarterBase base (quarters[index.val]'index.isLt)) (entries.get index).1 source retained
        (preparation.castBox (circleBox_quarterBase base (quarters[index.val]'index.isLt)).symm) :=
  DependentProduct.get_ofFn quarters _ index

/-- Lookup returns the complete actual polar edge constructed from the same supplied numerator and box caches. -/
theorem Entries.reciprocalEdges_get {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    {source : CoefficientPolynomial} {order : Nat} (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero))
    (index : Fin quarters.length) :
    (entries.reciprocalEdges retained preparation).get index =
      Dyadic.reciprocalEdge (quarterBase base (quarters[index.val]'index.isLt))
        (quarterBase_ne_zero base nonzero (quarters[index.val]'index.isLt)) (entries.get index).1 retained
        (preparation.castBox (reciprocalBox_quarterBase base nonzero (quarters[index.val]'index.isLt)).symm) :=
  DependentProduct.get_ofFn quarters _ index

/-- Each actual retained polynomial edge has the original complete same-curve dyadic model. -/
theorem Entries.polynomialEdges_model {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base))
    (quarter : Fin quarters.length) (index : Nat) :
    (((entries.polynomialEdges source retained preparation).get quarter).program.model index) =
      Dyadic.model (quarterBase base (quarters[quarter.val]'quarter.isLt)) (entries.get quarter).1
        (Evaluation.eval source) index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
  rewrite [entries.polynomialEdges_get]
  exact Dyadic.polynomialEdge_model _ _ _ _ _ _

/-- Each actual retained polar edge has the original complete same-curve dyadic model. -/
theorem Entries.reciprocalEdges_model {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    {source : CoefficientPolynomial} {order : Nat} (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero))
    (quarter : Fin quarters.length) (index : Nat) :
    (((entries.reciprocalEdges retained preparation).get quarter).program.model index) =
      Dyadic.model (quarterBase base (quarters[quarter.val]'quarter.isLt)) (entries.get quarter).1
        retained.derivativeValue index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
  rewrite [entries.reciprocalEdges_get]
  exact Dyadic.reciprocalEdge_model _ _ _ _ _ _

/-- Every actual retained polynomial quarter has the original dyadic cell count at its original stage. -/
theorem Entries.polynomialEdges_count {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (source : CoefficientPolynomial)
    (retained : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (preparation : Antiderivative.BoxPreparation source retained (circleBox base))
    (quarter : Fin quarters.length) (index : Nat) :
    (((entries.polynomialEdges source retained preparation).get quarter).program.model index).cells.length =
      2 ^ index := by
  rewrite [entries.polynomialEdges_model]
  exact Dyadic.model_count _ _ _ _ _ _

/-- Every actual retained polar quarter has the original dyadic cell count at its original stage. -/
theorem Entries.reciprocalEdges_count {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    {source : CoefficientPolynomial} {order : Nat} (retained : Antiderivative.ReciprocalPrimitive source order)
    (preparation : Antiderivative.BoxPreparation retained.1.val retained.2 (reciprocalBox base nonzero))
    (quarter : Fin quarters.length) (index : Nat) :
    (((entries.reciprocalEdges retained preparation).get quarter).program.model index).cells.length =
      2 ^ index := by
  rewrite [entries.reciprocalEdges_model]
  exact Dyadic.model_count _ _ _ _ _ _

/-- Close the four stored paid primitive edges using their actual original curve joins.

Every required endpoint presentation is computed once and retained directly
by the original boundary and path constructors. The supplied product provides
every original edge program and paid comparison; exact original endpoint
joins and closure supply the same-cache operational boundary.
-/
@[expose] def PrimitiveEdges.boundary {base : Canonical} {nonzero : base ≠ 0} {entries : Entries base nonzero}
    {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive) : ClosedPrimitiveBoundary :=
  let firstStart := entries.primitiveStart primitive ⟨0, by decide +kernel⟩
  let firstFinish := entries.primitiveFinish primitive ⟨0, by decide +kernel⟩
  let secondStart := entries.primitiveStart primitive ⟨1, by decide +kernel⟩
  let secondFinish := entries.primitiveFinish primitive ⟨1, by decide +kernel⟩
  let thirdStart := entries.primitiveStart primitive ⟨2, by decide +kernel⟩
  let thirdFinish := entries.primitiveFinish primitive ⟨2, by decide +kernel⟩
  let fourthStart := entries.primitiveStart primitive ⟨3, by decide +kernel⟩
  let fourthFinish := entries.primitiveFinish primitive ⟨3, by decide +kernel⟩
  have firstJoin : firstFinish = secondStart := congrArg
    (fun point => PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive point)))
    (entries.join ⟨0, by decide +kernel⟩)
  have secondJoin : secondFinish = thirdStart := congrArg
    (fun point => PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive point)))
    (entries.join ⟨1, by decide +kernel⟩)
  have thirdJoin : thirdFinish = fourthStart := congrArg
    (fun point => PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive point)))
    (entries.join ⟨2, by decide +kernel⟩)
  let firstShared := NamedEquivalent.transport (congrArg CoherentNamed.name firstJoin.symm) rfl
    (NamedEquivalent.refl secondStart.name)
  let secondShared := NamedEquivalent.transport (congrArg CoherentNamed.name secondJoin.symm) rfl
    (NamedEquivalent.refl thirdStart.name)
  let thirdShared := NamedEquivalent.transport (congrArg CoherentNamed.name thirdJoin.symm) rfl
    (NamedEquivalent.refl fourthStart.name)
  let fourthPath : PrimitivePath fourthStart fourthFinish :=
    .cons (edges.get ⟨3, by decide +kernel⟩) (.nil fourthFinish)
  let thirdPath : PrimitivePath thirdStart fourthFinish :=
    .overlap (edges.get ⟨2, by decide +kernel⟩) fourthPath thirdShared
  let secondPath : PrimitivePath secondStart fourthFinish :=
    .overlap (edges.get ⟨1, by decide +kernel⟩) thirdPath secondShared
  let firstPath : PrimitivePath firstStart fourthFinish :=
    .overlap (edges.get ⟨0, by decide +kernel⟩) secondPath firstShared
  have closed : fourthFinish = firstStart := congrArg
    (fun point => PeriodMatrix.geometricNamed (GeometricApproximation.exact (primitive point))) entries.closed
  { start := firstStart
    finish := fourthFinish
    path := firstPath
    closed := NamedEquivalent.transport (congrArg CoherentNamed.name closed.symm) rfl
      (NamedEquivalent.refl firstStart.name) }

/-- The actual four paid primitive-program outputs sum operationally to exact zero on the retained circle. -/
@[expose] def PrimitiveEdges.integralSum_zero {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive) :
    NamedEquivalent edges.boundary.integralSum.name (CoherentNamed.Coherence.exact 0).name :=
  edges.boundary.integralSum_zero

/-- The closed boundary retains the complete four actual program outputs in their original path sum. -/
theorem PrimitiveEdges.boundary_integralSum {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive) :
    edges.boundary.integralSum =
      CoherentNamed.add (edges.get ⟨0, by decide +kernel⟩).program.output
        (CoherentNamed.add (edges.get ⟨1, by decide +kernel⟩).program.output
          (CoherentNamed.add (edges.get ⟨2, by decide +kernel⟩).program.output
            (CoherentNamed.add (edges.get ⟨3, by decide +kernel⟩).program.output
              (CoherentNamed.Coherence.exact 0)))) := rfl

/-- Concatenate all four actual stored primitive integration programs with their original equally resolved cells.

Both original half-programs are constructed once from the supplied edge
programs. Their original cell-count laws derive the actual concatenation
allowance; no primitive or quarter program is rebuilt.
-/
@[expose] def PrimitiveEdges.concatenate {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive)
    (count : ∀ quarter index, ((edges.get quarter).program.model index).cells.length = 2 ^ index) :
    RefinementProgram :=
  let first := (edges.get ⟨0, by decide +kernel⟩).program
  let second := (edges.get ⟨1, by decide +kernel⟩).program
  let third := (edges.get ⟨2, by decide +kernel⟩).program
  let fourth := (edges.get ⟨3, by decide +kernel⟩).program
  let earlier := first.concatOfEqualCounts second
    (fun index => (count ⟨0, by decide +kernel⟩ index).trans (count ⟨1, by decide +kernel⟩ index).symm)
  let later := third.concatOfEqualCounts fourth
    (fun index => (count ⟨2, by decide +kernel⟩ index).trans (count ⟨3, by decide +kernel⟩ index).symm)
  earlier.concatOfEqualCounts later (by
    intro index
    change ((first.model index).cells ++ (second.model index).cells).length =
      ((third.model index).cells ++ (fourth.model index).cells).length
    rewrite [List.length_append, List.length_append, count ⟨0, by decide +kernel⟩, count ⟨1, by decide +kernel⟩,
      count ⟨2, by decide +kernel⟩, count ⟨3, by decide +kernel⟩]
    rfl)

/-- The actual closed concatenation retains all four same-stage quarter models in their original grouping. -/
theorem PrimitiveEdges.concatenate_model {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive)
    (count : ∀ quarter index, ((edges.get quarter).program.model index).cells.length = 2 ^ index) (index : Nat) :
    (edges.concatenate count).model index =
      (((edges.get ⟨0, by decide +kernel⟩).program.model index).concat
        ((edges.get ⟨1, by decide +kernel⟩).program.model index)).concat
          (((edges.get ⟨2, by decide +kernel⟩).program.model index).concat
            ((edges.get ⟨3, by decide +kernel⟩).program.model index)) := rfl

/-- Compare the sum of two actual outputs with their exact original equally resolved concatenation. -/
private def concat_output (first second : RefinementProgram)
    (count : ∀ index, (first.model index).cells.length = (second.model index).cells.length) :
    NamedEquivalent (CoherentNamed.add first.output second.output).name
      (first.concatOfEqualCounts second count).output.name := by
  unfold RefinementProgram.concatOfEqualCounts RefinementProgram.concat
  exact Integration.Program.Comparison.Add.addProgram_output_equivalent _ _ _

/-- Compare the actual ordered primitive-path sum with the actual four-quarter concatenated program.

The original addition comparisons first remove only the terminal zero and
associate the same four outputs. The original sum-program comparisons then
consume those same actual quarter programs in their retained grouping.
-/
def PrimitiveEdges.integralSum_concatenate {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive)
    (count : ∀ quarter index, ((edges.get quarter).program.model index).cells.length = 2 ^ index) :
    NamedEquivalent edges.boundary.integralSum.name (edges.concatenate count).output.name := by
  let first := (edges.get ⟨0, by decide +kernel⟩).program
  let second := (edges.get ⟨1, by decide +kernel⟩).program
  let third := (edges.get ⟨2, by decide +kernel⟩).program
  let fourth := (edges.get ⟨3, by decide +kernel⟩).program
  let earlierCount := fun index =>
    (count ⟨0, by decide +kernel⟩ index).trans (count ⟨1, by decide +kernel⟩ index).symm
  let laterCount := fun index =>
    (count ⟨2, by decide +kernel⟩ index).trans (count ⟨3, by decide +kernel⟩ index).symm
  let earlier := first.concatOfEqualCounts second earlierCount
  let later := third.concatOfEqualCounts fourth laterCount
  have outerCount : ∀ index, (earlier.model index).cells.length = (later.model index).cells.length := by
    intro index
    change ((first.model index).cells ++ (second.model index).cells).length =
      ((third.model index).cells ++ (fourth.model index).cells).length
    rewrite [List.length_append, List.length_append, count ⟨0, by decide +kernel⟩, count ⟨1, by decide +kernel⟩,
      count ⟨2, by decide +kernel⟩, count ⟨3, by decide +kernel⟩]
    rfl
  have removeZero := Congruence.coherentAdd_respects third.output third.output
    (CoherentNamed.add fourth.output (CoherentNamed.Coherence.exact 0)) fourth.output
    (NamedEquivalent.refl _) (Add.coherentAdd_zero_right fourth.output)
  have underSecond := Congruence.coherentAdd_respects second.output second.output
    (CoherentNamed.add third.output (CoherentNamed.add fourth.output (CoherentNamed.Coherence.exact 0)))
    (CoherentNamed.add third.output fourth.output) (NamedEquivalent.refl _) removeZero
  have underFirst := Congruence.coherentAdd_respects first.output first.output
    (CoherentNamed.add second.output
      (CoherentNamed.add third.output (CoherentNamed.add fourth.output (CoherentNamed.Coherence.exact 0))))
    (CoherentNamed.add second.output (CoherentNamed.add third.output fourth.output))
    (NamedEquivalent.refl _) underSecond
  have associate := NamedEquivalent.symm
    (Add.coherentAdd_assoc first.output second.output (CoherentNamed.add third.output fourth.output))
  have group := Congruence.coherentAdd_respects
    (CoherentNamed.add first.output second.output) earlier.output
    (CoherentNamed.add third.output fourth.output) later.output
    (concat_output first second earlierCount) (concat_output third fourth laterCount)
  rewrite [edges.boundary_integralSum]
  exact underFirst.trans (associate.trans (group.trans (concat_output earlier later outerCount)))

/-- The actual concatenated four-quarter primitive integration program is operationally exact zero.

Its finite comparison is derived from the actual paid quarter comparisons,
actual stored endpoint joins and actual output-addition comparisons. No
integral-zero or successful integration comparison is supplied by a caller.
-/
def PrimitiveEdges.concatenate_zero {base : Canonical} {nonzero : base ≠ 0}
    {entries : Entries base nonzero} {primitive : Canonical → Canonical} (edges : PrimitiveEdges entries primitive)
    (count : ∀ quarter index, ((edges.get quarter).program.model index).cells.length = 2 ^ index) :
    NamedEquivalent (edges.concatenate count).output.name (CoherentNamed.Coherence.exact 0).name :=
  (edges.integralSum_concatenate count).symm.trans edges.integralSum_zero

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
