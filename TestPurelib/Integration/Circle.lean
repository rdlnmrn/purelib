module

import Purelib.System.IO
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Primitive
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Dyadic
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.PrimitiveLoop
import Purelib.Integration.Polynomial.Gaussian.Path.Concatenation
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Stored rational-circle quarters and their actual integral normalizer -/

namespace TestPurelib.Integration.Circle

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The displayed nonzero starting point of the actual four-quarter circle. -/
private def base : Canonical := ⟨1, 0⟩

/-- The original rational-circle starting point is nonzero. -/
private theorem base_ne_zero : base ≠ 0 := by decide +kernel

/-- The original four stored curves, their same-cache programs and their exact concatenation. -/
private def retained : Circuit base base_ne_zero := circuit base base_ne_zero

/-- The first actual original curve is the complete source stored in the first materialized entry. -/
private theorem first_curve :
    (retained.1.get ⟨0, by decide +kernel⟩).1.val = circle (quarterBase base .first) := rfl

/-- The last actual original program consumes the same last stored curve with its original guard. -/
private theorem last_program :
    (retained.1.get ⟨3, by decide +kernel⟩).2.val =
      program (quarterBase base .fourth) (quarterBase_ne_zero base base_ne_zero .fourth)
        (retained.1.get ⟨3, by decide +kernel⟩).1 := rfl

/-- The three joins use the actual stored original curves. -/
private theorem consecutive (index : Fin 3) :
    (retained.1.get index.castSucc).1.val.point 1 = (retained.1.get index.succ).1.val.point 0 :=
  retained.1.join index

/-- The final stored original curve returns to the first stored original curve's start. -/
private theorem closed :
    (retained.1.get ⟨3, by decide +kernel⟩).1.val.point 1 =
      (retained.1.get ⟨0, by decide +kernel⟩).1.val.point 0 := retained.1.closed

/-- The retained actual closed-loop integral channel has its original division-ready denominator certificate. -/
private def normalizer : Prepared retained.channel := retained.prepared

/-- A finite original coefficient table with both nonlogarithmic and logarithmic polar terms. -/
private def polar : CoefficientPolynomial := ⟨[1, 3, 5, 7]⟩

/-- The original retained reversal and antiderivative caches for its two nonlogarithmic polar terms. -/
private def primitive : Antiderivative.ReciprocalPrimitive polar 2 := Antiderivative.reciprocalPrimitive polar 2

/-- The complete primitive table is built from the actual same retained reversal. -/
private theorem same_reversal : primitive.2.val = Antiderivative.antiderivative primitive.1.val := rfl

/-- The actual stored original circle supplies the reciprocal primitive's coordinate guard internally. -/
private theorem actual_coefficient (index : Fin quarters.length) (time : Data.Rat.Fraction.Rational) :
    primitive.derivativeValue ((retained.1.get index).1.val.point time) =
      Evaluation.eval ⟨polar.coefficients.take 2⟩ ((retained.1.get index).1.val.point time) *
        (((retained.1.get index).1.val.point time) ^ 3)⁻¹ :=
  retained.1.reciprocalPrimitive_coefficient primitive index time

/-- The same cached reciprocal primitive cancels on all four actual joined curve endpoints. -/
private theorem primitive_closed :
    (retained.1.primitiveIncrement primitive.value ⟨0, by decide +kernel⟩ +
      retained.1.primitiveIncrement primitive.value ⟨1, by decide +kernel⟩) +
    (retained.1.primitiveIncrement primitive.value ⟨2, by decide +kernel⟩ +
      retained.1.primitiveIncrement primitive.value ⟨3, by decide +kernel⟩) = 0 :=
  retained.1.primitive_closed primitive.value

/-- Preparing a boxed primitive retains the complete supplied antiderivative, including its coefficient table. -/
private theorem boxed_original (source : CoefficientPolynomial)
    (actual : { value : CoefficientPolynomial // value = Antiderivative.antiderivative source })
    (box : Geometry.Rational.Box) :
    (Antiderivative.prepareInBox source actual box).1.val.value = Dense.Evaluation.toDense actual.val := rfl

/-- The actual left-cell integral reads the stored quarter's nonlogarithmic coefficient and original tangent. -/
private theorem polar_cell_sample :
    (coefficientCell (quarterBase base .first) (retained.1.get ⟨0, by decide +kernel⟩).1
      primitive.derivativeValue 0 1).integralSample = (⟨0, 8⟩ : Canonical) := by
  rewrite [coefficientCell_integralSample, first_curve]
  decide +kernel

/-- The independent cached primitive endpoint increment differs from that actual single-cell integral. -/
private theorem polar_endpoint_increment :
    primitive.value ((retained.1.get ⟨0, by decide +kernel⟩).1.val.point 1) -
      primitive.value ((retained.1.get ⟨0, by decide +kernel⟩).1.val.point 0) = (⟨4, 3⟩ : Canonical) := by
  rewrite [first_curve]
  decide +kernel

/-- The same stored first curve with its exact first-quarter subtype certificate made explicit. -/
private def firstCurve : { value : RationalCurve // value = circle (quarterBase base .first) } :=
  ⟨(retained.1.get ⟨0, by decide +kernel⟩).1.val, first_curve⟩

/-- The actual retained first-quarter reciprocal primitive preparation is computed once. -/
private def polarPreparation := Antiderivative.prepareInBox primitive.1.val primitive.2
  (reciprocalBox (quarterBase base .first) (quarterBase_ne_zero base base_ne_zero .first))

/-- The original paid primitive edge for the same stored curve and cached nonlogarithmic primitive. -/
private def polarEdge := Dyadic.reciprocalEdge (quarterBase base .first)
  (quarterBase_ne_zero base base_ne_zero .first) firstCurve primitive polarPreparation

/-- The actual numerical primitive edge's first model retains the original nonlogarithmic Riemann-cell sample. -/
private theorem polar_program_initial : (polarEdge.program.model 0).integralSample = (⟨0, 8⟩ : Canonical) := by
  unfold polarEdge
  rewrite [Dyadic.reciprocalEdge_model, Dyadic.model_zero,
    PathModel.singleton_integralSample]
  exact polar_cell_sample

/-- The original regular tail is the literal higher block of the same original polar coefficient source. -/
private def regular : CoefficientPolynomial := Arithmetic.divideByPower 3 polar

/-- The original antiderivative of that actual regular tail is retained once. -/
private def regularPrimitive : { value : CoefficientPolynomial // value = Antiderivative.antiderivative regular } :=
  let value := Antiderivative.antiderivative regular
  ⟨value, rfl⟩

/-- The actual regular-tail primitive and coefficient bounds are prepared once on the same circle. -/
private def regularPreparation :=
  Antiderivative.prepareInBox regular regularPrimitive (circleBox (quarterBase base .first))

/-- The original paid regular-tail edge consumes the same stored first-quarter curve and finite primitive. -/
private def regularEdge := Dyadic.polynomialEdge (quarterBase base .first)
  firstCurve regular regularPrimitive regularPreparation

/-- The actual regular-tail program starts with its genuine same-curve left-cell sample. -/
private theorem regular_program_initial : (regularEdge.program.model 0).integralSample = (⟨0, 14⟩ : Canonical) := by
  unfold regularEdge
  rewrite [Dyadic.polynomialEdge_model, Dyadic.model_zero,
    PathModel.singleton_integralSample,
    coefficientCell_integralSample]
  dsimp only [firstCurve]
  rewrite [first_curve]
  decide +kernel

/-- The same actual regular-tail box caches transported once to the common circuit box. -/
private def regularSharedPreparation := regularPreparation.castBox (circleBox_quarterBase base .first)

/-- All four actual regular primitive programs, built once from the same retained curve and preparation table. -/
private def regularEdges := retained.1.polynomialEdges regular regularPrimitive regularSharedPreparation

/-- The actual concatenated regular-tail program is operationally exact zero on the original closed curve. -/
private def regular_closed_operational :
    NamedEquivalent
      (regularEdges.concatenate
        (retained.1.polynomialEdges_count regular regularPrimitive regularSharedPreparation)).output.name
      (CoherentNamed.Coherence.exact 0).name :=
  regularEdges.concatenate_zero
    (retained.1.polynomialEdges_count regular regularPrimitive regularSharedPreparation)

/-- The same actual polar box caches transported once to the common reciprocal circuit box. -/
private def polarSharedPreparation :=
  polarPreparation.castBox (reciprocalBox_quarterBase base base_ne_zero .first)

/-- All four actual nonlogarithmic polar programs share the supplied reversal, antiderivative and box caches. -/
private def polarEdges := retained.1.reciprocalEdges primitive polarSharedPreparation

/-- The actual concatenated nonlogarithmic polar program is operationally exact zero on the original circle. -/
private def polar_closed_operational :
    NamedEquivalent
      (polarEdges.concatenate (retained.1.reciprocalEdges_count primitive polarSharedPreparation)).output.name
      (CoherentNamed.Coherence.exact 0).name :=
  polarEdges.concatenate_zero (retained.1.reciprocalEdges_count primitive polarSharedPreparation)

/-- A higher nonlogarithmic pole whose coarse four-quarter Riemann sample has a nonzero aliasing error. -/
private def higherPole : CoefficientPolynomial := ⟨[1]⟩

/-- The actual retained primitive of the original coefficient divided by the fifth coordinate power. -/
private def higherPrimitive := Antiderivative.reciprocalPrimitive higherPole 4

/-- One common boxed preparation of that actual retained higher-pole primitive. -/
private def higherPreparation :=
  Antiderivative.prepareInBox higherPrimitive.1.val higherPrimitive.2 (reciprocalBox base base_ne_zero)

/-- Materialize the actual four higher-pole primitive programs once on the same supplied original circle. -/
private def higherEdges := retained.1.reciprocalEdges higherPrimitive higherPreparation

/-- The concatenated actual higher-pole program retains its original four numerical quarter models. -/
private def higherProgram :=
  higherEdges.concatenate (retained.1.reciprocalEdges_count higherPrimitive higherPreparation)

/-- The higher-pole closed program is operationally exact zero through its actual paid primitive comparisons. -/
private def higher_closed_operational :
    NamedEquivalent higherProgram.output.name (CoherentNamed.Coherence.exact 0).name :=
  higherEdges.concatenate_zero (retained.1.reciprocalEdges_count higherPrimitive higherPreparation)

/-- Each higher-pole coarse actual quarter sample reads the same nonzero original Riemann value. -/
private theorem higher_quarter_initial (index : Fin quarters.length) :
    ((higherEdges.get index).program.model 0).integralSample = (⟨0, 2⟩ : Canonical) := by
  unfold higherEdges
  rewrite [Entries.reciprocalEdges_model, Dyadic.model_zero, PathModel.singleton_integralSample,
    coefficientCell_integralSample, (retained.1.get index).1.property]
  refine Fin.cases ?_
    (fun tail => Fin.cases ?_ (fun last => Fin.cases ?_ (fun final => Fin.cases ?_
      (fun impossible => Fin.elim0 impossible) final) last) tail) index <;> decide +kernel

/-- The actual closed program starts at a nonzero sample, rather than a substituted endpoint-difference sample. -/
private theorem higher_program_initial : (higherProgram.model 0).integralSample = (⟨0, 8⟩ : Canonical) := by
  unfold higherProgram
  rewrite [PrimitiveEdges.concatenate_model, PathModel.integralSample_concat, PathModel.integralSample_concat,
    PathModel.integralSample_concat, higher_quarter_initial, higher_quarter_initial,
    higher_quarter_initial, higher_quarter_initial]
  decide +kernel

/-- Execute the actual closed-primitive comparison at independently requested positive starts and tolerance.

The original coarse model is evaluated before requesting the actual paid
comparison. The returned indices are checked against their two independent
starts; the retained kernel certificate supplies its squared-tail bound.
-/
public def checkClosedPrimitive : IO Unit := do
  let coarse := (higherProgram.model 0).integralSample
  unless coarse == (⟨0, 8⟩ : Canonical) do
    throw (IO.userError "the actual higher-pole coarse sample changed")
  System.IO.println "closed primitive payment: actual coarse sample=8i; starts=1/2; squared tolerance=1/16"
  let quarterScale := (higherEdges.get ⟨0, by decide +kernel⟩).program.errorScale
  let scale := higherProgram.errorScale
  let stage := higherProgram.approximation.refineIndex 1 (1 / 16) (by decide +kernel)
  System.IO.println (s!"retained quarter error scale={quarterScale.num}/{quarterScale.den}; " ++
    s!"whole-loop scale={scale.num}/{scale.den}; direct whole-program refinement stage={stage}")
  (← IO.getStdout).flush
  let comparison := higher_closed_operational.compare 1 2 (1 / 16) (by decide +kernel)
  unless comparison.leftIndex ≥ 1 && comparison.rightIndex ≥ 2 do
    throw (IO.userError "the actual paid comparison lost an independently requested start")
  System.IO.println s!"closed primitive payment passed at {comparison.leftIndex}/{comparison.rightIndex}"

end TestPurelib.Integration.Circle
