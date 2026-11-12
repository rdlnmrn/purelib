module
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Integration.Program.Comparison
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
public import Purelib.Integration.Path.Lifted.Model
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

/-! Ordered primitive paths retain their exact coherent endpoints and original
integration programs. Their boundary certificates compare the retained endpoint
names and integral outputs without replacing either owner. -/

public section

namespace Purelib.Integration.Path.Primitive

open Purelib.Approximation.Gaussian
open Purelib.Integration.Path
open Purelib
open Purelib.Riemann.Periods

/-- The coherent difference of the original finish and start values, formed as negative start plus finish. -/
@[expose] def primitiveDifference (start finish : CoherentNamed) : CoherentNamed :=
  CoherentNamed.add
    (CoherentNamed.neg start) finish

/-- An original value's difference from itself is coherently equivalent to exact zero.

The finite comparison retains the same coherent value as both endpoints and
uses its additive cancellation certificate at every requested tolerance. -/
@[expose] def primitiveDifference_self_zero (value : CoherentNamed) :
    Equivalence.NamedEquivalent (primitiveDifference value value).name
      (CoherentNamed.Coherence.exact 0).name := by
  simpa only [primitiveDifference,
    CoherentNamed.add,
    CoherentNamed.neg,
    CoherentNamed.Coherence.exact] using
    Arithmetic.Neg.coherentAdd_neg_left value

/-- Compare endpoint differences after identifying the original finishing names.

The starting name is retained literally. The comparison changes only the
finishing occurrence through its supplied operational identification. -/
@[expose] def primitiveDifference_finish_respects
    (start left right : CoherentNamed)
    (finish : Equivalence.NamedEquivalent left.name right.name) :
    Equivalence.NamedEquivalent (primitiveDifference start left).name
      (primitiveDifference start right).name :=
  Congruence.coherentAdd_respects
    (CoherentNamed.neg start) (CoherentNamed.neg start)
    left right (Equivalence.NamedEquivalent.refl _) finish

/-- Compare original primitive endpoint differences using both original endpoint identifications. -/
@[expose] def primitiveDifference_respects
    (leftStart rightStart leftFinish rightFinish : CoherentNamed)
    (start : Equivalence.NamedEquivalent leftStart.name rightStart.name)
    (finish : Equivalence.NamedEquivalent leftFinish.name rightFinish.name) :
    Equivalence.NamedEquivalent (primitiveDifference leftStart leftFinish).name
      (primitiveDifference rightStart rightFinish).name :=
  Congruence.coherentAdd_respects
    (CoherentNamed.neg leftStart) (CoherentNamed.neg rightStart)
    leftFinish rightFinish (Coherent.Additive.coherentNeg_respects _ _ start) finish

/-- Adding original endpoint-compatible primitive differences is equivalent to the outer endpoint difference.

The comparison retains the exact three coherent names and composes their original additive and cancellation
certificates. -/
@[expose] def primitiveDifference_compose (start middle finish : CoherentNamed) :
    Equivalence.NamedEquivalent
      (CoherentNamed.add
        (primitiveDifference start middle)
        (primitiveDifference middle finish)).name
      (primitiveDifference start finish).name := by
  let negativeStart := CoherentNamed.neg start
  let negativeMiddle := CoherentNamed.neg middle
  let middleFinish := CoherentNamed.add
    negativeMiddle finish
  have associate : Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.add negativeStart middle)
        middleFinish).name
      (CoherentNamed.add negativeStart
        (CoherentNamed.add middle
          middleFinish)).name :=
    Arithmetic.Add.coherentAdd_assoc
      negativeStart middle middleFinish
  have exposeCancellation : Equivalence.NamedEquivalent
      (CoherentNamed.add middle middleFinish).name
      (CoherentNamed.add
        (CoherentNamed.add middle negativeMiddle)
        finish).name :=
    Equivalence.NamedEquivalent.symm (by
      simpa only [middleFinish,
        CoherentNamed.add] using
        Arithmetic.Add.coherentAdd_assoc
          middle negativeMiddle finish)
  let zero := CoherentNamed.Coherence.exact 0
  have cancellation : Equivalence.NamedEquivalent
      (CoherentNamed.add middle negativeMiddle).name
      zero.name := by
    simpa only [negativeMiddle, zero,
      CoherentNamed.neg,
      CoherentNamed.Coherence.exact,
      CoherentNamed.add] using
      Arithmetic.Neg.coherentAdd_neg_right middle
  have removeCancellation : Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.add middle negativeMiddle)
        finish).name
      finish.name :=
    Equivalence.NamedEquivalent.trans
      (Congruence.coherentAdd_respects
        (CoherentNamed.add middle negativeMiddle)
        zero finish finish cancellation
        (Equivalence.NamedEquivalent.refl finish.name))
      (Arithmetic.Add.coherentAdd_zero_left finish)
  have reduceTail : Equivalence.NamedEquivalent
      (CoherentNamed.add middle middleFinish).name
      finish.name :=
    Equivalence.NamedEquivalent.trans exposeCancellation
      removeCancellation
  have reduceUnderStart : Equivalence.NamedEquivalent
      (CoherentNamed.add negativeStart
        (CoherentNamed.add middle middleFinish)).name
      (CoherentNamed.add
        negativeStart finish).name :=
    Congruence.coherentAdd_respects
      negativeStart negativeStart
      (CoherentNamed.add middle middleFinish)
      finish
      (Equivalence.NamedEquivalent.refl negativeStart.name)
      reduceTail
  simpa only [primitiveDifference, negativeStart, negativeMiddle,
    middleFinish, CoherentNamed.add,
    CoherentNamed.neg] using
    Equivalence.NamedEquivalent.trans associate reduceUnderStart

/-- An original increment is equivalent to the difference from the original start to start plus that increment.

The retained start and increment supply both endpoint names. The comparison
keeps the same increment owner while cancelling only the repeated start. -/
@[expose] def increment_eq_primitiveDifference (start increment : CoherentNamed) :
    Equivalence.NamedEquivalent increment.name
      (primitiveDifference start
        (CoherentNamed.add start increment)).name := by
  let negativeStart := CoherentNamed.neg start
  let zero := CoherentNamed.Coherence.exact 0
  let cancellation := CoherentNamed.add
    negativeStart start
  have begin : Equivalence.NamedEquivalent increment.name
      (CoherentNamed.add zero increment).name :=
    Equivalence.NamedEquivalent.symm
      (Arithmetic.Add.coherentAdd_zero_left increment)
  have exposeCancellation : Equivalence.NamedEquivalent
      (CoherentNamed.add zero increment).name
      (CoherentNamed.add
        cancellation increment).name :=
    Congruence.coherentAdd_respects
      zero cancellation increment increment
      (Equivalence.NamedEquivalent.symm (by
        simpa only [zero, cancellation, negativeStart,
          CoherentNamed.Coherence.exact,
          CoherentNamed.add,
          CoherentNamed.neg] using
          Arithmetic.Neg.coherentAdd_neg_left start))
      (Equivalence.NamedEquivalent.refl increment.name)
  have associate : Equivalence.NamedEquivalent
      (CoherentNamed.add
        cancellation increment).name
      (CoherentNamed.add negativeStart
        (CoherentNamed.add start increment)).name := by
    simpa only [cancellation,
      CoherentNamed.add] using
      Arithmetic.Add.coherentAdd_assoc
        negativeStart start increment
  simpa only [primitiveDifference, negativeStart] using
    Equivalence.NamedEquivalent.trans begin
      (Equivalence.NamedEquivalent.trans exposeCancellation
        associate)

set_option genInjectivity false in
/-- A retained integration program with a coherent equivalence to its exact original endpoint difference.

The certificate links the program output to the two supplied coherent primitive owners. -/
structure PrimitiveEdge (start finish : CoherentNamed) where
  /-- The original Gaussian integration refinement program for this primitive edge. -/ program :
    Program.Comparison.RefinementProgram
  /-- The retained program output is equivalent to the exact original endpoint difference. -/ integral_eq_difference :
    Equivalence.NamedEquivalent program.output.name
    (primitiveDifference start finish).name

constructive_injectivity PrimitiveEdge

namespace PrimitiveEdge

/-- Retain the original edge program while transporting its primitive endpoint realizations. -/
@[expose] def changeEndpoints {leftStart leftFinish : CoherentNamed}
    (edge : PrimitiveEdge leftStart leftFinish)
    (rightStart rightFinish : CoherentNamed)
    (start : Equivalence.NamedEquivalent leftStart.name rightStart.name)
    (finish : Equivalence.NamedEquivalent leftFinish.name rightFinish.name) :
    PrimitiveEdge rightStart rightFinish :=
  ⟨edge.program, Equivalence.NamedEquivalent.trans edge.integral_eq_difference
    (primitiveDifference_respects _ _ _ _ start finish)⟩

end PrimitiveEdge

set_option genInjectivity false in
/-- An ordered chain of retained primitive edges indexed by its exact start and finish owners.

Each cons joins the original head edge to an endpoint-compatible retained tail; the empty path keeps its original
coherent value. -/
inductive PrimitivePath : CoherentNamed -> CoherentNamed -> Type 2
  /-- The empty primitive path at the retained original coherent value. -/ | nil (value : CoherentNamed) :
    Primitive.PrimitivePath value value
  /-- Join the retained original primitive edge to its endpoint-compatible original tail path. -/ | cons {start middle
    finish : CoherentNamed}
      (head : PrimitiveEdge start middle)
      (tail : Primitive.PrimitivePath middle finish) :
        Primitive.PrimitivePath start finish
  /-- Join two retained endpoint presentations through their original overlap comparison. -/ | overlap
      {start left right finish : CoherentNamed}
      (head : PrimitiveEdge start left)
      (tail : Primitive.PrimitivePath right finish)
      (shared : Equivalence.NamedEquivalent left.name right.name) :
        Primitive.PrimitivePath start finish

constructive_injectivity PrimitivePath

namespace PrimitivePath

/-- Sum the original retained primitive-edge outputs in path order.

The recursion reuses each edge's program output and the retained tail sum, with exact zero at an empty path. -/
@[expose] def integralSum : {start finish : CoherentNamed} ->
    PrimitivePath start finish -> CoherentNamed
  | _, _, .nil _ => CoherentNamed.Coherence.exact 0
  | _, _, .cons head tail =>
      CoherentNamed.add
        head.program.output tail.integralSum
  | _, _, .overlap head tail _ =>
      CoherentNamed.add head.program.output tail.integralSum

/-- The original primitive-path output sum is equivalent to its exact endpoint difference.

Each head program contributes its retained endpoint-difference comparison,
which composes with the original tail comparison in path order. -/
@[expose] def integralSum_eq_difference : {start finish : CoherentNamed} ->
    (path : PrimitivePath start finish) ->
      Equivalence.NamedEquivalent path.integralSum.name
        (primitiveDifference start finish).name
  | _, _, .nil value =>
      Equivalence.NamedEquivalent.symm
        (primitiveDifference_self_zero value)
  | _, _, .cons head tail => by
      apply Equivalence.NamedEquivalent.trans
      · exact Congruence.coherentAdd_respects
          head.program.output (primitiveDifference _ _)
          tail.integralSum (primitiveDifference _ _)
          head.integral_eq_difference tail.integralSum_eq_difference
      · exact primitiveDifference_compose _ _ _
  | _, _, .overlap head tail shared => by
      apply Equivalence.NamedEquivalent.trans
      · exact Congruence.coherentAdd_respects
          head.program.output (primitiveDifference _ _)
          tail.integralSum (primitiveDifference _ _)
          (Equivalence.NamedEquivalent.trans head.integral_eq_difference
            (primitiveDifference_finish_respects _ _ _ shared)) tail.integralSum_eq_difference
      · exact primitiveDifference_compose _ _ _

/-- Append original primitive paths whose middle coherent owner is literally shared.

The recursion preserves every original edge program and overlap certificate
of the first path and returns the second path at its original endpoint. -/
@[expose] def append {start middle finish : CoherentNamed}
    (first : PrimitivePath start middle) (second : PrimitivePath middle finish) :
    PrimitivePath start finish :=
  match first with
  | .nil _ => second
  | .cons head tail => .cons head (tail.append second)
  | .overlap head tail shared => .overlap head (tail.append second) shared

/-- Appending original primitive paths adds their original integral output sums operationally. -/
@[expose] def append_integralSum : {start middle finish : CoherentNamed} →
    (first : PrimitivePath start middle) → (second : PrimitivePath middle finish) →
      Equivalence.NamedEquivalent (first.append second).integralSum.name
        (CoherentNamed.add first.integralSum second.integralSum).name
  | _, _, _, .nil _, _ =>
      Equivalence.NamedEquivalent.symm (Arithmetic.Add.coherentAdd_zero_left _)
  | _, _, _, .cons head tail, second =>
      Equivalence.NamedEquivalent.trans
        (Congruence.coherentAdd_respects
          head.program.output head.program.output
          (tail.append second).integralSum
          (CoherentNamed.add tail.integralSum second.integralSum)
          (Equivalence.NamedEquivalent.refl _) (tail.append_integralSum second))
        (Equivalence.NamedEquivalent.symm (Arithmetic.Add.coherentAdd_assoc _ _ _))
  | _, _, _, .overlap head tail _, second =>
      Equivalence.NamedEquivalent.trans
        (Congruence.coherentAdd_respects
          head.program.output head.program.output
          (tail.append second).integralSum
          (CoherentNamed.add tail.integralSum second.integralSum)
          (Equivalence.NamedEquivalent.refl _) (tail.append_integralSum second))
        (Equivalence.NamedEquivalent.symm (Arithmetic.Add.coherentAdd_assoc _ _ _))

end PrimitivePath

/-- Accumulate the original finite program outputs from the retained initial coherent value.

Each step advances the exact current start by the original indexed program output before reading the remaining original
indices. -/
@[expose] def cumulativePrimitiveFinish : {count : Nat} -> CoherentNamed ->
    (Fin count -> Program.Comparison.RefinementProgram) -> CoherentNamed
  | 0, start, _programs => start
  | count + 1, start, programs =>
      Primitive.cumulativePrimitiveFinish
        (CoherentNamed.add start
          (programs 0).output)
        (fun index : Fin count => programs index.succ)

/-- Build the exact primitive path through the accumulated original program outputs.

Every edge retains its original program and the certificate that its output equals the corresponding successive
primitive difference. -/
@[expose] def cumulativePrimitivePath : {count : Nat} ->
    (start : CoherentNamed) -> (programs : Fin count -> Program.Comparison.RefinementProgram)
      ->
      PrimitivePath start (cumulativePrimitiveFinish start programs)
  | 0, start, _programs => .nil start
  | count + 1, start, programs =>
      let finish := CoherentNamed.add start
        (programs 0).output
      .cons
        { program := programs 0
          integral_eq_difference :=
            increment_eq_primitiveDifference start (programs 0).output }
        (Primitive.cumulativePrimitivePath finish
          (fun index : Fin count => programs index.succ))

/-- The constructed primitive path's output sum is equivalent to the original indexed named sum.

The same finite program function supplies every retained edge and named-sum
entry. Successor recursion compares the head output and the same indexed tail. -/
@[expose] def cumulativePrimitivePath_integralSum_equivalent_sumNamed :
    {count : Nat} -> (start : CoherentNamed) ->
      (programs : Fin count -> Program.Comparison.RefinementProgram) ->
        Equivalence.NamedEquivalent
          (cumulativePrimitivePath start programs).integralSum.name
          (PeriodMatrix.sumNamed fun index => (programs index).output).name
  | 0, start, _programs => by
      change Equivalence.NamedEquivalent
        (CoherentNamed.Coherence.exact 0).name
        (PeriodMatrix.geometricNamed
          (Geometric.GeometricApproximation.exact
            0)).name
      exact Equivalence.NamedEquivalent.symm
        Geometric.Coherent.Comparison.geometricZero_equivalent_exact
  | count + 1, start, programs => by
      change Equivalence.NamedEquivalent
        (CoherentNamed.add
          (programs 0).output
          (cumulativePrimitivePath
            (CoherentNamed.add start
              (programs 0).output)
            (fun index : Fin count => programs index.succ)).integralSum).name
        (CoherentNamed.add
          (programs 0).output
          (PeriodMatrix.sumNamed fun index : Fin count =>
            (programs index.succ).output)).name
      exact Congruence.coherentAdd_respects
        (programs 0).output (programs 0).output
        (cumulativePrimitivePath
          (CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ)).integralSum
        (PeriodMatrix.sumNamed fun index : Fin count => (programs index.succ).output)
        (Equivalence.NamedEquivalent.refl _)
        (Primitive.cumulativePrimitivePath_integralSum_equivalent_sumNamed
          (CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ))

/-- The accumulated original finish is equivalent to original start plus the same indexed program-output sum.

Every step retains its current coherent start and the next program output.
The comparison reassociates their ordered additions without choosing new names. -/
@[expose] def cumulativePrimitiveFinish_equivalent_add_sumNamed :
    {count : Nat} -> (start : CoherentNamed) ->
      (programs : Fin count -> Program.Comparison.RefinementProgram) ->
        Equivalence.NamedEquivalent
          (cumulativePrimitiveFinish start programs).name
          (CoherentNamed.add start
            (PeriodMatrix.sumNamed fun index => (programs index).output)).name
  | 0, start, _programs => by
      let exactZero := CoherentNamed.Coherence.exact 0
      let geometricZero := PeriodMatrix.geometricNamed
        (Geometric.GeometricApproximation.exact 0)
      have insertExact : Equivalence.NamedEquivalent start.name
          (CoherentNamed.add start exactZero).name :=
        Equivalence.NamedEquivalent.symm
          (Arithmetic.Add.coherentAdd_zero_right start)
      have replaceZero : Equivalence.NamedEquivalent
          (CoherentNamed.add start exactZero).name
          (CoherentNamed.add start geometricZero).name :=
        Congruence.coherentAdd_respects
          start start exactZero geometricZero
          (Equivalence.NamedEquivalent.refl start.name)
          (Equivalence.NamedEquivalent.symm
            Geometric.Coherent.Comparison.geometricZero_equivalent_exact)
      simpa only [cumulativePrimitiveFinish, PeriodMatrix.sumNamed, exactZero,
        geometricZero] using
        Equivalence.NamedEquivalent.trans insertExact
          replaceZero
  | count + 1, start, programs => by
      let nextStart := CoherentNamed.add start
        (programs 0).output
      let tailPrograms := fun index : Fin count => programs index.succ
      have tailEquivalent :=
        Primitive.cumulativePrimitiveFinish_equivalent_add_sumNamed nextStart
          tailPrograms
      have associate := Arithmetic.Add.coherentAdd_assoc
        start (programs 0).output
          (PeriodMatrix.sumNamed fun index : Fin count => (programs index.succ).output)
      simpa only [cumulativePrimitiveFinish, PeriodMatrix.sumNamed, nextStart,
        tailPrograms, CoherentNamed.add] using
        Equivalence.NamedEquivalent.trans tailEquivalent
          associate

/-- Starting the original accumulation at exact zero gives the original indexed program-output sum.

The zero-start comparison composes the original accumulated-finish certificate
with the retained named sum's left-zero identity. -/
@[expose] def cumulativePrimitiveFinish_zero_equivalent_sumNamed {count : Nat}
    (programs : Fin count -> Program.Comparison.RefinementProgram) :
    Equivalence.NamedEquivalent
      (cumulativePrimitiveFinish
        (CoherentNamed.Coherence.exact 0) programs).name
      (PeriodMatrix.sumNamed fun index => (programs index).output).name :=
  Equivalence.NamedEquivalent.trans
    (cumulativePrimitiveFinish_equivalent_add_sumNamed
      (CoherentNamed.Coherence.exact 0) programs)
    (Arithmetic.Add.coherentAdd_zero_left
      (PeriodMatrix.sumNamed fun index => (programs index).output))

set_option genInjectivity false in
/-- A retained primitive path whose exact endpoint names are coherently equivalent.

The closure certificate keeps both original start and finish owners rather than identifying their retained processes. -/
structure ClosedPrimitiveBoundary where
  /-- The retained original initial coherent primitive value. -/ start : CoherentNamed
  /-- The retained original final coherent primitive value. -/ finish : CoherentNamed
  /-- The original primitive path indexed by these exact endpoints. -/ path : PrimitivePath start finish
  /-- The original finish and start names are coherently equivalent. -/ closed : Equivalence.NamedEquivalent finish.name
    start.name

constructive_injectivity ClosedPrimitiveBoundary

namespace ClosedPrimitiveBoundary

/-- Close an original primitive path at its literally retained initial coherent owner.

The endpoint type already supplies closure. No comparison of unrelated
endpoints or base coordinates is used to construct the boundary. -/
@[expose] def ofLoop {value : CoherentNamed} (path : PrimitivePath value value) :
    ClosedPrimitiveBoundary :=
  ⟨value, value, path, Equivalence.NamedEquivalent.refl _⟩

/-- Read the original closed boundary path's retained integral output sum. -/
@[expose] def integralSum (boundary : ClosedPrimitiveBoundary) : CoherentNamed :=
  boundary.path.integralSum

/-- The retained closed primitive boundary's output sum is coherently equivalent to exact zero.

The original path supplies its endpoint-difference comparison, and the closure
witness compares the retained finish with its retained start. -/
@[expose] def integralSum_zero (boundary : ClosedPrimitiveBoundary) :
    Equivalence.NamedEquivalent boundary.integralSum.name
      (CoherentNamed.Coherence.exact 0).name := by
  let negativeStart :=
    CoherentNamed.neg boundary.start
  have closeDifference : Equivalence.NamedEquivalent
      (primitiveDifference boundary.start boundary.finish).name
      (primitiveDifference boundary.start boundary.start).name := by
    simpa only [primitiveDifference, negativeStart,
      CoherentNamed.add] using
      Congruence.coherentAdd_respects
        negativeStart negativeStart boundary.finish boundary.start
        (Equivalence.NamedEquivalent.refl negativeStart.name)
        boundary.closed
  exact Equivalence.NamedEquivalent.trans
    boundary.path.integralSum_eq_difference
    (Equivalence.NamedEquivalent.trans closeDifference
      (primitiveDifference_self_zero boundary.start))

end ClosedPrimitiveBoundary

/-- Read the exact-zero coherent comparison for the original closed primitive boundary. -/
@[expose] def exactDifferential_closed_operational_zero
    (boundary : ClosedPrimitiveBoundary) :
    Equivalence.NamedEquivalent boundary.integralSum.name
      (CoherentNamed.Coherence.exact 0).name :=
  boundary.integralSum_zero

end Purelib.Integration.Path.Primitive

end
