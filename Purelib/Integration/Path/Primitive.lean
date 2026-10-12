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
meta import Purelib.Elab.ConstructiveInjectivity

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
@[expose] def primitiveDifference (start finish : Name.Coherent.CoherentNamed) : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.add
    (Name.Coherent.CoherentNamed.neg start) finish

/-- An original value's difference from itself is coherently equivalent to exact zero.

The finite comparison retains the same coherent value as both endpoints and
uses its additive cancellation certificate at every requested tolerance. -/
@[expose] def primitiveDifference_self_zero (value : Name.Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent (Primitive.primitiveDifference value value).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  simpa only [Primitive.primitiveDifference,
    Name.Coherent.CoherentNamed.add,
    Name.Coherent.CoherentNamed.neg,
    Name.Coherent.CoherentNamed.Coherence.exact] using
    Arithmetic.Neg.coherentAdd_neg_left value

/-- Adding original endpoint-compatible primitive differences is equivalent to the outer endpoint difference.

The comparison retains the exact three coherent names and composes their original additive and cancellation
certificates. -/
@[expose] def primitiveDifference_compose (start middle finish : Name.Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        (Primitive.primitiveDifference start middle)
        (Primitive.primitiveDifference middle finish)).name
      (Primitive.primitiveDifference start finish).name := by
  let negativeStart := Name.Coherent.CoherentNamed.neg start
  let negativeMiddle := Name.Coherent.CoherentNamed.neg middle
  let middleFinish := Name.Coherent.CoherentNamed.add
    negativeMiddle finish
  have associate : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.add negativeStart middle)
        middleFinish).name
      (Name.Coherent.CoherentNamed.add negativeStart
        (Name.Coherent.CoherentNamed.add middle
          middleFinish)).name :=
    Arithmetic.Add.coherentAdd_assoc
      negativeStart middle middleFinish
  have exposeCancellation : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add middle middleFinish).name
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.add middle negativeMiddle)
        finish).name :=
    Equivalence.NamedEquivalent.symm (by
      simpa only [middleFinish,
        Name.Coherent.CoherentNamed.add] using
        Arithmetic.Add.coherentAdd_assoc
          middle negativeMiddle finish)
  let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
  have cancellation : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add middle negativeMiddle).name
      zero.name := by
    simpa only [negativeMiddle, zero,
      Name.Coherent.CoherentNamed.neg,
      Name.Coherent.CoherentNamed.Coherence.exact,
      Name.Coherent.CoherentNamed.add] using
      Arithmetic.Neg.coherentAdd_neg_right middle
  have removeCancellation : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.add middle negativeMiddle)
        finish).name
      finish.name :=
    Equivalence.NamedEquivalent.trans
      (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
        (Name.Coherent.CoherentNamed.add middle negativeMiddle)
        zero finish finish cancellation
        (Equivalence.NamedEquivalent.refl finish.name))
      (Arithmetic.Add.coherentAdd_zero_left finish)
  have reduceTail : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add middle middleFinish).name
      finish.name :=
    Equivalence.NamedEquivalent.trans exposeCancellation
      removeCancellation
  have reduceUnderStart : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add negativeStart
        (Name.Coherent.CoherentNamed.add middle middleFinish)).name
      (Name.Coherent.CoherentNamed.add
        negativeStart finish).name :=
    Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      negativeStart negativeStart
      (Name.Coherent.CoherentNamed.add middle middleFinish)
      finish
      (Equivalence.NamedEquivalent.refl negativeStart.name)
      reduceTail
  simpa only [Primitive.primitiveDifference, negativeStart, negativeMiddle,
    middleFinish, Name.Coherent.CoherentNamed.add,
    Name.Coherent.CoherentNamed.neg] using
    Equivalence.NamedEquivalent.trans associate reduceUnderStart

/-- An original increment is equivalent to the difference from the original start to start plus that increment.

The retained start and increment supply both endpoint names. The comparison
keeps the same increment owner while cancelling only the repeated start. -/
@[expose] def increment_eq_primitiveDifference (start increment : Name.Coherent.CoherentNamed) :
    Equivalence.NamedEquivalent increment.name
      (Primitive.primitiveDifference start
        (Name.Coherent.CoherentNamed.add start increment)).name := by
  let negativeStart := Name.Coherent.CoherentNamed.neg start
  let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
  let cancellation := Name.Coherent.CoherentNamed.add
    negativeStart start
  have begin : Equivalence.NamedEquivalent increment.name
      (Name.Coherent.CoherentNamed.add zero increment).name :=
    Equivalence.NamedEquivalent.symm
      (Arithmetic.Add.coherentAdd_zero_left increment)
  have exposeCancellation : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add zero increment).name
      (Name.Coherent.CoherentNamed.add
        cancellation increment).name :=
    Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      zero cancellation increment increment
      (Equivalence.NamedEquivalent.symm (by
        simpa only [zero, cancellation, negativeStart,
          Name.Coherent.CoherentNamed.Coherence.exact,
          Name.Coherent.CoherentNamed.add,
          Name.Coherent.CoherentNamed.neg] using
          Arithmetic.Neg.coherentAdd_neg_left start))
      (Equivalence.NamedEquivalent.refl increment.name)
  have associate : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.add
        cancellation increment).name
      (Name.Coherent.CoherentNamed.add negativeStart
        (Name.Coherent.CoherentNamed.add start increment)).name := by
    simpa only [cancellation,
      Name.Coherent.CoherentNamed.add] using
      Arithmetic.Add.coherentAdd_assoc
        negativeStart start increment
  simpa only [Primitive.primitiveDifference, negativeStart] using
    Equivalence.NamedEquivalent.trans begin
      (Equivalence.NamedEquivalent.trans exposeCancellation
        associate)

set_option genInjectivity false in
/-- A retained integration program with a coherent equivalence to its exact original endpoint difference.

The certificate links the program output to the two supplied coherent primitive owners. -/
structure PrimitiveEdge (start finish : Name.Coherent.CoherentNamed) where
  /-- The original Gaussian integration refinement program for this primitive edge. -/ program :
    Integration.Program.Comparison.RefinementProgram
  /-- The retained program output is equivalent to the exact original endpoint difference. -/ integral_eq_difference :
    Equivalence.NamedEquivalent program.output.name
    (Primitive.primitiveDifference start finish).name

constructive_injectivity PrimitiveEdge

set_option genInjectivity false in
/-- An ordered chain of retained primitive edges indexed by its exact start and finish owners.

Each cons joins the original head edge to an endpoint-compatible retained tail; the empty path keeps its original
coherent value. -/
inductive PrimitivePath : Name.Coherent.CoherentNamed -> Name.Coherent.CoherentNamed -> Type 2
  /-- The empty primitive path at the retained original coherent value. -/ | nil (value : Name.Coherent.CoherentNamed) :
    Purelib.Integration.Path.Primitive.PrimitivePath value value
  /-- Join the retained original primitive edge to its endpoint-compatible original tail path. -/ | cons {start middle
    finish : Name.Coherent.CoherentNamed}
      (head : Primitive.PrimitiveEdge start middle)
      (tail : Purelib.Integration.Path.Primitive.PrimitivePath middle finish) :
        Purelib.Integration.Path.Primitive.PrimitivePath start finish

constructive_injectivity PrimitivePath

namespace PrimitivePath

/-- Sum the original retained primitive-edge outputs in path order.

The recursion reuses each edge's program output and the retained tail sum, with exact zero at an empty path. -/
@[expose] def integralSum : {start finish : Name.Coherent.CoherentNamed} ->
    Primitive.PrimitivePath start finish -> Name.Coherent.CoherentNamed
  | _, _, .nil _ => Name.Coherent.CoherentNamed.Coherence.exact 0
  | _, _, .cons head tail =>
      Name.Coherent.CoherentNamed.add
        head.program.output tail.integralSum

/-- The original primitive-path output sum is equivalent to its exact endpoint difference.

Each head program contributes its retained endpoint-difference comparison,
which composes with the original tail comparison in path order. -/
@[expose] def integralSum_eq_difference : {start finish : Name.Coherent.CoherentNamed} ->
    (path : Primitive.PrimitivePath start finish) ->
      Equivalence.NamedEquivalent path.integralSum.name
        (Primitive.primitiveDifference start finish).name
  | _, _, .nil value =>
      Equivalence.NamedEquivalent.symm
        (Primitive.primitiveDifference_self_zero value)
  | _, _, .cons head tail => by
      apply Equivalence.NamedEquivalent.trans
      · exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          head.program.output (Primitive.primitiveDifference _ _)
          tail.integralSum (Primitive.primitiveDifference _ _)
          head.integral_eq_difference tail.integralSum_eq_difference
      · exact Primitive.primitiveDifference_compose _ _ _

end PrimitivePath

/-- Accumulate the original finite program outputs from the retained initial coherent value.

Each step advances the exact current start by the original indexed program output before reading the remaining original
indices. -/
@[expose] def cumulativePrimitiveFinish : {count : Nat} -> Name.Coherent.CoherentNamed ->
    (Fin count -> Integration.Program.Comparison.RefinementProgram) -> Name.Coherent.CoherentNamed
  | 0, start, _programs => start
  | count + 1, start, programs =>
      Purelib.Integration.Path.Primitive.cumulativePrimitiveFinish
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add start
          (programs 0).output)
        (fun index : Fin count => programs index.succ)

/-- Build the exact primitive path through the accumulated original program outputs.

Every edge retains its original program and the certificate that its output equals the corresponding successive
primitive difference. -/
@[expose] def cumulativePrimitivePath : {count : Nat} ->
    (start : Name.Coherent.CoherentNamed) -> (programs : Fin count -> Integration.Program.Comparison.RefinementProgram)
      ->
      Primitive.PrimitivePath start (Primitive.cumulativePrimitiveFinish start programs)
  | 0, start, _programs => .nil start
  | count + 1, start, programs =>
      let finish := Name.Coherent.CoherentNamed.add start
        (programs 0).output
      .cons
        { program := programs 0
          integral_eq_difference :=
            Primitive.increment_eq_primitiveDifference start (programs 0).output }
        (Purelib.Integration.Path.Primitive.cumulativePrimitivePath finish
          (fun index : Fin count => programs index.succ))

/-- The constructed primitive path's output sum is equivalent to the original indexed named sum.

The same finite program function supplies every retained edge and named-sum
entry. Successor recursion compares the head output and the same indexed tail. -/
@[expose] def cumulativePrimitivePath_integralSum_equivalent_sumNamed :
    {count : Nat} -> (start : Name.Coherent.CoherentNamed) ->
      (programs : Fin count -> Integration.Program.Comparison.RefinementProgram) ->
        Equivalence.NamedEquivalent
          (Primitive.cumulativePrimitivePath start programs).integralSum.name
          (PeriodMatrix.sumNamed fun index => (programs index).output).name
  | 0, start, _programs => by
      change Equivalence.NamedEquivalent
        (Name.Coherent.CoherentNamed.Coherence.exact 0).name
        (PeriodMatrix.geometricNamed
          (Geometric.GeometricApproximation.exact
            0)).name
      exact Equivalence.NamedEquivalent.symm
        Geometric.Coherent.Comparison.geometricZero_equivalent_exact
  | count + 1, start, programs => by
      change Equivalence.NamedEquivalent
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          (programs 0).output
          (Primitive.cumulativePrimitivePath
            (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add start
              (programs 0).output)
            (fun index : Fin count => programs index.succ)).integralSum).name
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add
          (programs 0).output
          (PeriodMatrix.sumNamed fun index : Fin count =>
            (programs index.succ).output)).name
      exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
        (programs 0).output (programs 0).output
        (Primitive.cumulativePrimitivePath
          (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ)).integralSum
        (PeriodMatrix.sumNamed fun index : Fin count => (programs index.succ).output)
        (Equivalence.NamedEquivalent.refl _)
        (Purelib.Integration.Path.Primitive.cumulativePrimitivePath_integralSum_equivalent_sumNamed
          (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ))

/-- The accumulated original finish is equivalent to original start plus the same indexed program-output sum.

Every step retains its current coherent start and the next program output.
The comparison reassociates their ordered additions without choosing new names. -/
@[expose] def cumulativePrimitiveFinish_equivalent_add_sumNamed :
    {count : Nat} -> (start : Name.Coherent.CoherentNamed) ->
      (programs : Fin count -> Integration.Program.Comparison.RefinementProgram) ->
        Equivalence.NamedEquivalent
          (Primitive.cumulativePrimitiveFinish start programs).name
          (Name.Coherent.CoherentNamed.add start
            (PeriodMatrix.sumNamed fun index => (programs index).output)).name
  | 0, start, _programs => by
      let exactZero := Name.Coherent.CoherentNamed.Coherence.exact 0
      let geometricZero := PeriodMatrix.geometricNamed
        (Geometric.GeometricApproximation.exact 0)
      have insertExact : Equivalence.NamedEquivalent start.name
          (Name.Coherent.CoherentNamed.add start exactZero).name :=
        Equivalence.NamedEquivalent.symm
          (Arithmetic.Add.coherentAdd_zero_right start)
      have replaceZero : Equivalence.NamedEquivalent
          (Name.Coherent.CoherentNamed.add start exactZero).name
          (Name.Coherent.CoherentNamed.add start geometricZero).name :=
        Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          start start exactZero geometricZero
          (Equivalence.NamedEquivalent.refl start.name)
          (Equivalence.NamedEquivalent.symm
            Geometric.Coherent.Comparison.geometricZero_equivalent_exact)
      simpa only [Primitive.cumulativePrimitiveFinish, PeriodMatrix.sumNamed, exactZero,
        geometricZero] using
        Equivalence.NamedEquivalent.trans insertExact
          replaceZero
  | count + 1, start, programs => by
      let nextStart := Name.Coherent.CoherentNamed.add start
        (programs 0).output
      let tailPrograms := fun index : Fin count => programs index.succ
      have tailEquivalent :=
        Purelib.Integration.Path.Primitive.cumulativePrimitiveFinish_equivalent_add_sumNamed nextStart
          tailPrograms
      have associate := Arithmetic.Add.coherentAdd_assoc
        start (programs 0).output
          (PeriodMatrix.sumNamed fun index : Fin count => (programs index.succ).output)
      simpa only [Primitive.cumulativePrimitiveFinish, PeriodMatrix.sumNamed, nextStart,
        tailPrograms, Name.Coherent.CoherentNamed.add] using
        Equivalence.NamedEquivalent.trans tailEquivalent
          associate

/-- Starting the original accumulation at exact zero gives the original indexed program-output sum.

The zero-start comparison composes the original accumulated-finish certificate
with the retained named sum's left-zero identity. -/
@[expose] def cumulativePrimitiveFinish_zero_equivalent_sumNamed {count : Nat}
    (programs : Fin count -> Integration.Program.Comparison.RefinementProgram) :
    Equivalence.NamedEquivalent
      (Primitive.cumulativePrimitiveFinish
        (Name.Coherent.CoherentNamed.Coherence.exact 0) programs).name
      (PeriodMatrix.sumNamed fun index => (programs index).output).name :=
  Equivalence.NamedEquivalent.trans
    (Primitive.cumulativePrimitiveFinish_equivalent_add_sumNamed
      (Name.Coherent.CoherentNamed.Coherence.exact 0) programs)
    (Arithmetic.Add.coherentAdd_zero_left
      (PeriodMatrix.sumNamed fun index => (programs index).output))

set_option genInjectivity false in
/-- A retained primitive path whose exact endpoint names are coherently equivalent.

The closure certificate keeps both original start and finish owners rather than identifying their retained processes. -/
structure ClosedPrimitiveBoundary where
  /-- The retained original initial coherent primitive value. -/ start : Name.Coherent.CoherentNamed
  /-- The retained original final coherent primitive value. -/ finish : Name.Coherent.CoherentNamed
  /-- The original primitive path indexed by these exact endpoints. -/ path : Primitive.PrimitivePath start finish
  /-- The original finish and start names are coherently equivalent. -/ closed : Equivalence.NamedEquivalent finish.name
    start.name

constructive_injectivity ClosedPrimitiveBoundary

namespace ClosedPrimitiveBoundary

/-- Read the original closed boundary path's retained integral output sum. -/
@[expose] def integralSum (boundary : Primitive.ClosedPrimitiveBoundary) : Name.Coherent.CoherentNamed :=
  boundary.path.integralSum

/-- The retained closed primitive boundary's output sum is coherently equivalent to exact zero.

The original path supplies its endpoint-difference comparison, and the closure
witness compares the retained finish with its retained start. -/
@[expose] def integralSum_zero (boundary : Primitive.ClosedPrimitiveBoundary) :
    Equivalence.NamedEquivalent boundary.integralSum.name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  let negativeStart :=
    Name.Coherent.CoherentNamed.neg boundary.start
  have closeDifference : Equivalence.NamedEquivalent
      (Primitive.primitiveDifference boundary.start boundary.finish).name
      (Primitive.primitiveDifference boundary.start boundary.start).name := by
    simpa only [Primitive.primitiveDifference, negativeStart,
      Name.Coherent.CoherentNamed.add] using
      Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
        negativeStart negativeStart boundary.finish boundary.start
        (Equivalence.NamedEquivalent.refl negativeStart.name)
        boundary.closed
  exact Equivalence.NamedEquivalent.trans
    boundary.path.integralSum_eq_difference
    (Equivalence.NamedEquivalent.trans closeDifference
      (Primitive.primitiveDifference_self_zero boundary.start))

end ClosedPrimitiveBoundary

/-- Read the exact-zero coherent comparison for the original closed primitive boundary. -/
@[expose] def exactDifferential_closed_operational_zero
    (boundary : Primitive.ClosedPrimitiveBoundary) :
    Equivalence.NamedEquivalent boundary.integralSum.name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  boundary.integralSum_zero

end Purelib.Integration.Path.Primitive

end
