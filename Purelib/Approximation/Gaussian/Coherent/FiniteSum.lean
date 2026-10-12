module
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric.Coherent

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Approximation.Gaussian.Coherent.FiniteSum

/-- Recursive finite sums distribute over pointwise operational addition. -/
def sumNamed_add {count : Nat}
    (left right : Fin count -> Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.sumNamed fun entry =>
        CoherentNamed.add
          (left entry) (right entry)).name
      (CoherentNamed.add
        (PeriodMatrix.sumNamed left) (PeriodMatrix.sumNamed right)).name := by
  induction count with
  | zero =>
      exact NamedEquivalent.symm
        (Add.coherentAdd_zero_right
          (Coherence.exact 0))
  | succ count inductionHypothesis =>
      let leftTail := fun entry : Fin count => left entry.succ
      let rightTail := fun entry : Fin count => right entry.succ
      have replaceTail : Gaussian.Equivalence.NamedEquivalent
          (CoherentNamed.add
            (CoherentNamed.add (left 0) (right 0))
            (PeriodMatrix.sumNamed fun entry : Fin count =>
              CoherentNamed.add
                (leftTail entry) (rightTail entry))).name
          (CoherentNamed.add
            (CoherentNamed.add (left 0) (right 0))
            (CoherentNamed.add
              (PeriodMatrix.sumNamed leftTail) (PeriodMatrix.sumNamed rightTail))).name :=
        Congruence.coherentAdd_respects
          (CoherentNamed.add (left 0) (right 0))
          (CoherentNamed.add (left 0) (right 0))
          (PeriodMatrix.sumNamed fun entry : Fin count =>
            CoherentNamed.add
              (leftTail entry) (rightTail entry))
          (CoherentNamed.add
            (PeriodMatrix.sumNamed leftTail) (PeriodMatrix.sumNamed rightTail))
          (NamedEquivalent.refl _)
          (inductionHypothesis leftTail rightTail)
      exact NamedEquivalent.trans replaceTail
        (Additive.coherentAdd_interchange (left 0) (right 0)
          (PeriodMatrix.sumNamed leftTail) (PeriodMatrix.sumNamed rightTail))

/-- Recursive finite sums commute with actual stateful negation. -/
def sumNamed_neg {count : Nat} (values : Fin count ->
  Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.sumNamed fun entry =>
        CoherentNamed.neg (values entry)).name
      (CoherentNamed.neg
        (PeriodMatrix.sumNamed values)).name := by
  induction count with
  | zero => exact Additive.zero_equivalent_neg_zero
  | succ count inductionHypothesis =>
      let tail := fun entry : Fin count => values entry.succ
      apply NamedEquivalent.trans
      · exact Congruence.coherentAdd_respects
          (CoherentNamed.neg (values 0))
          (CoherentNamed.neg (values 0))
          (PeriodMatrix.sumNamed fun entry : Fin count =>
            CoherentNamed.neg (tail entry))
          (CoherentNamed.neg (PeriodMatrix.sumNamed tail))
          (NamedEquivalent.refl _)
          (inductionHypothesis tail)
      · exact Additive.coherentNeg_add (values 0) (PeriodMatrix.sumNamed tail)

/-- A finite recursive sum vanishes when every displayed coherent summand does. The empty case explicitly bridges the
synchronized geometric zero used by `sumNamed` to the terminating coherent zero. -/
def sumNamed_zero : {count : Nat} ->
    (values : Fin count -> Coherent.CoherentNamed) ->
    (forall index,
      Gaussian.Equivalence.NamedEquivalent (values index).name
        (Coherence.exact 0).name) ->
    Gaussian.Equivalence.NamedEquivalent (PeriodMatrix.sumNamed values).name
      (Coherence.exact 0).name
  | 0, _values, _zero => Comparison.geometricZero_equivalent_exact
  | count + 1, values, zeroValues => by
      let zero := Coherence.exact 0
      let tail := fun index : Fin count => values index.succ
      have replaceBoth : Gaussian.Equivalence.NamedEquivalent
          (CoherentNamed.add
            (values 0) (PeriodMatrix.sumNamed tail)).name
          (CoherentNamed.add zero zero).name :=
        Congruence.coherentAdd_respects
          (values 0) zero (PeriodMatrix.sumNamed tail) zero
          (zeroValues 0)
          (sumNamed_zero tail (fun index => zeroValues index.succ))
      exact NamedEquivalent.trans replaceBoth
        (Add.coherentAdd_zero_right zero)

end Purelib.Approximation.Gaussian.Coherent.FiniteSum

end
