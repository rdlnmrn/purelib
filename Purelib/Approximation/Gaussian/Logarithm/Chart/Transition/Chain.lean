module
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transition
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Init.Prelude
import Purelib.Approximation.ElementaryFunction.Exponential.Operational.Inverse
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Chain

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

open Purelib.Approximation

/-- Sum a finite sequence of explicit chart transitions. The recursion is on the displayed finite list only. -/
@[expose] def transitionChain {input : CoherentNamed} :
    Anchored.AnchoredChart input → List (Anchored.AnchoredChart input) → CoherentNamed
  | _start, [] =>
      Coherence.exact 0
  | start, next :: rest =>
      CoherentNamed.add
        (Transition.transition start next)
          (Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Chain.transitionChain next rest)

/-- Every finite chart-transition chain has unit exponential.

This is the finite monodromy statement: it does not identify the chain with a completed multiple of any non-rational
constant. -/
@[expose] def exp_transitionChain_unit {input : CoherentNamed} :
    (start : Anchored.AnchoredChart input) → (rest : List (Anchored.AnchoredChart input)) →
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Approximation.Gaussian.Logarithm.Chart.Transition.Chain.transitionChain start rest).name)
      (Named.exact 1)
  | _start, [] => by
      simpa only [Approximation.Gaussian.Logarithm.Chart.Transition.Chain.transitionChain,
        Coherence.exact] using
        Exponential.Progressive.Range.Exact.automaticExp_zero
  | start, next :: rest => by
      let head := Transition.transition start next
      let tail := Approximation.Gaussian.Logarithm.Chart.Transition.Chain.transitionChain next rest
      let headExp := Exponential.Progressive.Range.Coherent.exp head.name
      let tailExp := Exponential.Progressive.Range.Coherent.exp tail.name
      let one :=
        Coherence.exact 1
      have productToOne : Gaussian.Equivalence.NamedEquivalent
          (Named.mul
            headExp.name tailExp.name)
          (Named.mul
            one.name one.name) :=
        Congruence.coherentMul_respects headExp one tailExp one
          (Transition.exp_transition_unit start next)
          (Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Chain.exp_transitionChain_unit next rest)
      exact NamedEquivalent.trans
        (NamedEquivalent.symm
          (by
            simpa only [Approximation.Gaussian.Logarithm.Chart.Transition.Chain.transitionChain, head, tail, headExp,
              tailExp,
              CoherentNamed.add,
              Exponential.Progressive.Range.Coherent.exp] using
              Exponential.Progressive.Range.Addition.automaticExp_add head tail))
        (NamedEquivalent.trans
          productToOne
          (by
            simpa only [one,
              Coherence.exact] using
              Mul.coherentMul_one_right one))

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Chain
