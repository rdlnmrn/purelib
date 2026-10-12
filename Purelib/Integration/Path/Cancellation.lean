module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Neg
public import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Reversal
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Integration.Program.Gaussian.Name

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

namespace Purelib.Integration.Path.Cancellation

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- Two retained coherent boundary names with a certificate that the reverse is equivalent to the negative forward name.
-/
structure BoundaryPair where
  /-- The retained original forward name or refinement program. -/ forward : Name.Coherent.CoherentNamed
  /-- The exact retained reverse coherent boundary name. -/ reverse : Name.Coherent.CoherentNamed
  /-- The reverse name is equivalent to the negative of the exact original forward name. -/ reverse_eq_neg :
    Equivalence.NamedEquivalent reverse.name
    (Name.Coherent.CoherentNamed.neg forward).name

constructive_injectivity BoundaryPair

namespace BoundaryPair

section
open Purelib.Approximation.Gaussian
open Purelib.Integration.Path
/-- Add the exact retained forward and reverse coherent names. -/
def sum (pair : Cancellation.BoundaryPair) : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.add pair.forward pair.reverse

/-- The retained paired boundary sum is equivalent to the exact zero name. -/
def sum_zero (pair : Cancellation.BoundaryPair) :
    Equivalence.NamedEquivalent pair.sum.name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  Equivalence.NamedEquivalent.trans
    (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
      pair.forward pair.forward pair.reverse
      (Name.Coherent.CoherentNamed.neg pair.forward)
      (Equivalence.NamedEquivalent.refl pair.forward.name)
      pair.reverse_eq_neg)
    (Arithmetic.Neg.coherentAdd_neg_right pair.forward)

end

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Integration.Program in
/-- The reversed program and original program use identical emitted sample indices at every stage. -/
public theorem reverse_emittedSampleIndex (program : Comparison.RefinementProgram)
    (models : Comparison.ReversalModels program) (index : Nat) :
    Equivalence.Sampling.emittedSampleIndex
        (Gaussian.Basic.RefinementProgram.reverse
          program models).approximation index =
      Equivalence.Sampling.emittedSampleIndex program.approximation
        index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      unfold Equivalence.Sampling.emittedSampleIndex
      rw [Process.Sampling.stateAt_succ,
        Process.Sampling.stateAt_succ]
      change Geometric.Search.firstQuarterBelow program.errorScale
          (Equivalence.Sampling.emittedSampleIndex
            (Gaussian.Basic.RefinementProgram.reverse
              program models).approximation index)
          (Process.Sampling.refinementTarget (index + 1)) =
        Geometric.Search.firstQuarterBelow program.errorScale
          (Equivalence.Sampling.emittedSampleIndex
            program.approximation index)
          (Process.Sampling.refinementTarget (index + 1))
      rw [inductionHypothesis]

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Program in
/-- Retain the original program output and certified reversal output as a cancelling coherent boundary pair.

The construction uses the identical emitted-index sequence and original sample-negation certificates, retaining both
output owners. -/
def ofProgramReversal (program : Comparison.RefinementProgram)
    (models : Comparison.ReversalModels program) : Cancellation.BoundaryPair where
  forward := program.output
  reverse :=
    (Gaussian.Basic.RefinementProgram.reverse
      program models).output
  reverse_eq_neg := by
    apply Sequence.Equivalence.approximationEquivalentOfSamplesEq
    intro index
    let reverseProgram :=
      Gaussian.Basic.RefinementProgram.reverse
        program models
    rw [show
        (Name.Sampling.approximation
          reverseProgram.output.name).sample index =
          reverseProgram.approximation.sample
            (Equivalence.Sampling.emittedSampleIndex
              reverseProgram.approximation index) by
        exact Equivalence.Sampling.emittedSample_eq
          reverseProgram.approximation index]
    rw [show
        (Name.Coherent.CoherentNamed.neg program.output).name =
          Name.Basic.Named.neg program.output.name by rfl,
      Coherent.Additive.negSampling_sample]
    rw [show
        (Name.Sampling.approximation program.output.name).sample
            index =
          program.approximation.sample
            (Equivalence.Sampling.emittedSampleIndex
              program.approximation index) by
        exact Equivalence.Sampling.emittedSample_eq
          program.approximation index,
      Cancellation.BoundaryPair.reverse_emittedSampleIndex program models index]
    exact Gaussian.Basic.RefinementProgram.reverse_integralSample
      program models
        (Equivalence.Sampling.emittedSampleIndex
          program.approximation index)

end BoundaryPair

open Purelib.Integration.Program in
set_option genInjectivity false in
/-- An original refinement program retained together with its indexed reversal models. -/
structure ProgramBoundaryPair where
  /-- The retained original forward name or refinement program. -/ forward : Comparison.RefinementProgram
  /-- The retained reversal models indexed by the exact original forward program. -/ reversal :
    Comparison.ReversalModels forward

constructive_injectivity ProgramBoundaryPair

namespace ProgramBoundaryPair

open Purelib.Integration.Path in
/-- Read the exact original program and retained reversal as a cancelling coherent boundary pair. -/
def toBoundaryPair (pair : Cancellation.ProgramBoundaryPair) : Cancellation.BoundaryPair :=
  Cancellation.BoundaryPair.ofProgramReversal pair.forward pair.reversal

end ProgramBoundaryPair

open Purelib.Approximation.Gaussian
open Purelib.Integration.Path
/-- Add the retained forward-plus-reverse boundary names in original finite index order. -/
def boundarySum : {count : Nat} -> (Fin count -> Cancellation.BoundaryPair) -> Name.Coherent.CoherentNamed
  | 0, _ => Name.Coherent.CoherentNamed.Coherence.exact 0
  | count + 1, pairs =>
      Name.Coherent.CoherentNamed.add (pairs 0).sum
        (Purelib.Integration.Path.Cancellation.boundarySum fun index : Fin count => pairs index.succ)

/-- The finite sum of retained cancelling boundary pairs is equivalent to the exact zero name. -/
def boundarySum_zero {count : Nat} (pairs : Fin count -> Cancellation.BoundaryPair) :
    Equivalence.NamedEquivalent (Cancellation.boundarySum pairs).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  induction count with
  | zero =>
      exact Equivalence.NamedEquivalent.refl
        (Name.Coherent.CoherentNamed.Coherence.exact 0).name
  | succ count inductionHypothesis =>
      let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
      let tail := Cancellation.boundarySum fun index : Fin count => pairs index.succ
      have cancelHead : Equivalence.NamedEquivalent (pairs 0).sum.name zero.name := by
        simpa only [zero] using (pairs 0).sum_zero
      have cancelTail : Equivalence.NamedEquivalent tail.name zero.name := by
        simpa only [tail, zero] using
          inductionHypothesis (fun index : Fin count => pairs index.succ)
      exact Equivalence.NamedEquivalent.trans
        (by
          change Equivalence.NamedEquivalent
            (Name.Coherent.CoherentNamed.add (pairs 0).sum tail).name
            (Name.Coherent.CoherentNamed.add zero zero).name
          exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
            (pairs 0).sum zero tail zero cancelHead cancelTail)
        (Arithmetic.Add.coherentAdd_zero_right zero)

end Purelib.Integration.Path.Cancellation

end
