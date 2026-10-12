module
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Name.Sampling

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- The displayed Gaussian witness after the indexed canonical refinement of the original name. -/
def ComplexLog.inputSample (input : Named)
  (index : Nat) : Canonical :=
  Gaussian.Process.Sampling.witnessAt
    input.process input.state index

/-- The indexed Gaussian sample remains possible at the original named state. -/
theorem ComplexLog.inputSample_possible_start (input :
  Named) (index : Nat) :
    input.process.Possible input.state (ComplexLog.inputSample input index) :=
  Gaussian.Process.Sampling.witnessAt_possible_start
    input.process input.state index

/-- Later named samples lie within the earlier index's scale-four quarter-radius allowance. -/
theorem inputSample_later_close (input : Named)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq (ComplexLog.inputSample input newIndex
      - ComplexLog.inputSample input oldIndex) ≤
      Geometric.Basic.quarterRadius 4 oldIndex :=
  Gaussian.Process.Sampling.witnessAt_later_close
    input.process input.state order
end Purelib.Approximation.Gaussian.Name.Sampling

end

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Name.Sampling.Exp

/-- The displayed Gaussian witness after the indexed canonical refinement of the original name. -/
def inputSample (input : Named) (index :
  Nat) : Canonical :=
  Gaussian.Process.Sampling.witnessAt
    input.process input.state index

/-- The indexed Gaussian sample remains possible at the original named state. -/
theorem inputSample_possible_start (input :
  Named) (index : Nat) :
    input.process.Possible input.state (inputSample input index) :=
  Gaussian.Process.Sampling.witnessAt_possible_start
    input.process input.state index
end Purelib.Approximation.Gaussian.Name.Sampling.Exp

end

section
@[expose] public section

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace Purelib.Approximation.Gaussian.Name.Sampling.Log

/-- The displayed Gaussian witness after the indexed canonical refinement of the original name. -/
def inputWitness (input : Named) (index :
  Nat) : Canonical :=
  Gaussian.Process.Sampling.witnessAt
    input.process input.state index

/-- The indexed Gaussian witness remains possible at the original named state. -/
theorem inputWitness_possible_start (input :
  Named) (index : Nat) :
    input.process.Possible input.state (inputWitness input index) :=
  Gaussian.Process.Sampling.witnessAt_possible_start
    input.process input.state index
end Purelib.Approximation.Gaussian.Name.Sampling.Log

end

section
@[expose] public section

/-!
# Finite sampling of a progressive name

Every state below is obtained by one explicitly requested finite refinement.
Its displayed sample is the process's finite rational witness at that state.
The construction never selects or names a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)

/-- A progressive name viewed only through a nested sequence of displayed finite witnesses and rational pairwise-error
allowances. -/
def approximation (name : Named) :
  ApproximationData where
  sample := Gaussian.Process.Sampling.witnessAt name.process name.state
  radiusSq := Geometric.Basic.quarterRadius 4
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := Gaussian.Process.Sampling.witnessAt_later_close name.process name.state
  refineIndex current target _ :=
    Search.firstQuarterBelow 4 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 4 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 4 (by decide)
  centerBound := 2 * (1 + name.process.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) name.process.centerBound_nonneg)
  sample_bounded := Gaussian.Process.Sampling.witnessAt_bounded name.process name.state

end Purelib.Approximation.Gaussian.Name.Sampling

end
