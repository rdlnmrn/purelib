module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Matrix.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre

open Purelib.LinearAlgebra.Matrix

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
@[expose] public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

namespace Purelib.Curves.Legendre.FractionalAction.Standard

/-- The standard combined path confirms the locked order `one * zero`. -/
theorem standard_combined_order {parameter :
    Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (loops : Monodromy.StandardLoops frame) :
    Words.wordMatrix
        loops.combinedPath.word =
      Multiplication.mul
        Monodromy.oneMatrix
        Monodromy.zeroMatrix :=
  loops.combinedPath_matrix

/-- The standard infinity path is the certified left inverse of that combined order. -/
theorem standard_infinity_left_inverse :
    Multiplication.mul
        Monodromy.infinityMatrix
        (Multiplication.mul
          Monodromy.oneMatrix
          Monodromy.zeroMatrix) =
      Multiplication.identity :=
  Monodromy.explicit_loop_product_left

/-- Productive infinity transport undoes the combined zero-then-one action. -/
def standard_infinity_after_combined (tau :
  Coherent.CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation
      Monodromy.infinityMatrix
      (Multiplication.mul
        Monodromy.oneMatrix
        Monodromy.zeroMatrix) tau) :
    Gaussian.Equivalence.NamedEquivalent preparation.nestedOutput.name tau.name :=
  Inverse.fractionalLinear_inverse_of_mul_eq_identity
    Monodromy.infinityMatrix
    (Multiplication.mul
      Monodromy.oneMatrix
      Monodromy.zeroMatrix)
    tau preparation
    Monodromy.explicit_loop_product_left

/-- Productive combined zero-then-one transport also undoes infinity transport, using the independently certified
reverse multiplication order. -/
def standard_combined_after_infinity (tau :
  Coherent.CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation
      (Multiplication.mul
        Monodromy.oneMatrix
        Monodromy.zeroMatrix)
      Monodromy.infinityMatrix tau) :
    Gaussian.Equivalence.NamedEquivalent preparation.nestedOutput.name tau.name :=
  Inverse.fractionalLinear_inverse_of_mul_eq_identity
    (Multiplication.mul
      Monodromy.oneMatrix
      Monodromy.zeroMatrix)
    Monodromy.infinityMatrix tau preparation
    Monodromy.explicit_loop_product_right

end Purelib.Curves.Legendre.FractionalAction.Standard

end
