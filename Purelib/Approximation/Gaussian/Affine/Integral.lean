module
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Data.Gaussian.Cast
import Init.Data.Int.Basic

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Data.Gaussian

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Approximation.Gaussian.Affine.Integral

/-- A directly executable affine row, with exact integral coefficients. -/
def affine (a b : Int) (tau : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.add
    (Coherence.exact (Cast.integralGaussian a))
    (CoherentNamed.mul
      (Coherence.exact (Cast.integralGaussian b)) tau)
end Purelib.Approximation.Gaussian.Affine.Integral

end
