module

import Purelib.Examples.Curves.Legendre.RegularCycle.Rotated

/-!
# Closure with distinct actual primitive basepoint owners

The original nonempty six-program schedule supplies all actual admitted
cells and endpoint banks. Its initial representative starts lower-left;
later representatives use the same physical cell caches in cyclic order
starting lower-right. Each row bound is derived from its own closed lift.
-/

namespace TestPurelib.Curves.Legendre.VaryingBasepoint

open Purelib.Examples.Curves.Legendre.RegularCycle
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Gaussian
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- Construct the original schedule with its six actual certified programs and internally admitted primitive banks. -/
def schedule (sheet : Fin 2) : Schedule sheet := Schedule.build sheet

example (sheet : Fin 2) (index : Nat) :
    (Rotated.representatives (schedule sheet) 0).base.entry.point ≠
      (Rotated.representatives (schedule sheet) (index + 1)).base.entry.point :=
  Rotated.retained_basepoints_ne (schedule sheet) index

example (sheet : Fin 2) (index : Nat) :
    ((Rotated.cycle sheet).liftedPath index).cellCount = 4 := Rotated.cycle_cellCount sheet index

example (sheet : Fin 2) :
    (Rotated.representatives (schedule sheet) 0).base.original =
      ((schedule sheet).banks 0).lowerLeft.original := Rotated.representatives_initial_base (schedule sheet)

example (sheet : Fin 2) (index : Nat) :
    (Rotated.representatives (schedule sheet) (index + 1)).base.original =
      ((schedule sheet).banks (index + 1)).lowerRight.original :=
  Rotated.representatives_later_base (schedule sheet) index

example (sheet : Fin 2) (index : Nat) :
    Norm.Basic.normSq (PathModel.mk (Rotated.representatives (schedule sheet) index).sources.zero).integralSample ≤
      quarterRadius 1 index := (Rotated.representatives (schedule sheet) index).zero_error_le

example (sheet : Fin 2) (index : Nat) :
    Norm.Basic.normSq (PathModel.mk (Rotated.representatives (schedule sheet) index).sources.one).integralSample ≤
      quarterRadius 1 index := (Rotated.representatives (schedule sheet) index).one_error_le

example (sheet : Fin 2) (index : Nat) :
    Norm.Basic.normSq (PathModel.mk (Rotated.representatives (schedule sheet) index).sources.scalar).integralSample ≤
      quarterRadius 1 index := (Rotated.representatives (schedule sheet) index).scalar_error_le

example (sheet : Fin 2) : (Rotated.jet (schedule sheet)).cycle = Rotated.cycle sheet :=
  Rotated.jet_cycle (schedule sheet)

example (sheet : Fin 2) (index : Nat) : (Rotated.jet (schedule sheet)).source.stages index =
    Rotated.representatives (schedule sheet) index := Rotated.jet_stage (schedule sheet) index

-- These are contractible regular-chart representatives: the original six finite samples are zero.
example (sheet : Fin 2) (coordinate : Fin 2) (index : Nat) :
    (((Rotated.jet (schedule sheet)).value coordinate).integral.model index).integralSample = 0 :=
  Rotated.jet_value_sample_zero (schedule sheet) coordinate index

example (sheet : Fin 2) (coordinate : Fin 2) (index : Nat) :
    (((Rotated.jet (schedule sheet)).first coordinate).integral.model index).integralSample = 0 :=
  Rotated.jet_first_sample_zero (schedule sheet) coordinate index

example (sheet : Fin 2) (coordinate : Fin 2) (index : Nat) :
    (((Rotated.jet (schedule sheet)).second coordinate).integral.model index).integralSample = 0 :=
  Rotated.jet_second_sample_zero (schedule sheet) coordinate index

-- The actual finite Newton models retain a nonzero polynomial residual, despite those closed integral samples.
example (sheet : Fin 2) (index : Nat) :
    ((schedule sheet).sources index).model.residual.eval (0 : Basic.Canonical) ≠ 0 := by
  rewrite [(schedule sheet).residual_at_zero index]
  decide +kernel

end TestPurelib.Curves.Legendre.VaryingBasepoint
