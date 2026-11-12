module

public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Gaussian increments along the same retained increasing interval walk

The original finite edge list supplies the exact oriented scalar telescope.
No functions or endpoint owners are identified by the statement.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk

open Purelib
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid

/-- Primitive increments telescope along an increasing finite interval walk. -/
theorem telescope (value : Rational → Data.Gaussian.Basic.Canonical) {intervals : List
  PreparedAxisPartitions.Interval} :
    {first last : Rational} → (walk : AxisWalks.IncreasingWalk intervals first last) →
      Basic.gaussianSum (walk.edges.map fun interval => value interval.upper - value
        interval.lower) = value last - value first
  | _, _, .nil _ => by change (0 : Data.Gaussian.Basic.Canonical) = _ - _; ring1
  | _, _, .cons interval _ tail => by
      change (value interval.upper - value interval.lower) + Basic.gaussianSum _ = _
      rw [telescope value
        tail]
      simp only [id_eq]
      ring1

end Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk
