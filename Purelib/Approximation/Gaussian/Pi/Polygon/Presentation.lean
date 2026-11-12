module

public import Purelib.Approximation.Gaussian.Pi.Polygon
public import Purelib.Data.Gaussian.RationalEmbedding

namespace Purelib.Approximation.Gaussian.Pi.Polygon

open Purelib.Approximation
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian

/-- The polygon name's process center reads the actual full polygon area.

The original sampler evaluates the first quarter and reuses its fourfold area;
`sample_eq_area` proves that this equals the full shoelace computation. -/
public theorem named_center_area (stage : Nat) :
    (named.name.process.ball (show named.name.process.State from stage)).center =
      RationalEmbedding.realPoint (UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage)) :=
  sample_eq_area stage

/-- The polygon approximation uses the original bounded scale-four selector. -/
public theorem refine_readback (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    approximation.refineIndex current target positive = Search.firstQuarterBelow 4 current target := rfl

/-- The polygon selector respects the supplied starting stage. -/
public theorem refine_ge (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    current ≤ approximation.refineIndex current target positive :=
  approximation.refineIndex_ge current target positive

/-- The selected polygon stage pays the positive squared-error request. -/
public theorem refine_accurate (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    approximation.radiusSq (approximation.refineIndex current target positive) < target :=
  approximation.refineIndex_accurate current target positive

/-- The polygon selector returns within its finite logarithmic scan fuel. -/
public theorem refine_le (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    approximation.refineIndex current target positive ≤
      current + (Nat.log2 (Purelib.Data.Rat.Rounding.Floor.ceilNat (4 / target)) + 1) :=
  Search.firstQuarterBelow_le 4 current target

end Purelib.Approximation.Gaussian.Pi.Polygon
