module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Grid
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Fixed-order raw-winding selection

The original finite child order retains each grid child and selects a
nonzero raw winding, using exact additivity for the final fallback.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Selection

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Fixed finite order on the four children.

The original lower-left, upper-left, lower-right order is tested by
raw winding before the upper-right fallback. The returned child is
the original retained grid entry with its same parent and refinement data. -/
@[expose] public def firstNonzeroChild
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {state : State.Raw.RawWindingState p ambient} (grid : Subdivision.Raw.Grid.RawFourGrid state) :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box :=
  if Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box ≠ 0 then grid.lowerLeft
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box ≠ 0 then grid.upperLeft
  else if Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box ≠ 0 then grid.lowerRight
  else grid.upperRight

/-- The fixed-order selected child has nonzero raw winding, including the last-child fallback by exact additivity.

The original scan chooses the first nonzero raw winding in its retained
child order. If the first three readings are zero, exact four-child
additivity and the parent state's nonzero winding certify the last child. -/
public theorem firstNonzeroChild_rawWinding_ne
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {state : State.Raw.RawWindingState p ambient} (grid : Subdivision.Raw.Grid.RawFourGrid state) :
    Winding.Box.Basic.quadrupledBoxWinding p (firstNonzeroChild grid).box ≠ 0 := by
  by_cases lowerLeftNonzero :
      Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box ≠ 0
  · rw [firstNonzeroChild, if_pos lowerLeftNonzero]
    exact lowerLeftNonzero
  by_cases upperLeftNonzero :
      Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box ≠ 0
  · rw [firstNonzeroChild, if_neg lowerLeftNonzero, if_pos upperLeftNonzero]
    exact upperLeftNonzero
  by_cases lowerRightNonzero :
      Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box ≠ 0
  · rw [firstNonzeroChild, if_neg lowerLeftNonzero, if_neg upperLeftNonzero,
      if_pos lowerRightNonzero]
    exact lowerRightNonzero
  have upperRightNonzero :
      Winding.Box.Basic.quadrupledBoxWinding p grid.upperRight.box ≠ 0 := by
    have lowerLeftZero :
        Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box = 0 := by
      by_cases equal : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box = 0
      · exact equal
      · exact (lowerLeftNonzero equal).elim
    have upperLeftZero :
        Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box = 0 := by
      by_cases equal : Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box = 0
      · exact equal
      · exact (upperLeftNonzero equal).elim
    have lowerRightZero :
        Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box = 0 := by
      by_cases equal : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box = 0
      · exact equal
      · exact (lowerRightNonzero equal).elim
    intro upperRightZero
    apply state.rawWinding_ne
    rw [grid.additive]
    rw [lowerLeftZero, upperLeftZero, lowerRightZero, upperRightZero]
    ring1
  rw [firstNonzeroChild, if_neg lowerLeftNonzero, if_neg upperLeftNonzero,
    if_neg lowerRightNonzero]
  exact upperRightNonzero

end Purelib.RootIsolation.Subdivision.Raw.Selection
