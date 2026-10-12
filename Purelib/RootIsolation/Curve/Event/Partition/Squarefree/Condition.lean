module
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Guard
public import Purelib.RootIsolation.Curve.Event.Partition.Condition
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
public import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
import Purelib.RootIsolation.Sturm.Event.Resolution
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Width
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Polynomial.Dense.Basic (RationalPolynomial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.RootIsolation.Curve.Event.Partition.Squarefree

/-! ## Exhaustive squarefree leaves -/

/-- Resolve one original active box condition on a retained squarefree-subdivision leaf.

The leaf width is bounded by the common squarefree budget and hence by the original condition's resolution budget. -/
def squarefreeConditionEvent
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Data.Rat.Interval.Proper.Cell)
    (leafMember : leaf ∈
      (Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves)
    (polynomial : RationalPolynomial)
    (member : polynomial ∈
      Curve.Box.activeConditionPolynomials curve box) :
    Curve.Event.Partition.ConditionEvent event eventNonzero curve box root leaf where
  polynomial := polynomial
  member := member
  resolution :=
    Sturm.Event.polynomialEventResolutionOfBounds polynomial root leaf
      (Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_refines event eventNonzero squarefree
        curve box root leaf leafMember)
      ((Curve.Event.Partition.Squarefree.squarefreeSubdivision_leaf_width_lt event eventNonzero squarefree
        curve box root leaf leafMember).trans_le
          ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common event squarefree curve box root).trans
            (Purelib.RootIsolation.Curve.Event.Partition.commonLeafWidth_le_condition event root member)))

/-- Resolve the original attached list of active box conditions on one retained squarefree leaf.

Each output retains its actual condition and the same leaf's checked width and refinement evidence. -/
def squarefreeConditionEvents
    (event : RationalPolynomial) (eventNonzero : event.isZero = false)
    (squarefree : Dense.Rational.Squarefree.BoundaryPartition.SquarefreeCertificate event)
    (curve : Curve.RationalCurve) (box : Box) (root leaf : Data.Rat.Interval.Proper.Cell)
    (leafMember : leaf ∈
      (Curve.Event.Partition.Squarefree.squarefreeSubdivision event eventNonzero squarefree
        curve box root).leaves) :
    List (Curve.Event.Partition.ConditionEvent event eventNonzero curve box root leaf) :=
  (Curve.Box.activeConditionPolynomials curve box).attach.map
    fun entry => squarefreeConditionEvent event eventNonzero squarefree
      curve box root leaf leafMember entry.1 entry.2
end Purelib.RootIsolation.Curve.Event.Partition.Squarefree

end
