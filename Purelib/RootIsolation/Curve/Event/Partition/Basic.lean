module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RootIsolation.Curve.Event.Partition.Leaf
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic

section

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Curve.Event.Partition

set_option genInjectivity false in
/-- The finite common tree paired with the total simultaneous classifier for
every emitted leaf. -/
structure EventPartition
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Data.Rat.Interval.Proper.Cell) where
  /-- The actual retained simultaneous event-subdivision tree. -/ tree : Curve.Event.Partition.Subdivision event curve
    box
  /-- The retained tree equals the original common-subdivision construction. -/ tree_eq : tree =
    Curve.Event.Partition.commonSubdivision event eventNonzero curve box root
  /-- Classify each actual member of the retained leaf list. -/ classify : (leaf : Data.Rat.Interval.Proper.Cell) → leaf
    ∈ tree.leaves →
    Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root
  /-- Each classification retains its supplied original leaf exactly. -/ classify_cell : ∀ (leaf :
    Data.Rat.Interval.Proper.Cell) (member : leaf ∈ tree.leaves),
    (classify leaf member).cell = leaf

constructive_injectivity EventPartition

/-- Build the original common event subdivision with its total aligned leaf classifier.

Each classified record retains the exact leaf selected from that same subdivision tree. -/
def classifyEvents
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (root : Data.Rat.Interval.Proper.Cell) :
    Curve.Event.Partition.EventPartition event eventNonzero curve box root where
  tree := Curve.Event.Partition.commonSubdivision event eventNonzero curve box root
  tree_eq := rfl
  classify := fun leaf member =>
    Curve.Event.Partition.classifyLeaf event eventNonzero curve box root leaf member
  classify_cell := fun _leaf _member => rfl

set_option genInjectivity false in
/-- Constructive location of one displayed parameter in the classified
common leaf family. -/
structure LocatedParameter
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (partition : Curve.Event.Partition.EventPartition event eventNonzero curve box root)
    (parameter : Fraction.Rational) where
  /-- The original subdivision leaf selected for this parameter. -/ leaf : Data.Rat.Interval.Proper.Cell
  /-- The selected leaf belongs to the retained tree. -/ member : leaf ∈ partition.tree.leaves
  /-- The selected interval contains the original query parameter. -/ contains : leaf.interval.Contains parameter
  /-- The retained simultaneous classification of the selected leaf. -/ classification :
    Curve.Event.Partition.ClassifiedLeaf event eventNonzero curve box root
  /-- The retained classification equals the original partition classifier's result. -/ classification_eq :
    classification = partition.classify leaf member
  /-- The classified cell is the exact selected original leaf. -/ classification_cell : classification.cell = leaf

constructive_injectivity LocatedParameter

/-- Locate a displayed parameter in the retained common subdivision and return that exact leaf's classification. -/
def EventPartition.locate
    {event : Dense.Basic.RationalPolynomial} {eventNonzero : event.isZero = false}
    {curve : Curve.RationalCurve} {box : Box} {root : Data.Rat.Interval.Proper.Cell}
    (partition : Curve.Event.Partition.EventPartition event eventNonzero curve box root)
    (parameter : Fraction.Rational) (inside : root.interval.Contains parameter) :
    Curve.Event.Partition.LocatedParameter partition parameter := by
  let found := Curve.Event.Partition.Subdivision.locateBuild event eventNonzero curve box
    (Curve.Event.Partition.commonDepth event curve box root) root parameter inside
  have treeMember : found.leaf ∈ partition.tree.leaves := by
    rw [partition.tree_eq]
    exact found.member
  exact
    { leaf := found.leaf
      member := treeMember
      contains := found.contains
      classification := partition.classify found.leaf treeMember
      classification_eq := rfl
      classification_cell := partition.classify_cell found.leaf treeMember }

end Purelib.RootIsolation.Curve.Event.Partition

end

end
