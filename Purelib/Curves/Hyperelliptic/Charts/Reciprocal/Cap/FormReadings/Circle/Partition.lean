module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Observation
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Bounds
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Data.List.Append
import Purelib.Tactic.Ring

/-! # Same-cache dyadic partitions of the actual cap-form circle model

The original dependent-product split retains both complete numerical
reading banks. Typed transports use the original list append readbacks;
the actual cell lists preserve their original order and observed values.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}
  {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}

/-- The original shared left embedding reads the same actual dyadic edge in a literal concatenation. -/
private theorem left_edge (first last : List ParameterEdge) (index : Fin first.length) :
    (first ++ last)[(DependentProduct.leftIndex first last index).val]'
        (DependentProduct.leftIndex first last index).isLt = first[index.val]'index.isLt := by
  have position := DependentProduct.leftIndex_val first last index
  have bound := position ▸ (DependentProduct.leftIndex first last index).isLt
  exact (getElem_congr rfl position (DependentProduct.leftIndex first last index).isLt).trans
    (Append.getElem_append_left first last index.val index.isLt bound)

/-- The original shared right embedding reads the same actual dyadic edge after its retained left prefix. -/
private theorem right_edge (first last : List ParameterEdge) (index : Fin last.length) :
    (first ++ last)[(DependentProduct.rightIndex first last index).val]'
        (DependentProduct.rightIndex first last index).isLt = last[index.val]'index.isLt := by
  have position := DependentProduct.rightIndex_val first last index
  have bound := position ▸ (DependentProduct.rightIndex first last index).isLt
  exact (getElem_congr rfl position (DependentProduct.rightIndex first last index).isLt).trans
    (Append.getElem_append_right first last index.val index.isLt bound)

/-- Split the supplied whole reading bank into its two original dyadic halves without observing or preparing again.

The original dependent product preserves its actual bounded occurrences
and literal right tail. Exact original list readbacks transport those same
complete entries to their original half-interval indices.
-/
def split (stored : Readings differential cap base unitBound collarBound actual (depth + 1) left right target) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    Readings differential cap base unitBound collarBound actual depth left middle target ×
      Readings differential cap base unitBound collarBound actual depth middle right target :=
  let middle : Endpoint :=
    ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
  let first := dyadicEdges depth left middle
  let last := dyadicEdges depth middle right
  let kind := fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target
  let retained := DependentProduct.split first last stored
  ⟨DependentProduct.transport first (fun index => congrArg kind (left_edge first last index)) retained.1,
    DependentProduct.transport last (fun index => congrArg kind (right_edge first last index)) retained.2⟩

/-- The typed first half retains the same whole supplied original reading at its actual left embedding. -/
theorem get_split_left
    (stored : Readings differential cap base unitBound collarBound actual (depth + 1) left right target)
    (index : Fin (dyadicEdges depth left
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩).length) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    HEq ((split stored).1.get index)
      (stored.get (DependentProduct.leftIndex (dyadicEdges depth left middle)
        (dyadicEdges depth middle right) index)) := by
  dsimp only
  rewrite [get_eq, get_eq]
  unfold split
  dsimp only
  exact (DependentProduct.get_transport _ _ _ _).trans
    (heq_of_eq (DependentProduct.get_split_left _ _ stored index))

/-- The typed second half retains the same complete supplied original reading from its literal right suffix. -/
theorem get_split_right
    (stored : Readings differential cap base unitBound collarBound actual (depth + 1) left right target)
    (index : Fin (dyadicEdges depth
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩ right).length) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    HEq ((split stored).2.get index)
      (stored.get (DependentProduct.rightIndex (dyadicEdges depth left middle)
        (dyadicEdges depth middle right) index)) := by
  dsimp only
  rewrite [get_eq, get_eq]
  unfold split
  dsimp only
  exact (DependentProduct.get_transport _ _ _ _).trans
    (heq_of_eq (DependentProduct.get_split_right _ _ stored index))

/-- Transporting the actual whole reading along an edge identity preserves its complete original circle cell. -/
private theorem readingCell_cast (first last : ParameterEdge) (same : first = last)
    (reading : Reading differential cap (actual.val.point first.left.parameter)
      (point_inside base unitBound collarBound actual first.left.parameter) target)
    (reference : Option (Canonical → Canonical))
    (allowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    readingCell differential cap base unitBound collarBound actual target last
      (cast (congrArg (fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
        (point_inside base unitBound collarBound actual edge.left.parameter) target) same) reading)
        reference allowance =
      readingCell differential cap base unitBound collarBound actual target first reading
        reference allowance := by
  cases same
  rfl

/-- The same complete original cell list is the concatenation of its actual split banks in original order.

Both total and reference-difference cells use the same original reading
mapper. The whole-entry split and exact typed transport preserve every
actual coefficient, observation and original endpoint record.
-/
theorem split_cells
    (stored : Readings differential cap base unitBound collarBound actual (depth + 1) left right target)
    (reference : Option (Canonical → Canonical))
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none) :
    stored.cells reference allowance =
      (split stored).1.cells reference allowance ++ (split stored).2.cells reference allowance := by
  rewrite [cells_eq, cells_eq, cells_eq]
  unfold split
  dsimp only
  let middle : Endpoint :=
    ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
  let first := dyadicEdges depth left middle
  let last := dyadicEdges depth middle right
  change (DependentProduct.mapToList (first ++ last)
    (family := fun index => Reading differential cap
      (actual.val.point ((first ++ last)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual ((first ++ last)[index.val]'index.isLt).left.parameter) target)
    stored fun index reading =>
    readingCell differential cap base unitBound collarBound actual target
      ((first ++ last)[index.val]'index.isLt) reading reference allowance) = _
  rewrite [DependentProduct.mapToList_transport, DependentProduct.mapToList_transport,
    DependentProduct.mapToList_split]
  apply congrArg₂ (fun first last => first ++ last)
  · apply DependentProduct.mapToList_congr
    intro index entry
    exact (readingCell_cast _ _ (left_edge _ _ index) entry reference allowance).symm
  · apply DependentProduct.mapToList_congr
    intro index entry
    exact (readingCell_cast _ _ (right_edge _ _ index) entry reference allowance).symm

/-- The same original edge producer transports its complete actual reading along an exact edge identity. -/
private theorem readEdge_heq (nonzero : base ≠ 0) (positive : 0 < target)
    (first last : ParameterEdge) (same : first = last) :
    HEq (readEdge differential cap base nonzero unitBound collarBound actual target positive first)
      (readEdge differential cap base nonzero unitBound collarBound actual target positive last) := by
  cases same
  rfl

/-- Splitting a canonical bank returns both complete canonical half banks without changing any retained entry.

Whole-entry lookup and the original edge producer identify each stored
cache at its actual original bounded embedding. Finite product equality
then retains both actual half banks; no scalar-only cache identification
or new numerical observation is used.
-/
theorem split_readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (depth : Nat) (left right : Endpoint)
    (target : Fraction.Rational) (positive : 0 < target) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    split (readings differential cap base nonzero unitBound collarBound actual
      (depth + 1) left right target positive) =
      (readings differential cap base nonzero unitBound collarBound actual depth left middle target positive,
        readings differential cap base nonzero unitBound collarBound actual depth middle right target positive) := by
  let middle : Endpoint :=
    ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
  let first := dyadicEdges depth left middle
  let last := dyadicEdges depth middle right
  let parent := readings differential cap base nonzero unitBound collarBound actual
    (depth + 1) left right target positive
  apply Prod.ext
  · apply eq_of_get
    intro index
    have original := get_split_left parent index
    dsimp only [parent] at original
    rewrite [get_readEdge] at original
    have selected := readEdge_heq (differential := differential) (cap := cap)
      (unitBound := unitBound) (collarBound := collarBound) (actual := actual) nonzero positive _ _
      (left_edge first last index)
    have expected := get_readEdge differential cap base nonzero unitBound collarBound actual
      depth left middle target positive index
    exact eq_of_heq ((original.trans selected).trans (heq_of_eq expected.symm))
  · apply eq_of_get
    intro index
    have original := get_split_right parent index
    dsimp only [parent] at original
    rewrite [get_readEdge] at original
    have selected := readEdge_heq (differential := differential) (cap := cap)
      (unitBound := unitBound) (collarBound := collarBound) (actual := actual) nonzero positive _ _
      (right_edge first last index)
    have expected := get_readEdge differential cap base nonzero unitBound collarBound actual
      depth middle right target positive index
    exact eq_of_heq ((original.trans selected).trans (heq_of_eq expected.symm))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

end
