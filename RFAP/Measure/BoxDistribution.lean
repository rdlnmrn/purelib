import RFAP.Measure.BoxContent
import FiniteMeasure.Normalization
import FiniteMeasure.LawCoupling

/-!
# Normalized finite distributions on RFAP box partitions

A displayed positive-area box partition can be normalized to an exact
rational distribution over its finitely many child boxes.  This is a law on
the partition cells themselves, not a completed uniform point measure.
-/

namespace RFAP.FiniteMeasure

/-- One displayed box carrying its exact rational area as weight. -/
def boxContentAtom (box : Box) :
    _root_.FiniteMeasure.Weighted Box where
  item := box
  weight := boxContent box
  nonnegative := boxContent_nonneg box

/-- Exact finite content carried by a displayed box list. -/
def boxPartitionContent (boxes : List Box) :
    _root_.FiniteMeasure.FiniteContent Box where
  atoms := boxes.map boxContentAtom

theorem boxPartitionContent_total (boxes : List Box) :
    (boxPartitionContent boxes).total =
      (boxes.map boxContent).sum := by
  induction boxes with
  | nil => rfl
  | cons box remaining inductionHypothesis =>
      simp only [boxPartitionContent,
        _root_.FiniteMeasure.FiniteContent.total,
        _root_.FiniteMeasure.totalWeight, List.map_cons,
        boxContentAtom, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]

/-- Normalize one explicitly positive finite box partition. -/
def boxPartitionDistribution (boxes : List Box)
    (positive : 0 < (boxPartitionContent boxes).total) :
    _root_.FiniteMeasure.Distribution Box :=
  (boxPartitionContent boxes).normalize positive

theorem boxPartitionDistribution_atoms_length (boxes : List Box)
    (positive : 0 < (boxPartitionContent boxes).total) :
    (boxPartitionDistribution boxes positive).atoms.length = boxes.length := by
  rw [boxPartitionDistribution,
    _root_.FiniteMeasure.FiniteContent.normalize_atoms_length]
  simp only [boxPartitionContent, List.length_map]

theorem boxPartitionDistribution_probability (boxes : List Box)
    (positive : 0 < (boxPartitionContent boxes).total)
    (event : Box → Bool) :
    (boxPartitionDistribution boxes positive).probability event =
      (boxPartitionContent boxes).measure event /
        (boxes.map boxContent).sum := by
  rw [boxPartitionDistribution,
    _root_.FiniteMeasure.FiniteContent.normalize_probability,
    boxPartitionContent_total]

/-- Two-child normalized area law from one displayed vertical cut. -/
def verticalSplitDistribution (box : Box) (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < boxContent box) :
    _root_.FiniteMeasure.Distribution Box :=
  boxPartitionDistribution
    [box.verticalLeft cut inside, box.verticalRight cut inside] (by
      rw [boxPartitionContent_total]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [vertical_content_add]
      exact positive)

/-- Two-child normalized area law from one displayed horizontal cut. -/
def horizontalSplitDistribution (box : Box) (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < boxContent box) :
    _root_.FiniteMeasure.Distribution Box :=
  boxPartitionDistribution
    [box.horizontalLower cut inside, box.horizontalUpper cut inside] (by
      rw [boxPartitionContent_total]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [horizontal_content_add]
      exact positive)

theorem verticalSplitDistribution_atoms_length (box : Box)
    (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < boxContent box) :
    (verticalSplitDistribution box cut inside positive).atoms.length = 2 := by
  unfold verticalSplitDistribution
  rw [boxPartitionDistribution_atoms_length]
  rfl

theorem horizontalSplitDistribution_atoms_length (box : Box)
    (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < boxContent box) :
    (horizontalSplitDistribution box cut inside positive).atoms.length = 2 := by
  unfold horizontalSplitDistribution
  rw [boxPartitionDistribution_atoms_length]
  rfl

/-- Pair every vertical child cell with its named parent box. -/
def verticalSplitParentLawCoupling (box : Box) (cut : Coordinate)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper)
    (positive : 0 < boxContent box) :
    _root_.FiniteMeasure.LawCoupling
      (verticalSplitDistribution box cut inside positive)
      (_root_.FiniteMeasure.Distribution.pure box) :=
  _root_.FiniteMeasure.LawCoupling.collapse
    (verticalSplitDistribution box cut inside positive) box

/-- Pair every horizontal child cell with its named parent box. -/
def horizontalSplitParentLawCoupling (box : Box) (cut : Coordinate)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper)
    (positive : 0 < boxContent box) :
    _root_.FiniteMeasure.LawCoupling
      (horizontalSplitDistribution box cut inside positive)
      (_root_.FiniteMeasure.Distribution.pure box) :=
  _root_.FiniteMeasure.LawCoupling.collapse
    (horizontalSplitDistribution box cut inside positive) box

end RFAP.FiniteMeasure
