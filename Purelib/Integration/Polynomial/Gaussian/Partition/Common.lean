module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Partition.Unit.Common
public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells
import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Integration.Partition

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- Retained common refinements between two compilations of the exact same original source path.

Each original source segment keeps both input partitions and their common-refinement witness; the ordered tails retain
both compilations. -/
inductive Common.CommonCells : {source : Source.PolynomialPath} → Cells.CompiledCells source → Cells.CompiledCells
  source → Type
  /-- The common refinement of the exact two empty compilations. -/ | nil :
    Purelib.Integration.Polynomial.Gaussian.Partition.Common.CommonCells .nil .nil
  /-- Retain both original head partitions' common refinement and the exact compiled-tail comparison. -/ | cons {source
    : PolynomialSegment} {rest : Source.PolynomialPath}
      {left right : Segment.CompiledSegment source} {leftTail rightTail : Cells.CompiledCells rest}
      (head : Unit.Common.CommonRefinement left.partition right.partition)
      (tail : Purelib.Integration.Polynomial.Gaussian.Partition.Common.CommonCells leftTail rightTail) :
        Purelib.Integration.Polynomial.Gaussian.Partition.Common.CommonCells (.cons left leftTail) (.cons right
        rightTail)

constructive_injectivity Common.CommonCells

/-- Construct common refinements for the exact original compiled segment pairs in source order.

Both input owners and their retained partitions remain in the comparison. The construction keeps the ordered
common-refinement witnesses. -/
@[expose] def Cells.CompiledCells.common : {source : Source.PolynomialPath} →
    (left right : Cells.CompiledCells source) → Common.CommonCells left right
  | [], .nil, .nil => .nil
  | _ :: _, .cons left leftTail, .cons right rightTail =>
      .cons (left.common right) (leftTail.common rightTail)

end Purelib.Integration.Polynomial.Gaussian.Partition
end
