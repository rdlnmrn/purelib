module

import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.SafePath
import Purelib.Curves.Legendre.Paths

/-! # Exact original axis ownership in retained ordered path refinements -/

namespace TestPurelib.Curves.Legendre.Paths.Path.Refinement

open Purelib.Curves.Legendre.Paths

/-- The original empty path retains its actual axis cut and original frame parameter. -/
example {start finish source : Gaussian} (axis : AxisSegment start finish) (frame : Frame source)
    (parameter : Coordinate) (same : axis.pointAt parameter = source) :
    (Path.nil frame).RefinesAxis axis parameter parameter := Path.RefinesAxis.nil axis frame parameter same

/-- An empty refinement cannot silently skip an original nonempty parameter interval. -/
example {start finish source : Gaussian} (axis : AxisSegment start finish) (frame : Frame source)
    {lower upper : Coordinate} (different : lower ≠ upper) :
    ¬ (Path.nil frame).RefinesAxis axis lower upper := fun refinement =>
  different (Path.RefinesAxis.nil_data axis refinement).1

/-- Every actual refinement has ordered outer cuts, independently of its extracted braid word. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} (path : Path left right) :
    ¬ path.RefinesAxis axis 1 0 := fun refinement =>
  (by decide : ¬ (1 : Coordinate) ≤ 0) (refinement.lower_le_upper axis)

/-- The actual source and target path indices are the original parent-axis readings at the retained cuts. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) :
    axis.pointAt lower = source ∧ axis.pointAt upper = target := refinement.endpoints axis

/-- Every original point between the retained cuts has an actual unit-segment or final-frame membership witness. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) (parameter : Coordinate)
    (inside : lower ≤ parameter ∧ parameter ≤ upper) : path.Visits (axis.pointAt parameter) :=
  refinement.visits axis parameter inside

/-- A retained single segment gives physical refinement from its actual all-parameter affine geometry. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} (head : Segment left right) {lower upper : Coordinate}
    (ordered : lower ≤ upper) (geometry : ∀ parameter : Coordinate,
      head.geometry.pointAt parameter = axis.pointAt (lower + parameter * (upper - lower))) :
    (Path.cons head (Path.nil right)).RefinesAxis axis lower upper :=
  Path.RefinesAxis.single axis head ordered geometry

/-- Reversal retains each actual original path-point witness even when it lies on an endpoint or stationary piece. -/
example {source target : Gaussian} {left : Frame source} {right : Frame target}
    {path : Path left right} {point : Gaussian} (visited : path.Visits point) : path.reverse.Visits point :=
  visited.reverse

/-- Appending two actual refinements keeps the same original axis and shared intermediate frame and cut. -/
example {start finish source middle target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {center : Frame middle} {right : Frame target}
    {initial : Path left center} {remaining : Path center right} {lower next upper : Coordinate}
    (first : initial.RefinesAxis axis lower next) (last : remaining.RefinesAxis axis next upper) :
    (initial.append remaining).RefinesAxis axis lower upper := first.append axis last

/-- Exact endpoint-frame transports retain the complete original physical refinement. -/
example {start finish source target first last : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) (sourceEq : source = first) (targetEq : target = last) :
    (path.castParameters sourceEq targetEq).RefinesAxis axis lower upper :=
  refinement.castParameters axis sourceEq targetEq

/-- A local original-axis restriction refines its same original parent through the exact affine cut map. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {first last lower upper : Coordinate}
    (ordered : first ≤ last) (refinement : path.RefinesAxis (axis.restrict first last) lower upper) :
    path.RefinesAxis axis (first + lower * (last - first)) (first + upper * (last - first)) :=
  refinement.restrict axis ordered

/-- Exact outer-cut readbacks transport the same physical relation without changing any original path data. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper first last : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) (firstEq : lower = first) (lastEq : upper = last) :
    path.RefinesAxis axis first last := refinement.castCuts axis firstEq lastEq

/-- A complete local restriction refinement covers its same original parent interval without altering the path. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {first last : Coordinate}
    (ordered : first ≤ last) (refinement : path.RefinesAxis (axis.restrict first last) 0 1) :
    path.RefinesAxis axis first last := refinement.restrict_unit axis ordered

/-- An actual original-head refinement composes with the same original safe-tail refinement at its retained frame. -/
example {start middle finish : Gaussian} (segment : AxisSegment start middle) (safe : AxisSegment.Safe segment)
    {tail : SafePath middle finish} {left : Frame start} {center : Frame middle} {right : Frame finish}
    {initial : Path left center} {remaining : Path center right}
    (first : initial.RefinesAxis segment 0 1) (last : remaining.RefinesSafePath tail) :
    (initial.append remaining).RefinesSafePath (SafePath.cons segment safe tail) :=
  Path.RefinesSafePath.cons segment safe first last

/-- Reversal reflects every original cut and physically traverses the reversed original axis. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) :
    path.reverse.RefinesAxis axis.reverse (1 - upper) (1 - lower) := refinement.reverse axis

/-- Reversed endpoint readings retain the actual original frames in the opposite physical orientation. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right} {lower upper : Coordinate}
    (refinement : path.RefinesAxis axis lower upper) :
    axis.reverse.pointAt (1 - upper) = target ∧ axis.reverse.pointAt (1 - lower) = source :=
  (refinement.reverse axis).endpoints axis.reverse

/-- A complete original interval is retained on the actual original reversed path, including stationary pieces. -/
example {start finish source target : Gaussian} (axis : AxisSegment start finish)
    {left : Frame source} {right : Frame target} {path : Path left right}
    (refinement : path.RefinesAxis axis 0 1) : path.reverse.RefinesAxis axis.reverse 0 1 :=
  refinement.reverse_unit axis

/-- Physical whole-path reversal preserves its same original safe-path parent independently of word extraction. -/
example {start finish : Gaussian} {original : SafePath start finish} {left : Frame start} {right : Frame finish}
    {prepared : Path left right} (refinement : prepared.RefinesSafePath original) :
    prepared.reverse.RefinesSafePath original.reverse := refinement.reverse

/-- Whole-path physical correspondence transfers actual original-axis membership to the actual prepared path. -/
example {start finish : Gaussian} {original : SafePath start finish} {left : Frame start} {right : Frame finish}
    {prepared : Path left right} (refinement : prepared.RefinesSafePath original) {point : Gaussian}
    (visited : original.Visits point) : prepared.Visits point := refinement.visits visited

/-- Prepared concatenation retains both complete original geometric parents and their shared actual middle frame. -/
example {start middle finish : Gaussian} {firstOriginal : SafePath start middle}
    {lastOriginal : SafePath middle finish} {left : Frame start} {center : Frame middle} {right : Frame finish}
    {initial : Path left center} {remaining : Path center right}
    (first : initial.RefinesSafePath firstOriginal) (last : remaining.RefinesSafePath lastOriginal) :
    (initial.append remaining).RefinesSafePath (firstOriginal.append lastOriginal) := first.append last

end TestPurelib.Curves.Legendre.Paths.Path.Refinement
