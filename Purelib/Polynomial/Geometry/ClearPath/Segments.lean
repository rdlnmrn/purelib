module

public import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Data.List.DependentProduct
public import Purelib.Topology.Chain.PathBoundary

/-! # Clear paths from retained edge-segment caches

The original edge list supplies every occurrence. Its stored segment
product is traversed without invoking an entry producer. Endpoint
incidence supplies only exact index transports, including the empty word.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rational (Box)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

namespace ClearSegment

/-- Two original unit-interval points retain the axis of their same certified segment. -/
theorem pointAt_axis {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment polynomial ambient start finish) (first last : Purelib.Data.Rat.Fraction.Rational)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    (segment.pointAt first).im = (segment.pointAt last).im ∨
      (segment.pointAt first).re = (segment.pointAt last).re := by
  have firstOn := segment.pointAt_onCertifiedLine first firstInside
  have lastOn := segment.pointAt_onCertifiedLine last lastInside
  cases segment with
  | horizontal => exact Or.inl (firstOn.1.trans lastOn.1.symm)
  | vertical => exact Or.inr (firstOn.1.trans lastOn.1.symm)

end ClearSegment

variable {Vertex Edge : Type} {polynomial : GaussianPolynomial} {ambient : Box}
    (coordinate : Vertex → Canonical) (first last : Edge → Vertex)

/-- One actual contained clear segment at each original bounded edge occurrence. -/
abbrev Segments (edges : List Edge) :=
  DependentProduct edges (fun index =>
    {segment : ClearSegment polynomial ambient
        (coordinate (first (edges[index.val]'index.isLt)))
        (coordinate (last (edges[index.val]'index.isLt))) // segment.WithinAmbient})

/-- Concatenate the same stored segments according to the original exact endpoint chain.

Recursion follows the actual edge list and literal retained product tail.
The endpoint proposition is used only for equality transport of indices;
no computational witness is extracted from it.
-/
@[expose] def ofSegments : (edges : List Edge) →
    Segments (polynomial := polynomial) (ambient := ambient) coordinate first last edges →
    {start finish : Vertex} → PathEndpoints first last edges start finish →
    {path : ClearPath polynomial ambient (coordinate start) (coordinate finish) // path.WithinAmbient}
  | [], _, start, _, ends =>
      Eq.mp (congrArg (fun finish =>
        {path : ClearPath polynomial ambient (coordinate start) (coordinate finish) // path.WithinAmbient})
        ends.nil_eq) ⟨.nil (coordinate start), .nil (coordinate start)⟩
  | _head :: tail, segments, _, finish, ends =>
      let following := ofSegments tail segments.2 ends.cons_tail
      Eq.mpr (congrArg (fun start =>
        {path : ClearPath polynomial ambient (coordinate start) (coordinate finish) // path.WithinAmbient})
        ends.cons_start)
        ⟨.cons segments.1.val following.val, .cons segments.1.property following.property⟩

/-- The concatenation keeps exactly one geometric segment per original edge occurrence. -/
theorem ofSegments_count : (edges : List Edge) →
    (segments : Segments (polynomial := polynomial) (ambient := ambient) coordinate first last edges) →
    {start finish : Vertex} → (ends : PathEndpoints first last edges start finish) →
    (ofSegments (polynomial := polynomial) (ambient := ambient)
      coordinate first last edges segments ends).val.segmentCount = edges.length
  | [], _, _, _, ends => by
      have equal := ends.nil_eq
      cases equal
      rfl
  | _head :: tail, segments, _, _, ends => by
      have equal := ends.cons_start
      cases equal
      change (ofSegments (polynomial := polynomial) (ambient := ambient)
        coordinate first last tail segments.2 ends.cons_tail).val.segmentCount + 1 = tail.length + 1
      exact congrArg Nat.succ (ofSegments_count tail segments.2 ends.cons_tail)

/-- A nonempty concatenation uses the same stored head and original tail before its exact initial-index transport. -/
theorem ofSegments_cons (head : Edge) (tail : List Edge)
    (segments : Segments (polynomial := polynomial) (ambient := ambient) coordinate first last (head :: tail))
    {start finish : Vertex}
    (ends : PathEndpoints first last (head :: tail) start finish) :
    (ofSegments (polynomial := polynomial) (ambient := ambient)
      coordinate first last (head :: tail) segments ends).val =
      ClearPath.castStart (congrArg coordinate ends.cons_start).symm
        (.cons segments.1.val (ofSegments (polynomial := polynomial) (ambient := ambient)
          coordinate first last tail segments.2 ends.cons_tail).val) := by
  have equal := ends.cons_start
  cases equal
  rfl

/-- An empty word transports the same empty geometric path and does not construct a stationary segment. -/
theorem ofSegments_nil
    (segments : Segments (polynomial := polynomial) (ambient := ambient) coordinate first last ([] : List Edge))
    {start finish : Vertex}
    (ends : PathEndpoints first last [] start finish) :
    (ofSegments (polynomial := polynomial) (ambient := ambient) coordinate first last [] segments ends).val =
      ClearPath.castFinish (congrArg coordinate ends.nil_eq) (.nil (coordinate start)) := by
  have equal := ends.nil_eq
  cases equal
  rfl

end Purelib.Polynomial.Geometry.ClearPath

end
