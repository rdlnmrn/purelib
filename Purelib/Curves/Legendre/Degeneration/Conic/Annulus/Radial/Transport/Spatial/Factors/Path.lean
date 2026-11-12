module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
public import Purelib.Polynomial.Geometry.ClearPath

/-! # Retained factor preparations on original spatial paths

The original finite ClearPath spine determines every physical edge and its
ambient-containment proof. One original factor preparation cache is stored
per edge. Recursion consumes the same retained tail, never a reconstructed
list of spatial endpoints or a replacement path.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}

/-- One completed physical-edge factor cache retains its whole original construction identity. -/
@[irreducible, expose] def SegmentCache (budgets : Budgets anchor) {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) (completed : Segment budgets segment within) : Prop :=
  completed = Segment.build budgets segment within

/-- The original clear-path spine indexes the identical factor cache retained at each physical edge.

The existing product and subtype retain the whole completed Segment cache
and its factory equation. Only the original ClearPath is matched; the source
reading, anchor, budgets and actual ambient witnesses remain input indices.
-/
@[expose] def Path (budgets : Budgets anchor) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor) start finish) →
    path.WithinAmbient → Type
  | _, _, .nil _, _ => PUnit
  | _, _, .cons head tail, within =>
      { completed : Segment budgets head within.head // SegmentCache budgets head within.head completed } ×
        Path budgets tail within.tail

namespace Path

variable {budgets : Budgets anchor}

/-- The original empty spatial path needs no physical-edge factor preparation. -/
@[expose] def nil (point : Canonical)
    (within : (ClearPath.nil (polynomial := Paths.polynomial parameter)
      (ambient := sourceBox anchor) point).WithinAmbient) :
    Path budgets (.nil point) within := PUnit.unit

/-- Prepend a completed original edge cache to its identical retained tail without repeating either factory. -/
@[expose] def cons {start middle finish : Canonical}
    (head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start middle)
    (tail : ClearPath (Paths.polynomial parameter) (sourceBox anchor) middle finish)
    (within : (ClearPath.cons head tail).WithinAmbient)
    (completed : Segment budgets head within.head)
    (completed_eq : SegmentCache budgets head within.head completed)
    (following : Path budgets tail within.tail) : Path budgets (.cons head tail) within :=
  ⟨⟨completed, completed_eq⟩, following⟩

/-- Cache both actual factor preparations once per original physical edge of the supplied retained path. -/
def build (budgets : Budgets anchor) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) (sourceBox anchor) start finish) →
    (within : path.WithinAmbient) → Path budgets path within
  | _, _, .nil point, within => nil point within
  | _, _, .cons head tail, within =>
      let completed := Segment.build budgets head within.head
      let following := build budgets tail within.tail
      cons head tail within completed (by unfold SegmentCache; rfl) following

variable {start middle finish : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start middle}
variable {tail : ClearPath (Paths.polynomial parameter) (sourceBox anchor) middle finish}
variable {within : (ClearPath.cons head tail).WithinAmbient}

/-- Read the whole unchanged original factor preparation cache at the first physical edge. -/
@[expose] def headCache (completed : Path budgets (.cons head tail) within) :
    Segment budgets head within.head := completed.1.val

/-- Read the exact original tail's factor caches without re-enumerating or rebuilding its spatial edges. -/
@[expose] def tailCaches (completed : Path budgets (.cons head tail) within) :
    Path budgets tail within.tail := completed.2

/-- The first cache retains the complete original factor preparation factory for that identical physical edge. -/
theorem headCache_eq (completed : Path budgets (.cons head tail) within) :
    completed.headCache = Segment.build budgets head within.head := by
  have retained := completed.1.property
  unfold SegmentCache at retained
  exact retained

/-- Prepending completed caches returns the same entire first physical-edge cache. -/
theorem cons_headCache (completed : Segment budgets head within.head)
    (completed_eq : SegmentCache budgets head within.head completed)
    (following : Path budgets tail within.tail) :
    (cons head tail within completed completed_eq following).headCache = completed := rfl

/-- Prepending completed caches returns the identical supplied original tail cache. -/
theorem cons_tailCaches (completed : Segment budgets head within.head)
    (completed_eq : SegmentCache budgets head within.head completed)
    (following : Path budgets tail within.tail) :
    (cons head tail within completed completed_eq following).tailCaches = following := rfl

end Path

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
