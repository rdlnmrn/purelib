module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage

/-!
# Separation and point identification for retained grid cells

The finite pairwise list certificate relates any two distinct retained cells,
independently of their list order.  A point strictly inside one cell cannot
belong to another cell, even on the other's boundary.  These proofs do not
require decidable equality of the cached line-clearance functions.
-/

namespace Purelib.Polynomial.Geometry.Grid.CellSeparation

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Distinct members of a pairwise interior-separated cell list have separated interiors in either list order.

The two membership witnesses refer to the original cell list. Structural induction selects their pairwise certificate,
reversing the separation relation only when the second cell occurs first. -/
private theorem separated_of_mem {cells : List (Geometry.Grid.ClearGrid.Cell polynomial ambient)}
    (pairwise : cells.Pairwise (fun first second => first.box.InteriorSeparated second.box))
    {first second : Geometry.Grid.ClearGrid.Cell polynomial ambient} (firstMember : first ∈ cells) (secondMember :
      second ∈ cells)
    (different : first ≠ second) : first.box.InteriorSeparated second.box := by
  induction cells with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with firstEq | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · exact (different secondEq.symm).elim
        · exact (List.pairwise_cons.mp pairwise).1 second secondMember
      · rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · subst second
          exact Box.interiorSeparated_symm ((List.pairwise_cons.mp pairwise).1 first firstMember)
        · exact ih (List.pairwise_cons.mp pairwise).2 firstMember secondMember

/-- Any two distinct retained cells of a clear-line grid have separated interiors. -/
public theorem cells_interiorSeparated (grid : ClearGrid polynomial ambient) {first second :
  Geometry.Grid.ClearGrid.Cell polynomial ambient}
    (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells) (different : first ≠ second) :
    first.box.InteriorSeparated second.box := separated_of_mem
      (ClearGridCoverage.cells_pairwise grid) firstMember secondMember different

/-- A point strictly inside one of two interior-separated boxes cannot belong even weakly to the other box. -/
private theorem no_common_point {left right : Box} (separated : left.InteriorSeparated right)
    {point : Gaussian.Basic.Canonical} (insideLeft : left.StrictContains point) (insideRight : right.Contains point) :
      False := by
  rcases separated with before | after | below | above
  · exact (lt_irrefl _) (insideLeft.2.1.trans_le (before.trans insideRight.1))
  · exact (lt_irrefl _) ((insideRight.2.1.trans after).trans_lt insideLeft.1)
  · exact (lt_irrefl _) (insideLeft.2.2.2.trans_le (below.trans insideRight.2.2.1))
  · exact (lt_irrefl _) ((insideRight.2.2.2.trans above).trans_lt insideLeft.2.2.1)

/-- Two members of a pairwise separated cell list coincide if one contains a common point strictly and the other
contains it weakly.

The retained membership witnesses either identify the same head cell or expose a pairwise-separated pair. Strict
containment excludes the latter case without deciding equality of the cached payloads. -/
private theorem equal_of_common_point {cells : List (Geometry.Grid.ClearGrid.Cell polynomial ambient)}
    (pairwise : cells.Pairwise (fun first second => first.box.InteriorSeparated second.box))
    {first second : Geometry.Grid.ClearGrid.Cell polynomial ambient} (firstMember : first ∈ cells) (secondMember :
      second ∈ cells)
    {point : Gaussian.Basic.Canonical} (insideFirst : first.box.StrictContains point) (insideSecond :
      second.box.Contains point) :
    first = second := by
  induction cells with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with firstEq | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · exact secondEq.symm
        · exact (no_common_point ((List.pairwise_cons.mp pairwise).1 second secondMember)
            insideFirst insideSecond).elim
      · rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · subst second
          exact (no_common_point (Box.interiorSeparated_symm
            ((List.pairwise_cons.mp pairwise).1 first firstMember)) insideFirst insideSecond).elim
        · exact ih (List.pairwise_cons.mp pairwise).2 firstMember secondMember

/-- Identify cells by one strict interior point, without comparing the
proof-bearing cached line payloads. -/
public theorem cells_eq_of_common_point (grid : ClearGrid polynomial ambient) {first second :
  Geometry.Grid.ClearGrid.Cell polynomial ambient}
    (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells) {point : Gaussian.Basic.Canonical}
    (insideFirst : first.box.StrictContains point) (insideSecond : second.box.Contains point) : first = second :=
  equal_of_common_point (ClearGridCoverage.cells_pairwise grid)
    firstMember secondMember insideFirst insideSecond

end Purelib.Polynomial.Geometry.Grid.CellSeparation
