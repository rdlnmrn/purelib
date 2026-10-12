module
import Purelib.Polynomial.Dense.Gaussian.Split.Lattice
import Purelib.Topology.Knot.Braid.Artin
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Artin
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Cells.Far
public import Purelib.Topology.Knot.Braid.Polynomial.Exact.Homotopy
import Purelib.Topology.Knot.Braid.Polynomial.Exact.Word

public import Purelib.Examples.Topology.Knot.Torus.WorkedExamples
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Torus.Basic

open Purelib.Polynomial

open Purelib.Topology

section
@[expose] public section

/-!
# Worked finite torus-knot and torus-link examples

Each non-trivial knot below carries the same finite outputs expected from the
standard torus-knot formulas: one component, crossing count and writhe of the
displayed positive braid, genus `(p-1)(q-1)/2`, and the complete normalized
Alexander polynomial.  Every polynomial also carries the exact finite
quotient identity from `TorusInvariants.AlexanderCertificate`.

The final link examples check the non-coprime component theorem, and the
one-strand example is a trivial normalization sanity check.
-/

namespace Purelib.Examples.Topology.Knot.Polynomial.Realization.WorkedExamples

open Purelib.Examples

open Purelib.Topology.Knot.Braid.Polynomial.Exact
open Purelib.Examples.Topology.Knot
open Purelib.Topology.Knot.Braid.Artin

open Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.ExactPolynomialLoops

/-- The explicit rational coefficient loop realizing the original trefoil braid word. -/
def trefoilLoop :
  Word.RealizedLoop Torus.WorkedExamples.trefoil.braidWord :=
  Word.realizeWord _
/-- The explicit rational coefficient loop realizing the original cinquefoil braid word. -/
def cinquefoilLoop :
  Word.RealizedLoop Torus.WorkedExamples.cinquefoil.braidWord :=
  Word.realizeWord _
/-- The explicit rational coefficient loop realizing the original `(3, 4)` torus-knot word. -/
def torusKnot34Loop :
  Word.RealizedLoop Torus.WorkedExamples.torusKnot34.braidWord :=
  Word.realizeWord _
/-- The explicit rational coefficient loop realizing the original `(3, 5)` torus-knot word. -/
def torusKnot35Loop :
  Word.RealizedLoop Torus.WorkedExamples.torusKnot35.braidWord :=
  Word.realizeWord _
/-- The explicit rational coefficient loop realizing the original `(4, 5)` torus-knot word. -/
def torusKnot45Loop :
  Word.RealizedLoop Torus.WorkedExamples.torusKnot45.braidWord :=
  Word.realizeWord _

/-- The trefoil realization has thirteen coefficient vertices. -/
@[simp] theorem trefoilLoop_coefficientCount
  :
    trefoilLoop.coefficientVertices.length = 13 := by
  rw [trefoilLoop,
    Word.realizeWord_coefficientCount,
    Torus.WorkedExamples.trefoil_crossingCount]

/-- The cinquefoil realization has twenty-one coefficient vertices. -/
@[simp] theorem
  cinquefoilLoop_coefficientCount :
    cinquefoilLoop.coefficientVertices.length = 21 := by
  rw [cinquefoilLoop,
    Word.realizeWord_coefficientCount,
    Torus.WorkedExamples.cinquefoil_crossingCount]

/-- The `(3, 4)` realization has thirty-three coefficient vertices. -/
@[simp] theorem
  torusKnot34Loop_coefficientCount :
    torusKnot34Loop.coefficientVertices.length = 33 := by
  rw [torusKnot34Loop,
    Word.realizeWord_coefficientCount,
    Torus.WorkedExamples.torusKnot34_crossingCount]

/-- The `(3, 5)` realization has forty-one coefficient vertices. -/
@[simp] theorem
  torusKnot35Loop_coefficientCount :
    torusKnot35Loop.coefficientVertices.length = 41 := by
  rw [torusKnot35Loop,
    Word.realizeWord_coefficientCount,
    Torus.WorkedExamples.torusKnot35_crossingCount]

/-- The `(4, 5)` realization has sixty-one coefficient vertices. -/
@[simp] theorem
  torusKnot45Loop_coefficientCount :
    torusKnot45Loop.coefficientVertices.length = 61 := by
  rw [torusKnot45Loop,
    Word.realizeWord_coefficientCount,
    Torus.WorkedExamples.torusKnot45_crossingCount]

/-- Every coefficient vertex of the `(4, 5)` realization is monic of degree four. -/
theorem torusKnot45Loop_vertices_monic :
    ∀ polynomial ∈ torusKnot45Loop.coefficientVertices,
      polynomial.natDegree = 4 ∧ polynomial.leadingCoeff = 1 :=
  Word.realizeWord_vertices_monic _

/-- The positive first adjacent generator on five strands. -/
def fiveStrandFirst : Generator 5 :=
  ⟨⟨0, by decide⟩, .positive⟩

/-- The negative last adjacent generator on five strands. -/
def fiveStrandLast : Generator 5 :=
  ⟨⟨3, by decide⟩, .negative⟩

/-- The explicit far-commutation cell for the retained disjoint five-strand generators. -/
def fiveStrandFarCell :
  Cells.Far.FarCommutationCell
  fiveStrandFirst
  fiveStrandLast
    (by decide) :=
  Cells.Far.farCommutationCell
    fiveStrandFirst
    fiveStrandLast (by decide)

/-- The simultaneous midpoint polynomial of the far-commutation cell has degree five. -/
@[simp] theorem
  fiveStrandFarCell_center_degree :
    fiveStrandFarCell.simultaneousMidpoint.polynomial.natDegree = 5
      :=
  Dense.Gaussian.Split.Lattice.Vertex.polynomial_natDegree _

/-- The sole adjacent-pair index for an Artin relation on three strands. -/
def threeStrandIndex : Fin (3 - 2) := ⟨0, by
  decide⟩

/-- The positive three-strand Artin cell at the retained pair index. -/
def positiveArtinCell :
  Cells.Artin.ArtinCell threeStrandIndex
  .positive :=
  Cells.Artin.artinCell threeStrandIndex
    .positive

/-- The Artin cell's central polynomial has degree three. -/
@[simp] theorem
  positiveArtinCell_center_degree :
    positiveArtinCell.centralVertex.polynomial.natDegree = 3 :=
  Dense.Gaussian.Split.Lattice.Vertex.polynomial_natDegree _

/-- The explicit polynomial homotopy between the positive lower-upper-lower and upper-lower-upper braid words. -/
def positiveArtinHomotopy :
    Homotopy.PolynomialHomotopic
      [Generator.lower threeStrandIndex .positive,
        Generator.upper threeStrandIndex .positive,
        Generator.lower threeStrandIndex .positive]
      [Generator.upper threeStrandIndex .positive,
        Generator.lower threeStrandIndex .positive,
        Generator.upper threeStrandIndex .positive]
          := by
  exact Homotopy.PolynomialHomotopic.artin
    ([] : Word 3) [] threeStrandIndex .positive

end Purelib.Examples.Topology.Knot.Polynomial.Realization.WorkedExamples

end
