module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence
public import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Topology.Mesh.RetracingWords (Retracing)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

public section

/-!
# Exact finite retracing comparisons for ordered grid circuits

These comparisons preserve both the actual endpoint sheet and every
antisymmetric valuation and complete increment area of the lifted edge
word. The finite retracing proof itself is retained. In particular a branch circuit is never removed by declaring
its coordinate closure to be root closure.
-/

section

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk

/-- Appending an empty grid walk leaves the original walk unchanged. -/
theorem append_nil {start finish : Gaussian.Basic.Canonical} (walk : Walk grid start finish) :
  walk.append (.nil _) = walk := by
  induction walk with
  | nil => rfl
  | cons edge tail ih => exact congrArg (Walk.cons edge) ih

/-- Grid-walk append is associative with the original endpoints. -/
theorem append_assoc {first second third last : Gaussian.Basic.Canonical}
    (a : Walk grid first second) (b : Walk grid second third) (c :
      Walk grid third last) :
    (a.append b).append c = a.append (b.append c) := by
  induction a with
  | nil => rfl
  | cons edge tail ih => exact congrArg (Walk.cons edge) (ih b)

/-- Reversing a walk onto a joined suffix commutes with the suffix append. -/
private theorem reverseOnto_append {first second third last : Gaussian.Basic.Canonical}
    (a : Walk grid first second) (b : Walk grid first third) (c :
      Walk grid third last) :
    a.reverseOnto (b.append c) = (a.reverseOnto b).append c := by
  induction a generalizing third with
  | nil => rfl
  | cons edge tail ih => exact ih (.cons (.reverse edge) b) c

/-- Reversing onto a suffix equals appending that suffix to the original reversed walk. -/
theorem reverseOnto_eq_append {first second last : Gaussian.Basic.Canonical}
    (a : Walk grid first second) (b : Walk grid first last) : a.reverseOnto b =
      a.reverse.append b :=
  reverseOnto_append a (.nil _) b

/-- Reverse accumulation of an appended walk processes the second walk before the first. -/
private theorem append_reverseOnto {first second third last : Gaussian.Basic.Canonical}
    (a : Walk grid first second) (b : Walk grid second third) (c :
      Walk grid first last) :
    (a.append b).reverseOnto c = b.reverseOnto (a.reverseOnto c) := by
  induction a with
  | nil => rfl
  | cons edge tail ih => exact ih b (.cons (.reverse edge) c)

/-- Reversing an appended grid walk appends the reversed walks in opposite order. -/
theorem reverse_append {first second last : Gaussian.Basic.Canonical} (a : Walk grid first second)
  (b : Walk grid second last) :
    (a.append b).reverse = b.reverse.append a.reverse := by
  rw [Walk.reverse, append_reverseOnto,
    reverseOnto_eq_append]
  rfl

/-- Base a retained grid loop at the start of its original stem.

The original stem, loop and reversed stem occur in that order, preserving
the original grid, endpoints and every directed edge occurrence. -/
@[expose] def based
    {first last : Gaussian.Basic.Canonical} (stem : Walk grid first last) (loop :
      Walk grid last last) : Walk grid first first :=
  stem.append (loop.append stem.reverse)

/-- Traverse four retained grid sides in positive rectangle boundary order.

The bottom and right walks are followed by the reversed top and left walks.
Their original corner coordinates and directed edge occurrences are retained. -/
@[expose] def rectangle
    {lowerLeft lowerRight upperLeft upperRight : Gaussian.Basic.Canonical}
    (bottom : Walk grid lowerLeft lowerRight) (right : Walk grid lowerRight
      upperRight)
    (top : Walk grid upperLeft upperRight) (left : Walk grid lowerLeft
      upperLeft) : Walk grid lowerLeft lowerLeft :=
  bottom.append (right.append (top.reverse.append left.reverse))

end Purelib.Polynomial.Geometry.Grid.Walks.Walk

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {frames : RootFrames grid} {vertices : VertexBank
  grid} {edges : RootEdgeBank frames}

/-- Sum the supplied edge values along the original indexed sheet lift. -/
@[expose] def chainValue
    (edges : RootEdgeBank frames) (vertices : VertexBank
      grid)
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) {start finish :
      Gaussian.Basic.Canonical} (walk : Walk grid start finish) (sheet : Fin 2) :
  Gaussian := Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices walk sheet)

/-- Read the finite word area along the original indexed sheet lift. -/
@[expose] def chainArea
    (edges : RootEdgeBank frames) (vertices : VertexBank
      grid)
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) {start finish :
      Gaussian.Basic.Canonical} (walk : Walk grid start finish) (sheet : Fin 2) :
    Gaussian := Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices walk sheet)

/-- Joining grid walks adds their chain values with the second lift starting on the transported sheet. -/
theorem chainValue_append
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) {first middle last :
      Gaussian.Basic.Canonical}
    (a : Walk grid first middle) (b : Walk grid middle last) (sheet : Fin 2) :
    edges.chainValue vertices value (a.append b) sheet =
      edges.chainValue vertices value a sheet + edges.chainValue vertices value b
        (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges a sheet) := by
  rw [chainValue,
    edges.indexedEdges_append, Topology.Surface.Sewing.SewingRetraction.wordValue_append]
  rfl

/-- Joining grid walks adds their chain areas and the exact cross-ribbon area of their retained chain values. -/
theorem chainArea_append
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) {first middle last :
      Gaussian.Basic.Canonical}
    (a : Walk grid first middle) (b : Walk grid middle last) (sheet : Fin 2) :
    edges.chainArea vertices value (a.append b) sheet =
      edges.chainArea vertices value a sheet + edges.chainArea vertices value b
        (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges a sheet) +
        Integration.Path.BoundaryRibbon.area (edges.chainValue vertices value a sheet)
          (edges.chainValue vertices value b (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges a sheet)) := by
  rw [chainArea,
    edges.indexedEdges_append, Topology.Mesh.RetracingWords.wordArea_append]
  rfl

/-- Following the reverse walk and then the original walk restores the original terminal sheet. -/
theorem target_reverse_right
    (edges : RootEdgeBank frames)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {start finish : Gaussian.Basic.Canonical} (walk : Walk grid start finish) (sheet : Fin 2) :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges
      walk.reverse sheet) = sheet := by
  apply edges.target_injective reference walk.reverse
  exact edges.target_reverse reference walk (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk.reverse sheet)

/-- A comparison of two finite grid words, before any analytic face-zero
or physical-boundary relation. Every initial sheet is accounted for. -/
structure ChainComparison {start finish : Gaussian.Basic.Canonical} (edges : RootEdgeBank
  frames) (vertices : VertexBank grid)
    (first last : Walk grid start finish) : Prop where
  /-- The compared original grid walks have identical terminal sheet maps. -/ targets : ∀ sheet,
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges first sheet = SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges
    last sheet
  /-- For each original sheet, the actual indexed edge lists are related by finite retracing. -/ words : ∀ sheet,
    Retracing (edges.indexedEdges vertices first sheet) (edges.indexedEdges vertices last
    sheet)

namespace ChainComparison

variable {first middle last : Gaussian.Basic.Canonical}

/-- A retained chain comparison preserves every antisymmetric edge-value sum on each original sheet. -/
theorem values {a b : Walk grid first last} (same :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b)
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) (sheet : Fin 2) :
    edges.chainValue vertices value a sheet = edges.chainValue vertices value b sheet := (same.words sheet).values value
      anti

/-- A retained chain comparison preserves every antisymmetric finite word area on each original sheet. -/
theorem areas {a b : Walk grid first last} (same :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b)
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) (sheet : Fin 2) :
    edges.chainArea vertices value a sheet = edges.chainArea vertices value b sheet := (same.words sheet).areas value
      anti

/-- Every retained grid walk compares to itself on both sheets. -/
theorem refl (walk : Walk grid first last) :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices walk walk := ⟨fun _ => rfl, fun _ =>
  .refl _⟩

/-- Equality of original grid walks gives their exact chain comparison. -/
theorem of_eq {a b : Walk grid first last} (equal : a = b) :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b := by
  cases equal
  exact SquareRoot.Grid.RootEdgeBank.ChainComparison.refl a

/-- Reverse a retained comparison of the same original grid walks. -/
theorem symm {a b : Walk grid first last} (same :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b) :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices b a :=
  ⟨fun sheet => (same.targets sheet).symm, fun sheet => (same.words sheet).symm⟩

/-- Compose chain comparisons through their shared original middle walk. -/
theorem trans {a b c : Walk grid first last} (ab :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b)
    (bc : SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices b c) :
      SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a c :=
  ⟨fun sheet => (ab.targets sheet).trans (bc.targets sheet),
    fun sheet => (ab.words sheet).trans (bc.words sheet)⟩

/-- Append two compatible retained comparisons, transporting each suffix to the original target sheet. -/
theorem append {a b : Walk grid first middle} {c d : Walk grid middle last}
    (ab : SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b) (cd :
      SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices c d) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (a.append c) (b.append d) where
  targets := fun sheet => by
    rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges,
      SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges, ab.targets, cd.targets]
  words := fun sheet => by
    rw [edges.indexedEdges_append, edges.indexedEdges_append, ab.targets]
    exact (ab.words sheet).append (cd.words _)

/-- An original walk followed by its reverse compares to the empty walk at its start. -/
theorem retrace (reference : ∀ point, ContainsVertex grid point →
  WindingOneLoop polynomial point)
    (walk : Walk grid first last) :
      SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (walk.append walk.reverse) (.nil
      first) where
  targets := fun sheet => by
    rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges, edges.target_reverse reference]; rfl
  words := fun sheet => by
    rw [edges.indexedEdges_append, edges.indexedEdges_reverse vertices reference]
    exact Retracing.retrace _

/-- A reversed original walk followed by that walk compares to the empty walk at its finish. -/
theorem reverse_retrace (reference : ∀ point, ContainsVertex grid point →
  WindingOneLoop polynomial point)
    (walk : Walk grid first last) :
      SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (walk.reverse.append walk) (.nil
      last) where
  targets := fun sheet => by
    rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges, edges.target_reverse_right reference]; rfl
  words := fun sheet => by
    have reversed := edges.indexedEdges_reverse vertices reference walk (SquareRoot.Grid.EdgeBank.RootEdgeBank.target
      edges walk.reverse sheet)
    rw [edges.target_reverse_right reference] at reversed
    rw [edges.indexedEdges_append, reversed]
    exact Retracing.reverse_retrace _

/-- Erase an actual reversed-and-forward walk from the middle of a retained grid word. -/
theorem erase_reverse_retrace
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {a b c d : Gaussian.Basic.Canonical} (initial : Walk grid a c) (walk : Walk
      grid b c) (suffix : Walk grid c d) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (initial.append
      (walk.reverse.append (walk.append suffix))) (initial.append suffix) := by
  have same := (SquareRoot.Grid.RootEdgeBank.ChainComparison.refl (edges := edges) (vertices :=
    vertices) initial).append
    ((SquareRoot.Grid.RootEdgeBank.ChainComparison.reverse_retrace reference walk).append
      (SquareRoot.Grid.RootEdgeBank.ChainComparison.refl suffix))
  simpa only [Walk.append_assoc, Walk.append] using same

/-- Join the same original stem and its reverse around both compared loops. -/
theorem based {a b : Walk grid last last} (same :
  SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices a b) (stem : Walk
  grid first last) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (stem.based a) (stem.based b) :=
  (SquareRoot.Grid.RootEdgeBank.ChainComparison.refl stem).append (same.append
    (SquareRoot.Grid.RootEdgeBank.ChainComparison.refl stem.reverse))

/-- Joining two stem-based loops compares to basing their concatenation at that same original stem. -/
theorem based_append
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (stem : Walk grid first last) (a b : Walk grid last last) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices ((stem.based a).append (stem.based
      b)) (stem.based (a.append b)) := by
  have cancelled := SquareRoot.Grid.RootEdgeBank.ChainComparison.erase_reverse_retrace (edges :=
    edges) (vertices := vertices) reference
    (stem.append a) stem (b.append stem.reverse)
  simpa only [Walk.based, Walk.append_assoc] using cancelled

/-- Independently retained line certificates for one affine side have the
same actual lifted edge. This handles adjacent-cell payload handoffs. -/
theorem edge (reference : ∀ point, ContainsVertex grid point →
  WindingOneLoop polynomial point)
    (a b : Geometry.Grid.Walks.Edge grid first last) : SquareRoot.Grid.RootEdgeBank.ChainComparison
      edges vertices (.cons a (.nil _)) (.cons b (.nil _)) where
  targets := fun sheet => (edges.edge a).forward_target_eq (edges.edge b)
    (reference _ a.vertices.1) (reference _ a.vertices.2) sheet
  words := fun sheet => by
    change Retracing [edges.indexedEdge vertices a sheet] [edges.indexedEdge vertices b
      sheet]
    rw [edges.indexedEdge_eq vertices a b (reference _ a.vertices.1) (reference _ a.vertices.2)]
    exact .refl _

/-- Sew the right rectangle before the left rectangle along their retained seam.

The original bottom connector and common vertical side are erased in order.
The comparison retains the actual grid words, endpoints and both sheet lifts. -/
theorem horizontal_sewing
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {a b c d e f : Gaussian.Basic.Canonical} (bottomLeft : Walk grid a b) (bottomRight :
      Walk grid b c)
    (right : Walk grid c f) (topRight : Walk grid e f) (topLeft :
      Walk grid d e)
    (left : Walk grid a d) (seam : Walk grid b e) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      ((bottomLeft.based (Walk.rectangle bottomRight right topRight seam)).append
        (Walk.rectangle bottomLeft seam topLeft left))
      (Walk.rectangle (bottomLeft.append bottomRight) right (topLeft.append topRight) left) := by
  let initial := bottomLeft.append (bottomRight.append (right.append topRight.reverse))
  let suffix := topLeft.reverse.append left.reverse
  have first := SquareRoot.Grid.RootEdgeBank.ChainComparison.erase_reverse_retrace (edges := edges)
    (vertices := vertices) reference
    (initial.append seam.reverse) bottomLeft (seam.append suffix)
  have second := SquareRoot.Grid.RootEdgeBank.ChainComparison.erase_reverse_retrace (edges :=
    edges) (vertices := vertices) reference initial seam suffix
  apply (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (first.trans
    ((SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (second.trans
    (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_))))
  · simp only [Walk.based, Walk.rectangle, initial, suffix,
      Walk.append_assoc, -eq_self, -iff_self]
    rfl
  · simp only [Walk.append_assoc, -eq_self, -iff_self]
    rfl
  · simp only [Walk.rectangle, Walk.reverse_append, initial,
      suffix, Walk.append_assoc, -eq_self, -iff_self]
    rfl

/-- Sew the lower rectangle before the upper rectangle along their retained seam.

The common left connector and horizontal seam are erased in order. Both
cancellations retain the arriving sheet and original indexed edge word. -/
theorem vertical_sewing {frames : RootFrames grid} {vertices :
  VertexBank grid} {edges :
  RootEdgeBank frames}
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    {a b c d e f : Gaussian.Basic.Canonical} (bottom : Walk grid a b) (rightLower :
      Walk grid b d)
    (rightUpper : Walk grid d f) (top : Walk grid e f) (leftUpper :
      Walk grid c e)
    (leftLower : Walk grid a c) (seam : Walk grid c d) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
      ((Walk.rectangle bottom rightLower seam leftLower).append
        (leftLower.based (Walk.rectangle seam rightUpper top leftUpper)))
      (Walk.rectangle bottom (rightLower.append rightUpper) top (leftLower.append leftUpper)) := by
  let initial := bottom.append rightLower
  let suffix := rightUpper.append (top.reverse.append (leftUpper.reverse.append leftLower.reverse))
  have first := SquareRoot.Grid.RootEdgeBank.ChainComparison.erase_reverse_retrace (edges := edges)
    (vertices := vertices) reference
    (initial.append seam.reverse) leftLower (seam.append suffix)
  have second := SquareRoot.Grid.RootEdgeBank.ChainComparison.erase_reverse_retrace (edges :=
    edges) (vertices := vertices) reference initial seam suffix
  apply (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (first.trans
    ((SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (second.trans
    (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_))))
  · simp only [Walk.rectangle, Walk.based, initial, suffix,
      Walk.append_assoc, -eq_self, -iff_self]
    rfl
  · simp only [Walk.append_assoc, -eq_self, -iff_self]
    rfl
  · simp only [Walk.rectangle, Walk.reverse_append, initial,
      suffix, Walk.append_assoc, -eq_self, -iff_self]
    rfl

end ChainComparison
end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
end
