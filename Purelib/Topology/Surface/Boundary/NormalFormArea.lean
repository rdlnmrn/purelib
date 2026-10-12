module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Word.Selection
public import Purelib.LinearAlgebra.Alternating.Reduction.Dual
import Purelib.LinearAlgebra.Alternating.NormalForm.Evaluation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Bilinear

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Word

public section

/-!
# Evaluating the boundary form on its computed handles

The primitive increments are transformed by the inverse transpose of the
integral basis change. The retained handle sum is exactly the old matrix
contraction; it does not yet assert that those increments are period paths.
-/

namespace Purelib.Topology.Surface.Boundary

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra.Alternating
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)

variable {count : Nat}

namespace NormalFormArea

/-- Sum the oriented primitive areas at the retained ordered handle pairs. -/
@[expose] def handleArea : List (Handle.Basic.PivotIndices count) → Data.Vector Stokes.PrimitivePoint count
  → Gaussian.Basic.Canonical
  | [], _ => 0
  | pair :: remaining, values => Stokes.edgeArea (values pair.1) (values pair.2) +
    Purelib.Topology.Surface.Boundary.NormalFormArea.handleArea remaining values

end NormalFormArea

namespace NormalFormArea

open Purelib.Topology.Surface.Boundary in
/-- The algebraic handle pairing equals the area of the paired primitive-coordinate vector. -/
private theorem handlePairing_eq_area (raw : List (Handle.Basic.PivotIndices count))
    (left right : Data.Vector Gaussian.Basic.Canonical count) :
    Pairing.handlePairing raw left right = NormalFormArea.handleArea raw (Data.Vector.Basic.vectorOfFn fun index =>
      ⟨left index, right index⟩) := by
  induction raw with
  | nil => rfl
  | cons pair remaining ih =>
      rw [Pairing.handlePairing, NormalFormArea.handleArea, Data.Vector.Basic.vectorOfFn_apply,
        Data.Vector.Basic.vectorOfFn_apply, ih]
      rfl

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.

end NormalFormArea

set_option genInjectivity false in
/-- Transformed values and the final handle area are cached data. The equations permit any equivalent checked cache, not
just the constructor. -/
structure NormalFormArea {matrix : LinearAlgebra.Matrix.IntegralMatrix count} {raw : List
  (Handle.Basic.PivotIndices count)}
    (normal : LinearAlgebra.Alternating.NormalForm matrix raw) (values : Data.Vector Stokes.PrimitivePoint count)
      where
  /-- Cached left primitive coordinates after the retained dual reduction. -/ left : Data.Vector
    Gaussian.Basic.Canonical count
  /-- The cached left vector is the exact dual transform of the input left coordinates. -/ left_eq : left =
    normal.reduction.dualForward (Data.Vector.Basic.vectorOfFn fun index => (values index).left)
  /-- Cached right primitive coordinates after the retained dual reduction. -/ right : Data.Vector
    Gaussian.Basic.Canonical count
  /-- The cached right vector is the exact dual transform of the input right coordinates. -/ right_eq : right =
    normal.reduction.dualForward (Data.Vector.Basic.vectorOfFn fun index => (values index).right)
  /-- Retained primitive points assembled from the two transformed coordinate vectors. -/ points :
    Data.Vector Stokes.PrimitivePoint count
  /-- Each retained point contains the corresponding cached left and right coordinates. -/ points_eq : points =
    Data.Vector.Basic.vectorOfFn fun index => ⟨left index, right index⟩
  /-- Cached Gaussian rational value of the transformed handle pairing. -/ area : Gaussian.Basic.Canonical
  /-- The retained area is the handle pairing of the exact cached coordinate vectors. -/ area_eq : area =
    Pairing.handlePairing raw left right

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity NormalFormArea

namespace NormalFormArea

variable {matrix : LinearAlgebra.Matrix.IntegralMatrix count} {raw : List
  (Handle.Basic.PivotIndices count)}
  {normal : LinearAlgebra.Alternating.NormalForm matrix raw} {values : Data.Vector Stokes.PrimitivePoint count}

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Boundary in
/-- Cache both dual-transformed primitive coordinate vectors and their handle area.

The retained points and scalar evaluation use the same exact normal-form reduction and input values. -/
@[expose] def build (normal : LinearAlgebra.Alternating.NormalForm matrix raw) (values : Data.Vector
  Stokes.PrimitivePoint count) :
    NormalFormArea normal values :=
  let left := normal.reduction.dualForward (Data.Vector.Basic.vectorOfFn fun index => (values index).left)
  let right := normal.reduction.dualForward (Data.Vector.Basic.vectorOfFn fun index => (values index).right)
  let points := Data.Vector.Basic.vectorOfFn fun index => (⟨left index, right index⟩ : Stokes.PrimitivePoint)
  ⟨left, rfl, right, rfl, points, rfl, Pairing.handlePairing raw left right, rfl⟩

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Boundary in
/-- The cached algebraic pairing equals the handle-area sum on its retained primitive points. -/
theorem area_eq_handles (sample : NormalFormArea normal values) : sample.area = NormalFormArea.handleArea
  raw sample.points := by
  rw [sample.area_eq, sample.points_eq]
  exact NormalFormArea.handlePairing_eq_area raw sample.left sample.right

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Boundary in
/-- The original matrix contraction equals the cached normal-form area. -/
theorem contract_eq (sample : NormalFormArea normal values) :
    Pairing.contract (fun row column => matrix row column) values = sample.area := by
  let first := Data.Vector.Basic.vectorOfFn fun index => (values index).left
  let last := Data.Vector.Basic.vectorOfFn fun index => (values index).right
  have source : Pairing.contract (fun row column => matrix row column) values = Integral.pairing matrix first last := by
    apply FiniteSum.Fin.sumFin_congr; intro row
    apply FiniteSum.Fin.sumFin_congr; intro column
    dsimp only
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  rw [source, normal.pairing, sample.area_eq, sample.left_eq, sample.right_eq]

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Boundary in
/-- The inverse dual reduction recovers the original left primitive coordinates. -/
theorem restore_left (sample : NormalFormArea normal values) :
    normal.reduction.dualBackward sample.left = Data.Vector.Basic.vectorOfFn fun index => (values index).left := by
  rw [sample.left_eq, normal.reduction.dualBackward_dualForward]

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
open Purelib.Topology.Surface.Boundary in
/-- The inverse dual reduction recovers the original right primitive coordinates. -/
theorem restore_right (sample : NormalFormArea normal values) :
    normal.reduction.dualBackward sample.right = Data.Vector.Basic.vectorOfFn fun index => (values index).right := by
  rw [sample.right_eq, normal.reduction.dualBackward_dualForward]

end NormalFormArea

namespace NormalFormArea.CutBoundaryWord.AreaSample

open Purelib.Topology.Surface.Boundary in
/-- On a closed cut boundary, normalizing its paired block preserves the complete physical-boundary and
primitive-compatibility correction. -/
theorem closed_handle_area_eq
    {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
    {word : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source → Stokes.PrimitivePoint} {anchor : Fin
      source}
    (sample : CutBoundaryWord.AreaSample word primitive (primitive anchor))
    (pairing : Cut.IntegralPairing.CutBoundaryWord word) {raw : List (Handle.Basic.PivotIndices word.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm pairing.paired raw) (evaluated : NormalFormArea normal
      sample.values)
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor) :
    Stokes.edgeListArea primitive edges = 2 * evaluated.area +
      Pairing.contract (fun row column => pairing.remaining row column) sample.values + sample.closedCorrection := by
  rw [sample.closed_area_eq closed, pairing.contract_eq, evaluated.contract_eq]

end NormalFormArea.CutBoundaryWord.AreaSample

end Purelib.Topology.Surface.Boundary
