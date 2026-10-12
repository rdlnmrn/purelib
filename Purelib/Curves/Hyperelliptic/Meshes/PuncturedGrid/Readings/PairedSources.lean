module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Curves

open Purelib.Data

open Purelib.Polynomial

@[expose] public section

/-! Ordered signed source pairs from the actual paired walk. The selection
retains both original sheet labels, the walk parent, and its source readbacks;
it supplies geometry to scalar and two-component cached comparisons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.PairedSources

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Source Sources)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {owner : OwnedPuncturedMesh curve}

/-- The walk type on the original retained grid. -/
@[reducible] def Walk (owner : OwnedPuncturedMesh curve) (start finish : Gaussian.Basic.Canonical) :=
  Geometry.Grid.Walks.Walk owner.base.bank.grid start finish
/-- The original paired-walk parent on its exact retained mesh. -/
@[reducible] def Parent {start finish : Gaussian.Basic.Canonical} (walk : Walk owner start finish) :=
  Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk owner.mesh walk
/-- One pair of original labeled sources. -/
@[reducible] def Pair (owner : OwnedPuncturedMesh curve) := Source owner × Source owner

/-- Read the original paired source occurrences recursively, transporting both labels through the actual retained edge
target. -/
def pairs : {start finish : Gaussian.Basic.Canonical} → {walk : Walk owner start finish} →
    Parent walk → Fin 2 → Fin 2 → List (Pair owner)
  | _, _, _, .nil _, _, _ => []
  | _, _, _, .cons (edge := edge) head tail, left, right =>
      (head.source left, head.source right) ::
        pairs tail ((owner.edges.edge edge).forward.target left) ((owner.edges.edge edge).forward.target right)

/-- The paired source list has the original walk's exact edge count. -/
theorem pairs_length : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2), (pairs paired left right).length = walk.edgeCount
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg Nat.succ (pairs_length tail _ _)

/-- The first projections are exactly the original paired walk's first source list. -/
theorem pairs_first : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2), (pairs paired left right).map Prod.fst = paired.sources left
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg (List.cons _) (pairs_first tail _ _)

/-- The second projections are exactly the original paired walk's second source list. -/
theorem pairs_second : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2), (pairs paired left right).map Prod.snd = paired.sources right
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg (List.cons _) (pairs_second tail _ _)

/-- Exact equality with the original retained list of paired source occurrences. -/
@[reducible] def PairIdentity {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2) (retained : List (Pair owner)) : Prop :=
  retained = pairs paired left right
/-- Exact identity with the original retained paired-walk parent. -/
@[reducible] def ParentIdentity {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired retained : Parent walk) : Prop := retained = paired
/-- Exact equality with an original retained source-list projection. -/
@[reducible] def SourceIdentity {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (sheet : Fin 2) (retained : Sources owner) : Prop :=
  retained = paired.sources sheet

set_option genInjectivity false in
/-- A cached reading of the original paired sources.

Retain the actual parent, paired entries, both projections and count with their defining identities. -/
structure Selection {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2) where
  /-- The actual retained original paired-walk parent. -/ parent : Parent walk
  /-- The selected parent is exactly the original supplied owner. -/ parent_eq : ParentIdentity paired parent
  /-- The cached ordered pairs of original labeled source occurrences. -/ entries : List (Pair owner)
  /-- The cached entries equal the original recursive paired reading. -/ entries_eq : PairIdentity paired left right
    entries
  /-- The cached first original source list. -/ first : Sources owner
  /-- The first list equals the original paired-walk source projection. -/ first_eq : SourceIdentity paired left first
  /-- The first list is the exact first projection of the retained paired entries. -/ first_entries : first =
    entries.map Prod.fst
  /-- The cached second original source list. -/ second : Sources owner
  /-- The second list equals the original paired-walk source projection. -/ second_eq : SourceIdentity paired right
    second
  /-- The second list is the exact second projection of the retained paired entries. -/ second_entries : second =
    entries.map Prod.snd
  /-- The cached original paired edge count. -/ count : Nat
  /-- The count equals the original retained walk's edge count. -/ count_eq : count = walk.edgeCount
  /-- The retained paired-entry list has exactly the cached original count. -/ entries_count : entries.length = count

constructive_injectivity Selection

/-- Read the original paired entries once and retain their two exact projections and original parent identity. -/
def realize {start finish : Gaussian.Basic.Canonical} {walk : Walk owner start finish}
    (paired : Parent walk) (left right : Fin 2) : Selection paired left right :=
  let entries := pairs paired left right
  let first := entries.map Prod.fst
  let second := entries.map Prod.snd
  { parent := paired
    parent_eq := rfl
    entries := entries
    entries_eq := rfl
    first := first
    first_eq := by exact pairs_first paired left right
    first_entries := rfl
    second := second
    second_eq := by exact pairs_second paired left right
    second_entries := rfl
    count := walk.edgeCount
    count_eq := rfl
    entries_count := by exact pairs_length paired left right }

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.PairedSources
