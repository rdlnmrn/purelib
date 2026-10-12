module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-!
# Exact cancellation of intermediate original fragment readings

The cached closed original word is reduced to changes of face chart.
Equal-chart endpoint readings cancel literally. Every retained transition
keeps the original common point and query-root agreement; no transition
between different charts is declared small or discarded.
-/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.BranchCellBank
open
  LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}
  {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {index : Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings

/-- A chart is an actual retained face-bank position and its root sheet. -/
@[expose] def chart (piece : RootedWords.LiftedFragment axes domains mesh source count target) : Fin
  base.faces.regulars.length × Fin 2 :=
  ⟨piece.fragment.face.located.index, piece.assigned.entry.sheet⟩

/-- Read the supplied point from the actual fragment's retained face-bank position and root sheet. -/
@[expose] def atPoint (piece : RootedWords.LiftedFragment axes domains mesh source count target) (shared :
  CommonMeshes.FaceSharedMeshes budgets numerics)
    (point : Data.Gaussian.Basic.Canonical) : Gaussian :=
  SharedPrimitiveValues.atPoint
    ((FaceSharedMeshes.get shared (chart
      piece).1).atSheet (chart piece).2).readings point

/-- The assigned fragment mesh reading equals the reading selected by its exact original chart identity. -/
theorem assigned_atPoint (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (point : Data.Gaussian.Basic.Canonical) :
    SharedPrimitiveValues.atPoint
      (BankReadings.meshReadings piece.assigned shared).readings point =
      atPoint piece shared point :=
  (DomainMeshReadings.castDomain_atPoint piece.assigned.domain_eq.symm
    (((FaceSharedMeshes.get shared piece.fragment.face.located.index).castFace
      piece.fragment.face.located.indexed).atSheet
      piece.assigned.entry.sheet) point).trans
    (FaceMeshReadings.castFace_atPoint piece.fragment.face.located.indexed
      (FaceSharedMeshes.get shared piece.fragment.face.located.index) piece.assigned.entry.sheet point)

/-- The actual fragment value equals the difference of its retained chart's original endpoint readings. -/
theorem value_eq_atPoint (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    piece.value shared = (atPoint piece) shared
      piece.last - (atPoint piece) shared piece.first :=
  (LiftedSource.value_eq piece.occurrence shared).trans
    (congrArg₂ (· - ·) (assigned_atPoint piece shared
      piece.last) (assigned_atPoint piece shared
      piece.first))

/-- Equal retained face-and-sheet charts give equal readings at equal original points. -/
theorem atPoint_eq_of_chart {first last : RootedWords.LiftedFragment axes domains mesh source count target}
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (equal :
      (chart first) =
      (chart last))
    {a b : Data.Gaussian.Basic.Canonical} (pointEq : a = b) :
      (atPoint first) shared a =
      (atPoint last) shared b :=
  congrArg₂ (fun (owner : Fin base.faces.regulars.length × Fin 2) point =>
    SharedPrimitiveValues.atPoint
      ((FaceSharedMeshes.get shared owner.1).atSheet owner.2).readings point) equal pointEq

set_option genInjectivity false in
/-- A genuine change of chart, carrying both actual original endpoint roots and cached numerical readings. The root
comparison is erased proof data. -/
structure Seam (shared : CommonMeshes.FaceSharedMeshes budgets numerics) : Type 2 where
  /-- The original fragment ending at this retained chart transition. -/ left : RootedWords.LiftedFragment axes domains
    mesh source count target
  /-- The original fragment beginning at this retained chart transition. -/ right : RootedWords.LiftedFragment axes
    domains mesh source count target
  /-- The actual original transition endpoints are the same coordinate. -/ coordinate : left.last = right.first
  /-- The actual original endpoint root names retain a comparison witness. -/ roots : Nonempty
    (Gaussian.Equivalence.NamedEquivalent left.lastName right.firstName)
  /-- The two retained face-bank and root-sheet chart identities are distinct. -/ different :
    (chart left) ≠
    (chart right)
  /-- The cached original left-chart endpoint reading. -/ leftValue : Data.Gaussian.Basic.Canonical
  /-- The left cache equals the retained left fragment's actual terminal reading. -/ leftValue_eq : leftValue =
    (atPoint left) shared left.last
  /-- The cached original right-chart endpoint reading. -/ rightValue : Data.Gaussian.Basic.Canonical
  /-- The right cache equals the retained right fragment's actual initial reading. -/ rightValue_eq : rightValue =
    (atPoint right) shared right.first
  /-- The cached actual left-minus-right chart-transition discrepancy. -/ value : Data.Gaussian.Basic.Canonical
  /-- The transition discrepancy is exactly the difference of its retained endpoint reading caches. -/ value_eq : value
    = leftValue - rightValue

constructive_injectivity Seam

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam

/-- Cache the original endpoint readings and discrepancy at the supplied genuine chart transition, retaining coordinate
and root agreement. -/
@[expose] def build (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (left right : RootedWords.LiftedFragment axes domains mesh source count target)
    (coordinate : left.last = right.first) (roots : Nonempty (Gaussian.Equivalence.NamedEquivalent left.lastName
      right.firstName))
    (different : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.chart left) ≠
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.chart right)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh) (count :=
      count) (target := target) shared :=
  let first := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.atPoint left) shared left.last
  let last := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.atPoint right) shared right.first
  ⟨left, right, coordinate, roots, different, first, rfl, last, rfl, first - last, rfl⟩

/-- Retain an actual chart-changing junction before the original tail, cancelling equal-chart endpoint readings exactly.
-/
@[expose] def prepend (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (left right : RootedWords.LiftedFragment axes domains mesh source count target)
    (coordinate : left.last = right.first) (roots : Nonempty (Gaussian.Equivalence.NamedEquivalent left.lastName
      right.firstName))
    (tail : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh)
      (count := count) (target := target) shared)) : List
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh) (count :=
      count) (target := target) shared) :=
  if equal : (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.chart left) =
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.chart right) then tail else
    build shared left right coordinate roots equal
    :: tail

/-- Every retained prepended seam is the supplied original junction or an unchanged member of the tail. -/
theorem prepend_member (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (left right : RootedWords.LiftedFragment axes domains mesh source count target)
    (coordinate : left.last = right.first) (roots : Nonempty (Gaussian.Equivalence.NamedEquivalent left.lastName
      right.firstName))
    (tail : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh)
      (count := count) (target := target) shared))
    {seam : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh) (count :=
      count) (target := target) shared}
    (member : seam ∈ prepend shared left
      right coordinate roots tail) :
    (seam.left = left ∧ seam.right = right) ∨ seam ∈ tail := by
  unfold prepend at member
  split at member
  · exact Or.inr member
  · rcases Membership.mem_cons.mp member with rfl | member
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr member

/-- Prepending the actual junction preserves the exact original endpoint discrepancy in the seam sum. -/
theorem prepend_sum (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (left right : RootedWords.LiftedFragment axes domains mesh source count target)
    (coordinate : left.last = right.first) (roots : Nonempty (Gaussian.Equivalence.NamedEquivalent left.lastName
      right.firstName))
    (tail : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh)
      (count := count) (target := target) shared)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((prepend shared left right
      coordinate roots tail).map Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.value) =
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.atPoint left) shared left.last -
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.atPoint right) shared right.first +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.value) := by
  unfold prepend
  split
  · rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.atPoint_eq_of_chart shared ‹_› coordinate]
    ring1
  · rfl

/-- Prepending an actual junction adds at most one retained chart transition. -/
theorem prepend_length (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (left right : RootedWords.LiftedFragment axes domains mesh source count target)
    (coordinate : left.last = right.first) (roots : Nonempty (Gaussian.Equivalence.NamedEquivalent left.lastName
      right.firstName))
    (tail : List (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam (axes := axes) (mesh := mesh)
      (count := count) (target := target) shared)) :
    (prepend shared left right coordinate
      roots tail).length ≤ tail.length + 1 := by
  unfold prepend
  split
  · exact Nat.le_succ _
  · exact le_rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord

/-- A nonempty rooted word exposes the original first fragment's coordinate and root connection and exact remaining
tail. -/
theorem connection {piece : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (piece :: pieces) first firstName last lastName) :
    first = piece.first ∧ Nonempty (Gaussian.Equivalence.NamedEquivalent firstName piece.firstName) ∧
      LiftedFragment.RootedWord pieces piece.last piece.lastName last lastName := by
  cases word with
  | cons _ coordinate roots tail => exact ⟨coordinate, roots, tail⟩

/-- An empty rooted word retains equality of its original endpoints and a root-name comparison. -/
theorem empty {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (axes := axes) (domains := domains) (mesh := mesh) (source := source) (count :=
      count) (target := target)
      [] first firstName last lastName) : first = last ∧ Nonempty (Gaussian.Equivalence.NamedEquivalent firstName
        lastName) := by
  cases word with
  | nil coordinate roots => exact ⟨coordinate, roots⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings

/-- Read each remaining chart transition once. The recursive parameter keeps the full original tail and the closing
connection to its first piece. -/
@[expose] def seamWalk (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (first : RootedWords.LiftedFragment axes domains mesh source count target) :
    (current : RootedWords.LiftedFragment axes domains mesh source count target) →
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)) →
    LiftedFragment.RootedWord pieces current.last current.lastName first.first first.firstName → List
      (Seam (axes := axes) (mesh := mesh) (count :=
      count) (target := target) shared)
  | current, [], word => Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend shared current
    first (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).1
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).2 []
  | current, next :: rest, word => Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend shared
    current next (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).1
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.1
      (seamWalk shared first next rest
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.2)

/-- The retained transition sum equals the original fragment-tail sum with its actual endpoint readings. -/
theorem seamWalk_sum (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (first : RootedWords.LiftedFragment axes domains mesh source count target) :
    ∀ (current : RootedWords.LiftedFragment axes domains mesh source count target)
      (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target))
      (word : LiftedFragment.RootedWord pieces current.last current.lastName first.first first.firstName),
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((seamWalk shared first current pieces word).map
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.value) =
      (atPoint current) shared current.last +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => piece.value shared)) -
        (atPoint first) shared first.first
  | current, [], word => by
      rw [seamWalk,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_sum]
      change _ + 0 = _ + 0 - _
      ring1
  | current, next :: rest, word => by
      rw [seamWalk,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_sum,
        seamWalk_sum shared first next rest
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.2]
      change _ = (atPoint current) shared current.last +
        (next.value shared + Data.Gaussian.Norm.Sum.Basic.gaussianSum _) - _
      rw [value_eq_atPoint next shared]
      ring1

/-- The retained transition walk has at most one seam for each original junction including closure. -/
theorem seamWalk_length (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (first : RootedWords.LiftedFragment axes domains mesh source count target) :
    ∀ (current : RootedWords.LiftedFragment axes domains mesh source count target)
      (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target))
      (word : LiftedFragment.RootedWord pieces current.last current.lastName first.first first.firstName),
      (seamWalk shared first current pieces word).length
        ≤ pieces.length + 1
  | current, [], word => Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_length shared
    current first (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).1
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).2 []
  | current, next :: rest, word =>
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_length shared current next
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).1
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.1 _).trans
        (Nat.succ_le_succ (seamWalk_length
          shared first next rest (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection
          word).2.2))

/-- Both fragments of every actual retained seam belong to the original fragment list. -/
theorem seamWalk_members (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (first : RootedWords.LiftedFragment axes domains mesh source count target)
    (originals : List (RootedWords.LiftedFragment axes domains mesh source count target)) (firstMem : first ∈ originals)
      :
    ∀ (current : RootedWords.LiftedFragment axes domains mesh source count target)
      (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target))
      (word : LiftedFragment.RootedWord pieces current.last current.lastName first.first first.firstName),
      current ∈ originals → (∀ piece ∈ pieces, piece ∈ originals) →
      ∀ seam ∈ seamWalk shared first current pieces
        word, seam.left ∈ originals ∧ seam.right ∈ originals
  | current, [], word, currentMem, _, seam, member => by
      rcases Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_member shared current first
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).1
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.empty word).2 [] member with pair |
        absent
      · exact ⟨pair.1 ▸ currentMem, pair.2 ▸ firstMem⟩
      · exact (List.not_mem_nil absent).elim
  | current, next :: rest, word, currentMem, remaining, seam, member => by
      rcases Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.prepend_member shared current next
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).1
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.1 _ member with
        pair | member
      · exact ⟨pair.1 ▸ currentMem, pair.2 ▸ remaining next List.mem_cons_self⟩
      · exact seamWalk_members shared first
          originals firstMem next rest
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word).2.2
          (remaining next List.mem_cons_self) (fun piece present => remaining piece (List.mem_cons_of_mem _ present))
            seam member

set_option genInjectivity false in
/-- Exact chart-transition reduction of one cached closed original word. -/
structure ClosedSeams (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)) : Type 2 where
  /-- The cached ordered list of actual original chart-changing seams. -/ entries : List
    (Seam (axes := axes) (mesh := mesh) (count := count)
    (target := target) shared)
  /-- Both endpoints of every retained seam are actual members of the original fragment list. -/ entries_mem : ∀ seam ∈
    entries, seam.left ∈ pieces ∧ seam.right ∈ pieces
  /-- The cached number of retained chart transitions. -/ count : Nat
  /-- The transition count is exactly the cached seam-list length. -/ count_eq : count = entries.length
  /-- There are no more retained transitions than actual original fragments. -/ count_le : count ≤ pieces.length
  /-- The cached ordered actual seam discrepancies. -/ values : List Data.Gaussian.Basic.Canonical
  /-- The discrepancy list is exactly the readback of the retained seam entries. -/ values_eq : values = entries.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.value
  /-- The cached complete actual chart-transition discrepancy. -/ sum : Data.Gaussian.Basic.Canonical
  /-- The discrepancy cache is exactly the Gaussian sum of the retained seam values. -/ sum_eq : sum =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The seam sum equals the exact original closed fragment-word sum. -/ original_eq : sum =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => piece.value shared))

constructive_injectivity ClosedSeams

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.ClosedSeams

/-- Reduce the supplied original closed rooted word to its actual chart changes, retaining exact coverage, count and
total readback. -/
@[expose] def build (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)) {point :
      Data.Gaussian.Basic.Canonical} {root : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord pieces point root point root) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.ClosedSeams shared pieces := by
  cases pieces with
  | nil => exact ⟨[], fun _ member => (List.not_mem_nil member).elim, 0, rfl, le_rfl, [], rfl, 0, rfl, rfl⟩
  | cons first rest =>
      have head := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.RootedWord.connection word)
      have closing : LiftedFragment.RootedWord (axes := axes) (domains := domains) (mesh := mesh) (source := source)
        (count := count) (target := target)
          [] point root first.first first.firstName := .nil head.1 head.2.1
      have tail : LiftedFragment.RootedWord rest first.last first.lastName first.first first.firstName := by
        simpa only [Append.append_nil, -eq_self, -iff_self] using head.2.2.append closing
      let entries := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.seamWalk shared first first rest
        tail
      let values := entries.map Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.Seam.value
      let sum := Data.Gaussian.Norm.Sum.Basic.gaussianSum values
      refine ⟨entries, Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.seamWalk_members shared first
        (first :: rest) List.mem_cons_self first rest tail
        List.mem_cons_self (fun _ member => List.mem_cons_of_mem _ member), entries.length, rfl,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.seamWalk_length shared first first rest tail,
          values, rfl, sum, rfl, ?_⟩
      have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.seamWalk_sum shared first first rest
        tail
      change sum = first.value shared + Data.Gaussian.Norm.Sum.Basic.gaussianSum _
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.value_eq_atPoint first shared]
      exact equal.trans (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings.ClosedSeams

end
