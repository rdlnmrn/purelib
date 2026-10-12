module
import Purelib.Data.Fin
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
public import Purelib.Topology.Surface.Sewing.CutIntersection
public import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm

public section

/-!
# The computed intersection table of the actual standard tours

Cache the actual standard period rows, their root-backed tours, boundary rows and integral spans,
then compute the three independent blocks of their cut-crossing form.
Checking the expected symplectic table returns either all entry proofs or
the exact offending block, row and column. A rejected table is a statement
about these tours, not about the curve's ability to admit a period basis.
-/

section

open Purelib.Curves
open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.Riemann

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

set_option genInjectivity false in
/-- A retained standard period row with its actual tour geometry and integral span.

The period identity and source equality bind every coordinate to the original canonical row. -/
structure IntersectionRow (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) (index :
      Fin genus) where
  /-- The actual retained original standard period row. -/ period :
    Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve
  /-- The retained row equals the original canonical period row. -/ period_eq : period =
    (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches).rows index
  /-- The original A/B tour pair with its retained lifted geometry. -/ pair :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index
  /-- The geometric pair uses exactly the retained period row's tours. -/ source_eq : pair.source = period.tours
  /-- The boundary coordinates of the actual original tour pair. -/ coordinates :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair
  /-- The integral span of the retained coordinates in the original cut pairing. -/ span :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning coordinates integral

constructive_injectivity IntersectionRow

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow

/-- Attach geometry to the supplied standard period row, without preparing
its tours, initial owners, or integration states again. -/
@[expose] def ofPeriod (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw)
    (index : Fin genus) (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
    (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
      branches).rows index) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted integral index :=
  let sourceEq : period.tours = Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData curve branches index
    := by
    rw [periodEq, Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData_row]
    rfl
  let pair := Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource lifted index
    period.tours sourceEq
  let coordinates := Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates.build pair
  ⟨period, periodEq, pair, rfl, coordinates, Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.spanningWith
    coordinates integral normal⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

set_option genInjectivity false in
/-- The three intersection blocks of the retained original standard tours.

Cache the actual dependent rows and exact A–A, A–B and B–B integer pairings. -/
structure IntersectionBank (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) where
  /-- The actual dependent original period rows with their integral spans. -/ rows : Data.Vector.DependentVector (fun
    index : Fin genus => Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted integral
    index)
  /-- The cached original A–A integer intersection block. -/ aa : SquareMatrix Int genus
  /-- The cached original A–B integer intersection block. -/ ab : SquareMatrix Int genus
  /-- The cached original B–B integer intersection block. -/ bb : SquareMatrix Int genus
  /-- Every A–A entry equals the pairing of the retained original row spans. -/ aa_eq : ∀ first last, aa first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).span.a (rows.get last).span.a
  /-- Every A–B entry equals the pairing of the retained original row spans. -/ ab_eq : ∀ first last, ab first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).span.a (rows.get last).span.b
  /-- Every B–B entry equals the pairing of the retained original row spans. -/ bb_eq : ∀ first last, bb first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).span.b (rows.get last).span.b

constructive_injectivity IntersectionBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

variable {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank

/-- Existing cached tours and spans can be consumed without rebuilding
their geometry or normal form. Only the displayed table is materialized. -/
@[expose] def ofRows (rows : Data.Vector.DependentVector (fun index : Fin genus =>
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted integral index)) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral :=
  ⟨rows,
    SquareMatrix.matrixOfFn (fun first last =>
      Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
      first).span.a (rows.get last).span.a),
    SquareMatrix.matrixOfFn (fun first last =>
      Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
      first).span.a (rows.get last).span.b),
    SquareMatrix.matrixOfFn (fun first last =>
      Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
      first).span.b (rows.get last).span.b),
    SquareMatrix.matrixOfFn_apply _, SquareMatrix.matrixOfFn_apply _, SquareMatrix.matrixOfFn_apply _⟩

/-- A numerical consumer can supply its already retained canonical bank.
All geometric rows consume that same finite vector. -/
@[expose] def ofPeriods (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw)
    (periods : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank curve)
    (canonical : ∀ index, periods.rows index =
      (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches).rows index)
      :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.ofRows (Data.Vector.DependentVector.ofFn
    (fun index => Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral
    normal index (periods.rows index) (canonical index)))

/-- Prepare the original canonical period bank once and attach the supplied integral normal form. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral :=
  let periods := Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.ofPeriods lifted integral normal periods
    (fun _ => rfl)

/-- Build the actual standard intersection table using the retained cut pairing's computed normal form. -/
@[expose] def automatic (lifted : Meshes.LiftedPuncturedGrid base) :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted lifted.cutIntegralPairing :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.build lifted lifted.cutIntegralPairing
    (Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordNormalForm lifted.cutIntegralPairing).normal

/-- The original A–A intersection block is skew-symmetric. -/
theorem aa_skew (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral)
  (first last : Fin genus) :
    bank.aa first last = -bank.aa last first := by
  rw [bank.aa_eq, bank.aa_eq]
  exact Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_skew
    (bank.rows.get first).span.a (bank.rows.get last).span.a

/-- The original B–B intersection block is skew-symmetric. -/
theorem bb_skew (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral)
  (first last : Fin genus) :
    bank.bb first last = -bank.bb last first := by
  rw [bank.bb_eq, bank.bb_eq]
  exact Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_skew
    (bank.rows.get first).span.b (bank.rows.get last).span.b

/-- Each original A tour has zero self-intersection. -/
theorem aa_diagonal (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) (index : Fin genus) : bank.aa index index = 0 := by
  rw [bank.aa_eq]
  exact
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_diagonal
    (bank.rows.get index).span.a

/-- Each original B tour has zero self-intersection. -/
theorem bb_diagonal (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) (index : Fin genus) : bank.bb index index = 0 := by
  rw [bank.bb_eq]
  exact
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_diagonal
    (bank.rows.get index).span.b

/-- The retained A–A and B–B blocks vanish and the original A–B block is the identity. -/
structure SymplecticTable (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) : Prop where
  /-- Every retained A–A entry is zero. -/ aa_zero : ∀ first last, bank.aa first last = 0
  /-- The retained A–B entries form the exact identity matrix. -/ ab_identity : ∀ first last, bank.ab first last = if
    first = last then 1 else 0
  /-- Every retained B–B entry is zero. -/ bb_zero : ∀ first last, bank.bb first last = 0

set_option genInjectivity false in
/-- An actual offending block entry of the retained intersection table, with its proved inequality. -/
inductive InvalidTable (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) where
  /-- An actual nonzero A–A entry of the retained table. -/ | aa (first last : Fin genus) (different : bank.aa first
    last ≠ 0)
  /-- An actual A–B entry differing from the required identity entry. -/ | ab (first last : Fin genus) (different :
    bank.ab first last ≠ if first = last then 1 else 0)
  /-- An actual nonzero B–B entry of the retained table. -/ | bb (first last : Fin genus) (different : bank.bb first
    last ≠ 0)

constructive_injectivity InvalidTable

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.InvalidTable

/-- A retained offending entry rules out the symplectic identity for this exact table. -/
theorem not_symplectic {bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral} (invalid : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.InvalidTable bank)
  :
    ¬ Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.SymplecticTable bank := by
  intro table
  cases invalid with
  | aa first last different => exact different (table.aa_zero first last)
  | ab first last different => exact different (table.ab_identity first last)
  | bb first last different => exact different (table.bb_zero first last)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.InvalidTable

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank

set_option genInjectivity false in
/-- Either the complete symplectic certificate or an actual offending entry of the retained table. -/
inductive Check (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted integral)
  where
  /-- The complete symplectic identity for the retained original table. -/ | valid (table :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.SymplecticTable bank)
  /-- An actual offending entry of the retained original table. -/ | invalid (obstruction :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.InvalidTable bank)

constructive_injectivity Check

set_option genInjectivity false in
/-- Either all instances of a finite predicate or an explicit index with a proved failure. -/
inductive FiniteCheck {size : Nat} (predicate : Fin size → Prop) where
  /-- A proof of the predicate at every original finite index. -/ | valid (checked : ∀ index, predicate index)
  /-- An actual original finite index with a proof that the predicate fails. -/ | invalid (index : Fin size) (different
    : ¬ predicate index)

constructive_injectivity FiniteCheck

/-- Check every finite index constructively, returning the first encountered failed predicate with its proof. -/
@[expose] def checkFinite : {size : Nat} → (predicate : Fin size → Prop) → [DecidablePred predicate] →
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.FiniteCheck predicate
  | 0, _, _ => .valid (fun index => Fin.elim0 index)
  | _ + 1, predicate, _ =>
      if head : predicate 0 then
        match Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkFinite
          (fun index => predicate index.succ) with
        | .valid tail => .valid (Data.Fin.casesDependent head tail)
        | .invalid index different => .invalid index.succ different
      else .invalid 0 head

set_option genInjectivity false in
/-- Either entrywise equality of two finite integer arrays or an explicit unequal entry. -/
inductive EntryCheck {rows columns : Nat} (left right : Fin rows → Fin columns → Int) where
  /-- Equality at every entry of the two original finite arrays. -/ | valid (checked : ∀ row column, left row column =
    right row column)
  /-- An actual original row and column with proved unequal values. -/ | invalid (row : Fin rows) (column : Fin columns)
    (different : left row column ≠ right row column)

constructive_injectivity EntryCheck

/-- Compare the original finite arrays in row order, retaining the exact first encountered unequal entry. -/
@[expose] def checkEntries {columns : Nat} : {rows : Nat} →
    (left right : Fin rows → Fin columns → Int) →
      Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.EntryCheck left right
  | 0, _, _ => .valid (fun row => Fin.elim0 row)
  | _ + 1, left, right =>
      match Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkFinite (fun column =>
        left 0 column = right 0 column) with
      | .invalid column different => .invalid 0 column different
      | .valid head =>
          match
            Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkEntries
            (fun row => left row.succ) (fun row => right row.succ) with
          | .valid tail => .valid (Data.Fin.casesDependent head tail)
          | .invalid row column different => .invalid row.succ column different

/-- Exhaustive checking of the retained table, with no inconclusive case.
Failure carries the actual offending entry and its proved inequality. -/
@[expose] def check (bank : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank lifted
  integral) : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.Check bank :=
  match Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkEntries (fun row column =>
    bank.aa row column) (fun _ _ => 0) with
  | .invalid row column different => .invalid (.aa row column different)
  | .valid aa =>
      match Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkEntries (fun row column
        => bank.ab row column) (fun row column => if row = column then 1 else 0) with
      | .invalid row column different => .invalid (.ab row column different)
      | .valid ab =>
          match Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.checkEntries (fun row
            column => bank.bb row column) (fun _ _ => 0) with
          | .invalid row column different => .invalid (.bb row column different)
          | .valid bb => .valid ⟨aa, ab, bb⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank

end
