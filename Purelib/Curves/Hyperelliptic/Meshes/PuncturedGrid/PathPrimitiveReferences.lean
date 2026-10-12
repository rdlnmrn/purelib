module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Uniform finite bounds on complete retained paths

One coarse reference is retained for every segment occurrence. The cached
profile fixes a common index floor and the sum of squared increment bounds
before later numerical face data are selected. Finite Cauchy--Schwarz pays
the actual number of occurrences, including repeated or reversed segments.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
    {ambient : Rational.Box}

/-- An original coarse primitive reference for each retained assigned segment occurrence and comparison owner. -/
@[expose] def References (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces),
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned → Type 2
  | _, _, _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, _, _, .cons _ remaining, compared =>
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference compared.1.entered 1 ×
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet
          remaining compared.2

namespace References

/-- Prepare the original unit-tolerance reference recursively for every retained segment occurrence. -/
@[expose] def build (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned),
      Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet assigned compared
  | _, _, _, _, _, _, .nil _ _, _ => ⟨⟩
  | _, _, _, _, _, _, .cons _ remaining, compared =>
      ⟨Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.build compared.1.entered 1 (by decide),
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.build differential
          parentSheet remaining compared.2⟩

set_option genInjectivity false in
/-- All scalar totals are folded together once, not once per later request. -/
structure Profile where
  /-- The retained maximum sufficient grid stage of the original segment references. -/ index : Nat
  /-- The exact original assigned segment-occurrence count. -/ count : Nat
  /-- The retained sum of original squared-increment allowances. -/ total :
    Normalization.InverseRootPolynomial.Coordinate

constructive_injectivity Profile

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References
/-- Fold the actual original reference stages, occurrence count and squared-increment allowances once. -/
@[expose] def profile (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned),
      Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet assigned compared →
        Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.Profile
  | _, _, _, _, _, _, .nil _ _, _, _ => ⟨0, 0, 0⟩
  | _, _, _, _, _, _, .cons _ remaining, compared, references =>
      let tail := profile differential parentSheet remaining compared.2 references.2
      ⟨max references.1.budget.grid.index tail.index, tail.count + 1, references.1.bound + tail.total⟩

/-- The retained original profile's total squared-increment allowance is nonnegative. -/
theorem profile_nonnegative (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2)
  :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned)
      (references : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet
        assigned compared),
      0 ≤ (profile differential parentSheet assigned compared references).total
  | _, _, _, _, _, _, .nil _ _, _, _ => le_rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, references =>
      add_nonneg references.1.bound_positive.le
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile_nonnegative
        differential parentSheet remaining compared.2 references.2)

/-- The retained profile count equals the original complete corner-increment list length. -/
theorem profile_count (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat}
      (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned)
      (references : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet
        assigned compared),
      (profile differential parentSheet assigned compared references).count =
        (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned).length
  | _, _, _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, references =>
      congrArg Nat.succ
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile_count differential
        parentSheet shared remaining compared.2 references.2)

/-- At a sufficient shared stage, the original corner squared-norm sum satisfies the retained reference profile total.
-/
theorem normSum_le (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat}
      (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
        parentSheet assigned)
      (_aligned :
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains
        domains differential parentSheet assigned compared)
      (references : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet
        assigned compared),
      (profile differential parentSheet assigned compared references).index ≤ index →
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum
          (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned) ≤
          (profile differential parentSheet assigned compared references).total
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => le_rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, references, later => by
      have firstScalar := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_bounded compared.1
        aligned.1
        references.1 ((Data.Nat.Order.le_max_left _ _).trans later) shared
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      exact Rat.Fraction.Order.Arithmetic.add_le_add_direct firstScalar
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.normSum_le differential
          parentSheet shared remaining compared.2 aligned.2 references.2 ((Data.Nat.Order.le_max_right _ _).trans
          later))

end References

set_option genInjectivity false in
/-- Generated reference banks supply the same checked preparations and
cached totals. There is no condition equating them with `References.build`. -/
structure ReferenceBank (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
    (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
      parentSheet assigned) where
  /-- The exact original coarse references aligned with the retained segment comparisons. -/ references :
    Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References differential parentSheet assigned compared
  /-- The retained stage, count and allowance summary of those original references. -/ profile :
    Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.Profile
  /-- The cached profile equals the exact fold over the retained original reference bank. -/ profile_eq : profile =
    Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile differential parentSheet assigned
    compared references
  /-- The retained squared-norm bound for the complete original path sum. -/ bound :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The bound equals the original occurrence count times the retained allowance total. -/ bound_eq : bound =
    (profile.count : Normalization.InverseRootPolynomial.Coordinate) * profile.total

constructive_injectivity ReferenceBank

namespace ReferenceBank

variable {differential : Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
    Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
    Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
  {assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces} {compared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
    parentSheet assigned}

/-- Cache the profile and count-paid complete-path bound of the supplied original reference bank. -/
@[expose] def ofReferences (references : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References
  differential parentSheet assigned compared) : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank
  differential parentSheet assigned compared :=
  let profile := Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile differential parentSheet
    assigned compared references
  ⟨references, profile, rfl, Rational.Budget.Aggregate.countCoordinate profile.count * profile.total,
    by rw [Rational.Budget.Aggregate.countCoordinate_eq]⟩

/-- Prepare every original segment reference once and cache its complete-path profile and bound. -/
@[expose] def build (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces)
  (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
  parentSheet assigned) :
    Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank differential parentSheet assigned compared
      :=
  Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank.ofReferences
    (Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.build differential parentSheet assigned
    compared)

/-- The original retained reference profile has nonnegative total allowance. -/
theorem total_nonnegative (reference : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank
  differential parentSheet assigned compared) : 0 ≤ reference.profile.total := by
  rw [reference.profile_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile_nonnegative differential
    parentSheet assigned compared reference.references

/-- The complete original corner squared-norm sum is bounded by the cached profile total. -/
theorem normSum_bounded (reference : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank
  differential parentSheet assigned compared)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
      differential parentSheet assigned compared)
    {index : Nat} (later : reference.profile.index ≤ index) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned) ≤
      reference.profile.total := by
  have norms := Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.normSum_le differential
    parentSheet shared assigned compared aligned reference.references
    (reference.profile_eq ▸ later)
  rw [← reference.profile_eq] at norms
  exact norms

/-- The original full corner sum satisfies the retained count-paid path bound at every sufficient shared stage. -/
theorem bounded (reference : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank differential
  parentSheet assigned compared)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
      differential parentSheet assigned compared)
    {index : Nat} (later : reference.profile.index ≤ index) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned)) ≤
      reference.bound := open Purelib.Data.Rat in by
  have norms := reference.normSum_bounded aligned later shared
  have count := Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.References.profile_count differential
    parentSheet shared assigned compared reference.references
  rw [← reference.profile_eq] at count
  have estimate := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned)
  rw [← count, ← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct norms
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans_eq reference.bound_eq.symm)

end ReferenceBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
