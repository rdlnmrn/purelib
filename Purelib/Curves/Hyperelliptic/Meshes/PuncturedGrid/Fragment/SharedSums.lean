module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Whole original-request sums from shared face meshes

The dependent spines retain every original fragment occurrence. Execution
folds cached shared values and charges; the unchanged request polynomials
occur only in the erased error proof and exact splitting telescope.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {count : Nat} {target : Fraction.Rational} {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
    {index : Nat}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}

namespace RegularPrimitiveFragments.SheetEntries

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming FragmentSheets -> SheetEntries

variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {partition :
  Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : Readings.UniformPreparedRequests.LocalRequest parent count target}

set_option genInjectivity false in
/-- Dependent original fragment readings from one retained shared face-mesh bank.

The spine stores each fragment reading at its original cell and request.
The same shared numerical bank supplies the head and every retained tail. -/
inductive BankReadings (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  :
    {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} → {fragments :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals} →
      FragmentSheets domains request
        fragments → Type
  /-- The exact empty original fragment reading bank. -/ | nil :
    BankReadings
    shared .nil
  /-- Prepend the actual retained original fragment readings to their dependent tail. -/ | cons {interval :
    Rectangle.Partition.PreparedAxisPartitions.Interval} {intervals : List
    Rectangle.Partition.PreparedAxisPartitions.Interval}
      {head : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes parent partition
        interval} {tail : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent
        partition intervals}
      {entry : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry head domains
        request} {entries :
        FragmentSheets domains request
        tail}
      (first : Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.BankReading entry shared) (remaining :
        BankReadings
        shared entries) :

        BankReadings
        shared (.cons entry entries)

constructive_injectivity BankReadings

namespace BankReadings

variable {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics}

/-- Read every original fragment occurrence from the shared bank using the retained point-containment certificate. -/
@[expose] def build (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∀ {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition
      intervals}
      (entries : FragmentSheets domains
        request fragments), (∀ point ∈
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveFragments.SheetEntries.points entries),
        point ∈ points) →
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings
        shared entries
  | _, _, .nil, _ => .nil
  | _, _, .cons first rest, included =>
      .cons (Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.BankReading.build first shared
        (fun point member => included point (List.mem_append_left _ member)))

          (build
          shared rest (fun point member => included point (List.mem_append_right _ member)))

open
  SheetEntries.BankReadings
  in
/-- Read the ordered original fragment comparison values from their actual caches. -/
@[expose] def values : ∀ {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains
      request fragments},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
      entries → List Gaussian.Basic.Canonical
  | _, _, _, .nil => []
  | _, _, _, .cons first rest => first.value :: values rest

/-- Sum the retained original fragment comparison allowances. -/
@[expose] def chargeSum : ∀ {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains
      request fragments},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
      entries → Fraction.Rational
  | _, _, _, .nil => 0
  | _, _, _, .cons first rest => first.bound +
    chargeSum
    rest

/-- Read the original cached-minus-request-polynomial increment errors along the retained fragment spine. -/
@[expose] def errors : ∀ {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains
      request fragments},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
      entries → List Gaussian.Basic.Canonical
  | _, _, _, .nil => []
  | _, _, _, .cons (head := head) first rest =>
      (first.value - (request.request.model.primitive.value.eval head.located.last -
        request.request.model.primitive.value.eval head.located.first)) ::
          errors
          rest

variable {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
  {entries : FragmentSheets domains
    request fragments}

/-- The retained value list has the exact original total fragment occurrence count. -/
theorem values_length (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
  entries) : readings.values.length = intervals.length := by
  induction readings with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

/-- The retained error list has the exact original total fragment occurrence count. -/
theorem errors_length (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
  entries) : readings.errors.length = intervals.length := by
  induction readings with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

open
  SheetEntries.BankReadings
  in
/-- The sum of original fragment errors equals the cached reading sum minus the original split-polynomial increment sum.
-/
theorem errors_sum (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
  entries) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.errors = Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.values
      - Data.Gaussian.Norm.Sum.Basic.gaussianSum (intervals.map fun interval =>
      request.request.model.primitive.value.eval (parent.edge.point interval.upper) -
        request.request.model.primitive.value.eval (parent.edge.point interval.lower)) := by
  induction readings with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
      simp only
        [errors,
        values, Data.Gaussian.Norm.Sum.Basic.gaussianSum, List.map_cons,
        Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell.first_eq,
        Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell.last_eq, ih]
      ring1

/-- The squared-norm sum of original fragment errors is bounded by the retained charge sum. -/
theorem errors_bounded (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings shared
  entries) : Gaussian.Norm.Sum.Basic.gaussianNormSqSum readings.errors ≤ readings.chargeSum := by
  induction readings with
  | nil => exact le_rfl
  | cons first rest ih =>
      have firstScalar := first.accurate
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      exact Fraction.Order.Arithmetic.add_le_add_direct firstScalar ih

end BankReadings
end RegularPrimitiveFragments.SheetEntries

namespace RegularPrimitiveSplits.SheetEntries

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries

set_option genInjectivity false in
/-- Dependent original parent-fragment readings from one retained shared face-mesh bank.

Each parent occurrence retains its full fragment-reading spine, followed
by the original parent tail. The bank and dependent split indices are shared. -/
inductive BankReadings (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} → {splits :
      Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents} →
      {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
        splits} → {requests : Readings.UniformPreparedRequests.RequestedParents count target parents} →
      SheetEntries domains fragments requests → Type 2
  /-- The exact empty original parent-fragment reading bank. -/ | nil :
    BankReadings
    shared .nil
  /-- Prepend the actual retained original parent-fragment readings to their dependent tail. -/ | cons {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
      {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)} {splits :
        Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      {head : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragments axes parent partition
        partition.intervals} {tail : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits
        (base := base) axes splits}
      {request : Readings.UniformPreparedRequests.LocalRequest parent count target} {requests :
        Readings.UniformPreparedRequests.RequestedParents count target parents}
      {first : FragmentSheets domains
        request head} {rest : SheetEntries domains tail requests}
      (headReadings :
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries.BankReadings
        shared first) (tailReadings :
        BankReadings
        shared rest) :

        BankReadings
        shared (.cons first rest)

constructive_injectivity BankReadings

namespace BankReadings

variable {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics}

/-- Read every original parent-fragment occurrence from the shared bank using the retained point-containment
certificate. -/
@[expose] def build (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
      Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
        splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
      (entries : SheetEntries domains fragments requests), (∀ point ∈
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries),
        point ∈ points) →
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
        entries
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons first rest, included =>
      .cons
        (RegularPrimitiveFragments.SheetEntries.BankReadings.build
        shared first
        (fun point member => included point (List.mem_append_left _ member)))

          (build
          shared rest (fun point member => included point (List.mem_append_right _ member)))

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings
  in
/-- Read the ordered original parent-fragment comparison values from their actual caches. -/
@[expose] def values : ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
      entries → List Gaussian.Basic.Canonical
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons first rest => first.values ++ values rest

/-- Sum the retained original parent-fragment comparison allowances. -/
@[expose] def chargeSum : ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
  {splits : Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
      entries → Fraction.Rational
  | _, _, _, _, _, .nil => 0
  | _, _, _, _, _, .cons first rest => first.chargeSum +
    chargeSum
    rest

/-- Read the original cached-minus-request-polynomial increment errors along the retained parent-fragment spine. -/
private def errors : ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests},
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
      entries → List Gaussian.Basic.Canonical
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons first rest => first.errors ++
    errors
    rest

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
  {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
    splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
  {entries : SheetEntries domains fragments requests}

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings
  in
/-- The retained value list has the exact original total parent-fragment occurrence count. -/
theorem values_length (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
  entries) : readings.values.length = splits.count := by
  induction readings with
  | nil => rfl
  | cons first rest ih =>
    rw [values, Data.List.Append.length_append, first.values_length, ih]; exact congrArg (· + _)
      (Geometry.Rectangle.AxisPartition.count_eq _).symm

/-- The retained error list has the exact original total parent-fragment occurrence count. -/
private theorem errors_length (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
  entries) : readings.errors.length = splits.count := by
  induction readings with
  | nil => rfl
  | cons first rest ih =>
    rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings.errors,
      Data.List.Append.length_append, first.errors_length, ih]; exact congrArg (· + _)
      (Geometry.Rectangle.AxisPartition.count_eq _).symm

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings
  in
/-- The sum of original parent-fragment errors equals the cached reading sum minus the original split-polynomial
increment sum. -/
private theorem errors_sum (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
  entries) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.errors = Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.values
      - Data.Gaussian.Norm.Sum.Basic.gaussianSum (splits.increments requests) := by
  induction readings with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
      rw
        [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings.errors,
        values, Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits.increments,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum_append,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum_append, first.errors_sum, ih]
      ring1

/-- The squared-norm sum of original parent-fragment errors is bounded by the retained charge sum. -/
private theorem errors_bounded (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
  entries) : Gaussian.Norm.Sum.Basic.gaussianNormSqSum readings.errors ≤ readings.chargeSum := by
  induction readings with
  | nil => exact le_rfl
  | cons first rest ih =>
    rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings.errors,
      Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum_append]; exact add_le_add first.errors_bounded ih

/-- Every original grid-fragment charge is paid after its own complete
analytic-cell count. No original request polynomial is evaluated by the fold. -/
theorem accurate (readings :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
  entries) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.values -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments) ≤ Rational.Budget.Aggregate.countCoordinate
      splits.count * readings.chargeSum := by
  rw [← splits.sum_eq requests, ← readings.errors_sum, Rational.Budget.Aggregate.countCoordinate_eq]
  have bound := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le readings.errors
  rw [readings.errors_length] at bound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct readings.errors_bounded
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

end BankReadings

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveSplits axes parents}
  {fragments : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveSplits (base := base) axes
    splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
  {entries : SheetEntries domains fragments requests} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics}

set_option genInjectivity false in
/-- The complete original requested-parent reading fold from one retained shared numerical bank.

Cache the actual fragment values, count, sum and aggregate charge with their exact readback identities. -/
structure SharedSum (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  (entries : SheetEntries domains fragments requests) where
  /-- The actual dependent original fragment readings aligned with every retained parent request. -/ readings :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings shared
    entries
  /-- The ordered cached original fragment values. -/ values : List Gaussian.Basic.Canonical
  /-- The retained value list equals the exact original reading-bank projection. -/ values_eq : values = readings.values
  /-- The actual original total fragment-occurrence count. -/ fragmentCount : Nat
  /-- The cached fragment count equals the original split-bank count. -/ fragmentCount_eq : fragmentCount = splits.count
  /-- The retained finite sum of all actual original fragment values. -/ value : Gaussian.Basic.Canonical
  /-- The cached value equals the exact sum of its retained original list. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The retained sum of all original local comparison charges. -/ chargeSum : Fraction.Rational
  /-- The cached charge equals the exact original reading-bank charge fold. -/ chargeSum_eq : chargeSum =
    readings.chargeSum
  /-- The original complete-sum squared-norm error allowance. -/ bound : Fraction.Rational
  /-- The bound equals the original fragment count times the retained local charge sum. -/ bound_eq : bound =
    Rational.Budget.Aggregate.countCoordinate fragmentCount * chargeSum
  /-- The cached original sum differs from the original request increment sum within its retained allowance. -/ accurate
    : Data.Gaussian.Norm.Basic.normSq (value - Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments) ≤ bound

constructive_injectivity SharedSum

/-- Acquire all original fragment readings from the retained shared bank and cache the complete finite sum and paid
error bound. -/
@[expose] def SharedSum.build (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets
  numerics) (entries : SheetEntries domains fragments requests)
    (included : ∀ point ∈
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries), point
      ∈ points) : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum
      shared entries :=
  let readings :=
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.BankReadings.build shared
    entries included
  let values := readings.values
  let count := splits.count
  let charge := readings.chargeSum
  ⟨readings, values, rfl, count, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum values, rfl, charge, rfl,
    Rational.Budget.Aggregate.countCoordinate count * charge, rfl, readings.accurate⟩

end RegularPrimitiveSplits.SheetEntries
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

end
