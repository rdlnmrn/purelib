module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial.Accuracy
import Purelib.Data.List.DependentProduct
public import Purelib.Data.Fin.Fold.Max
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Polynomial
import Purelib.Polynomial.Geometry.Grid.AxisWalks.Gaussian
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order

/-! # Requests selected before ordinary polynomial fragment observations

One retained original FragmentAccuracy is prepared at each original bounded
fragment. The whole Owner/Entry pair and original endpoint-budget readbacks
later transport those same requests onto the actual numerical leaves.
Computed source and face floors pay the supplied cached comparisons.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets.Word.PolynomialComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Indexed
  (sumFin_eq_gaussianSum sumFin_map normSq_sumFin_sub_le_count_mul_sumFin)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Fin.Fold.Max (maxFin le_maxFin)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (DomainMeshBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus count modelFloor : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target}
variable {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable (entries : FragmentSheets domains request fragments)
variable {differential : OddPowerDifferential curve.polynomial}
variable {points : List Canonical} {index : Nat}
variable (budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains)

/-- The original fragment allocation on one complete retained fragment/Entry pair and supplied P mesh budget. -/
@[expose] def RequestOn {interval : Interval}
    (pair : OccurrencePair (axes := axes) (partition := partition) (domains := domains) (request := request) interval)
    (requested : Rational) :=
  FragmentAccuracy (BankReadings.meshBudget pair.2 budgets).globalBounds
    pair.2.domain.steps pair.2.split.count requested

/-- One actual original allocation per bounded original fragment, before any source or P-bank observation. -/
abbrev Requests (requested : Rational) :=
  DependentProduct partition.intervals fun position => RequestOn budgets (entries.at position) requested

/-- Prepare each original scalar allocation once from its actual geometry, piece count and P-specific majorants. -/
def prepareRequests (requested : Rational) (positive : 0 < requested) : Requests entries budgets requested :=
  DependentProduct.ofFn partition.intervals fun position =>
    let pair := entries.at position
    FragmentAccuracy.build (BankReadings.meshBudget pair.2 budgets).globalBounds
      pair.2.domain.steps pair.2.split.count requested positive

variable {entries budgets} {requested : Rational} (allocated : Requests entries budgets requested)

/-- Read the SAME original allocation at one original bounded occurrence. -/
@[expose] def requestAt (position : Fin partition.intervals.length) :
    RequestOn budgets (entries.at position) requested :=
  DependentProduct.get partition.intervals allocated position

/-- The finite source-model floor reads only the already retained allocations. -/
@[expose] def sourceFloor : Nat :=
  maxFin partition.intervals.length fun position => (requestAt allocated position).minimumIndex

/-- The finite numerical face floor reads only the already retained allocations. -/
@[expose] def faceFloor : Nat :=
  maxFin partition.intervals.length fun position => (requestAt allocated position).grid.index

/-- Every actual source requirement is below the same retained finite maximum. -/
theorem source_le (position : Fin partition.intervals.length) :
    (requestAt allocated position).minimumIndex ≤ sourceFloor allocated :=
  le_maxFin (fun position => (requestAt allocated position).minimumIndex) position

/-- Every actual grid requirement is below the same retained finite maximum. -/
theorem face_le (position : Fin partition.intervals.length) :
    (requestAt allocated position).grid.index ≤ faceFloor allocated :=
  le_maxFin (fun position => (requestAt allocated position).grid.index) position

/-- Transport the actual original request through equality of the whole fragment/Entry pair. -/
private def onPair {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition) (domains := domains)
      (request := request) interval}
    (same : first = last) (allocated : RequestOn budgets first requested) :
    RequestOn budgets last requested := by
  cases same
  exact allocated

/-- Whole-pair transport preserves the actual selected source floor. -/
private theorem onPair_minimum {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition) (domains := domains)
      (request := request) interval}
    (same : first = last) (allocated : RequestOn budgets first requested) :
    (onPair (budgets := budgets) same allocated).minimumIndex = allocated.minimumIndex := by
  cases same
  rfl

/-- Whole-pair transport preserves the actual selected face floor. -/
private theorem onPair_index {interval : Interval}
    {first last : OccurrencePair (axes := axes) (partition := partition) (domains := domains)
      (request := request) interval}
    (same : first = last) (allocated : RequestOn budgets first requested) :
    (onPair (budgets := budgets) same allocated).grid.index = allocated.grid.index := by
  cases same
  rfl

section BoundsTransport

variable {interval : Interval} {fragment : RegularFaces.RegularPrimitiveFragment axes parent partition interval}
variable {first last : PrimitiveOverlapBounds fragment.face.located.face.clearance
  (differential.numerator.scale differential.scale)} {columns pieces : Nat}

/-- Reindex the SAME original allocation along its actual retained bound-owner equality. -/
private def onBounds (same : first = last) (allocated : FragmentAccuracy first columns pieces requested) :
    FragmentAccuracy last columns pieces requested := by
  cases same
  exact allocated

/-- Bound-owner equality changes no source selection. -/
private theorem onBounds_minimum (same : first = last)
    (allocated : FragmentAccuracy first columns pieces requested) :
    (onBounds (fragment := fragment) same allocated).minimumIndex = allocated.minimumIndex := by
  cases same
  rfl

/-- Bound-owner equality changes no actual grid selection. -/
private theorem onBounds_index (same : first = last)
    (allocated : FragmentAccuracy first columns pieces requested) :
    (onBounds (fragment := fragment) same allocated).grid.index = allocated.grid.index := by
  cases same
  rfl

end BoundsTransport

variable {sourceBounds : UniformBounds (request.patch.neighborhood count)}
variable {allowance : Rational} {positive : 0 < allowance}
variable {uniform : UniformRequest sourceBounds 0 (differential.numerator.scale differential.scale)
  modelFloor (allowance / 4)}
variable {first last : Canonical} {coordinate : Spatial.Coordinate first last}
variable (model : PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive)
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable {shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics}
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points}
variable (kept : Word shared entries included)

/-- The SAME original allocation pays the actual retained comparison at its original bounded leaf.

The whole leaf pair identity and original endpoint-budget getter transport
that allocation. Neither a numerical scalar equality nor an index equality
identifies either record. No comparison, query, Finish or model is replayed.
-/
theorem fragment_bound_lt (comparisons : Leaves model kept)
    (sourceLater : sourceFloor allocated ≤ modelFloor) (faceLater : faceFloor allocated ≤ index)
    (position : Fin partition.intervals.length) :
    (comparisonAt model kept comparisons position).comparison.bound < requested := by
  let leaf := leafAt shared entries kept.leaves position
  let selected : RequestOn budgets (entries.at position) requested := requestAt allocated position
  let actual : RequestOn budgets leaf.pair requested := onPair (budgets := budgets) leaf.pair_eq.symm selected
  have sourcePaid : actual.minimumIndex ≤ modelFloor :=
    (onPair_minimum (budgets := budgets) leaf.pair_eq.symm selected).trans_le
      ((source_le allocated position).trans sourceLater)
  have facePaid : actual.grid.index ≤ index :=
    (onPair_index (budgets := budgets) leaf.pair_eq.symm selected).trans_le
      ((face_le allocated position).trans faceLater)
  have boundEq := congrArg
    (fun budget : DomainMeshBudget leaf.pair.2.domain source points tolerance
      (numerator := differential.numerator.scale differential.scale) => budget.globalBounds)
    (EndpointReadings.budget_eq leaf.occurrence.view)
  let viewed : FragmentAccuracy (EndpointReadings.budget leaf.occurrence.view).globalBounds
      leaf.pair.2.domain.steps leaf.pair.2.split.count requested :=
    onBounds (fragment := leaf.pair.1) boundEq.symm actual
  have sourceView : viewed.minimumIndex ≤ modelFloor :=
    (onBounds_minimum (fragment := leaf.pair.1) boundEq.symm actual).trans_le sourcePaid
  have faceView : viewed.grid.index ≤ index :=
    (onBounds_index (fragment := leaf.pair.1) boundEq.symm actual).trans_le facePaid
  exact PolynomialModelComparison.endpoint_bound_lt (comparisonAt model kept comparisons position)
    viewed sourceView faceView

/-- Summing the actual leaf charges preserves one copy of the literal fragment count.

The global word performs one Cauchy estimate later. This sum introduces no
parent multiplier and still charges stationary and repeated occurrences.
-/
theorem chargeSum_le (comparisons : Leaves model kept)
    (sourceLater : sourceFloor allocated ≤ modelFloor) (faceLater : faceFloor allocated ≤ index) :
    chargeSum model kept comparisons ≤ (partition.intervals.length : Rational) * requested := by
  exact (Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget.sumFin_le
    (fun position => (fragment_bound_lt allocated model kept comparisons sourceLater faceLater position).le)).trans_eq
      (Purelib.Algebra.FiniteSum.Fin.Rational.sum_constant partition.intervals.length requested)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets.Word.PolynomialComparison
