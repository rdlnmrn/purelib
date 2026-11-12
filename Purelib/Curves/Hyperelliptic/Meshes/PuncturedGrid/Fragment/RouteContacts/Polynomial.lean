module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.Readings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.Polynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Genuine P comparison on one old-left and actual routed endpoint view

The given raw contact and its P requests remain unchanged. Whole sheet and
domain certificates transport the actual cached numerical inputs, and one
original common-model comparison pays the two retained partial increments.
No primitive bank, query, contact geometry or left endpoint view is rebuilt.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
  (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

universe u

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree}

section MatchedDomains

variable {bank : BranchCellBank curve branches higher} {frames : RootFrames bank.grid}
    {firstFace lastFace : RegularFace bank} {firstModels : FaceModels frames firstFace}
    {lastModels : FaceModels frames lastFace} {start finish : Canonical}
    {owner : Owner (curve.polynomial.eval start)} {ambient : Geometry.Rational.Box}
    {path : ClearPath curve.polynomial ambient start finish} {prepared : CoveredTracedPath path owner}
    {basis : Differential genus} {parentSheet : Fin 2}
    {first : EnteredPath firstModels prepared basis parentSheet}
    {last : EnteredPath lastModels prepared basis parentSheet}
    {ordinary : Ordinary curve.polynomial} {allowance : Rational} {positive : 0 < allowance}
    {requested : ContactBudget.PolynomialPreparation first last ordinary.val allowance positive}
    {index : Nat} {leftSheet rightSheet : Fin 2}
    {leftDomain : PeriodDomain firstModels leftSheet} {rightDomain : PeriodDomain lastModels rightSheet}
    {leftActual : DomainPrimitives leftDomain basis index (numerator := ordinary.numerator)}
    {rightActual : DomainPrimitives rightDomain basis index (numerator := ordinary.numerator)}
    {point : Fin 2 → Canonical}
    {leftPoints : PointReadings leftActual.anchors leftActual.offsets point}
    {rightPoints : PointReadings rightActual.anchors rightActual.offsets point}

/-- The exact result continuation keeps both whole numerical transports and the single original comparison factory. -/
private abbrev MatchedConsumer (Result : Type u) :=
  (left : {value : DomainPrimitives first.domain basis index (numerator := ordinary.numerator) //
    HEq value leftActual}) →
  (right : {value : DomainPrimitives last.domain basis index (numerator := ordinary.numerator) //
    HEq value rightActual}) →
  {value : ContactBudget.PolynomialComparison requested left.val right.val //
    value = ContactBudget.comparePolynomial (owner := owner) (prepared := prepared) requested left.val right.val} →
  (value : Canonical) →
  value = ((leftPoints.values 1 - leftPoints.values 0) - (rightPoints.values 1 - rightPoints.values 0)) →
  normSq value < allowance → Result

/-- Transport the actual original data and point readings through genuine sheet/domain identities, then compare once. -/
private def withMatchedDomains
    (leftSheetEq : first.entry.sheet = leftSheet) (rightSheetEq : last.entry.sheet = rightSheet)
    (leftDomainEq : HEq first.domain leftDomain) (rightDomainEq : HEq last.domain rightDomain)
    (firstEq : point 0 = start) (lastEq : point 1 = finish)
    (later : requested.budget.index ≤ index) {Result : Type u}
    (consume : MatchedConsumer (first := first) (last := last) (requested := requested)
      (leftActual := leftActual) (rightActual := rightActual)
      (leftPoints := leftPoints) (rightPoints := rightPoints) Result) : Result := by
  cases leftSheetEq
  cases rightSheetEq
  cases eq_of_heq leftDomainEq
  cases eq_of_heq rightDomainEq
  let left : {value : DomainPrimitives first.domain basis index (numerator := ordinary.numerator) //
      HEq value leftActual} := ⟨leftActual, HEq.rfl⟩
  let right : {value : DomainPrimitives last.domain basis index (numerator := ordinary.numerator) //
      HEq value rightActual} := ⟨rightActual, HEq.rfl⟩
  let compared : {value : ContactBudget.PolynomialComparison requested left.val right.val //
      value = ContactBudget.comparePolynomial (owner := owner) (prepared := prepared) requested left.val right.val} :=
    ⟨ContactBudget.comparePolynomial (owner := owner) (prepared := prepared) requested left.val right.val, rfl⟩
  let value := (leftPoints.values 1 - leftPoints.values 0) - (rightPoints.values 1 - rightPoints.values 0)
  have bounded : normSq value < allowance :=
    ContactBudget.PolynomialComparison.points_accurate
      (first := first) (last := last) (retained := requested) (later := later) compared.val
      leftPoints rightPoints 0 1 0 1 firstEq lastEq firstEq lastEq
  exact consume left right compared value rfl bounded

end MatchedDomains

variable {count : Nat} {base : FramedPuncturedGrid curve branches higher}
    {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
    {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
    {domains : FaceDomainBank frames base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
    {target tolerance allowance : Rational} {points : List Canonical} {index : Nat}
    {ordinary : Ordinary curve.polynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := ordinary.numerator) domains}
    {shared : FaceSharedMeshes budgets numerics}
    {piece : LiftedFragment axes domains mesh source count target}
    {location : EdgeRoute mesh piece.occurrence.side.edge}
    {included : ∀ value ∈ piece.assigned.split.points, value ∈ points}
    (contact : RouteContact piece location) (requested : Budget contact allowance (some ordinary))
    (originalLeft : EndpointReadings.Cache piece.assigned shared included)

/-- Actual P request, old-left/new-right endpoint caches, whole input data transports and one paid common comparison.

The left view is the supplied object. The right view is genuinely new
numerical lookup work on the same primitive/shared bank. The original
contact's actual sheet/domain certificates align those caches with its two
existing entries; no root relation is inferred from the endpoint coordinates.
-/
@[expose] def PointComparison : Type _ :=
  {inputs : RouteContact piece location × Budget contact allowance (some ordinary) //
    inputs = (contact, requested) ∧ Budget.index requested ≤ index} ×
  (Σ endpoints : {value : EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft //
    value = EndpointView.build (ordinary := ordinary) (piece := piece) (location := location) originalLeft},
  Σ left : {value : DomainPrimitives contact.left.domain source index (numerator := ordinary.numerator) //
    HEq value (EndpointReadings.data endpoints.val.leftView)},
  Σ right : {value : DomainPrimitives contact.right.domain source index (numerator := ordinary.numerator) //
    HEq value endpoints.val.data},
  Σ _ : {value : ContactBudget.PolynomialComparison requested.2 left.val right.val //
    value = ContactBudget.comparePolynomial (owner := contact.owner) (prepared := contact.prepared)
      requested.2 left.val right.val},
  {value : Canonical // value = piece.value shared - routeValue piece location shared ∧ normSq value < allowance})

/-- Build one actual P contact comparison from the supplied left cache and the same-bank right endpoint view.

Only the right numerical endpoint view and the original common comparison
are constructed. Explicit cached Owner/prepared inputs and whole sheet/domain
transports preserve the given physical/query/entry lineage. The supplied P
request retains its independent source and face floors, and the given bank
stage pays its actual selected index.
-/
def comparePoints (later : Budget.index requested ≤ index) : PointComparison contact requested originalLeft :=
  let inputs : {value : RouteContact piece location × Budget contact allowance (some ordinary) //
      value = (contact, requested) ∧ Budget.index requested ≤ index} := ⟨(contact, requested), rfl, later⟩
  let endpoints : {value : EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft //
      value = EndpointView.build (ordinary := ordinary) (piece := piece) (location := location) originalLeft} :=
    ⟨EndpointView.build (ordinary := ordinary) (piece := piece) (location := location) originalLeft, rfl⟩
  have paid : requested.2.budget.index ≤ index :=
    Eq.mp (congrArg (fun value : Nat => value ≤ index) (Budget.index_some requested)) later
  withMatchedDomains (owner := contact.owner) (prepared := contact.prepared)
    (first := contact.left) (last := contact.right) (ordinary := ordinary) (requested := requested.2)
    (leftDomain := piece.assigned.domain) (rightDomain := (domains.atRoute location).domain location.sheet)
    (leftActual := EndpointReadings.data endpoints.val.leftView) (rightActual := endpoints.val.data)
    (leftPoints := EndpointReadings.reading endpoints.val.leftView) (rightPoints := endpoints.val.reading)
    contact.left_sheet contact.right_sheet contact.left_domain contact.right_domain rfl rfl paid
    (fun left right compared value valueEq bounded => by
      have leftEq : (EndpointReadings.reading endpoints.val.leftView).values 1 -
          (EndpointReadings.reading endpoints.val.leftView).values 0 = piece.value shared :=
        (congrArg₂ (· - ·)
          (EndpointReadings.value_eq_old_atPoint endpoints.val.leftView 1)
          (EndpointReadings.value_eq_old_atPoint endpoints.val.leftView 0)).trans
            (LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry.LiftedSource.value_eq
              piece.occurrence shared).symm
      have same : value = piece.value shared - routeValue piece location shared :=
        valueEq.trans (congrArg₂ (· - ·) leftEq endpoints.val.increment_eq)
      exact ⟨inputs, endpoints, left, right, compared, ⟨value, same, bounded⟩⟩)

namespace PointComparison

variable {contact requested originalLeft} (kept : PointComparison contact requested originalLeft)

/-- Read both original physical contact and P request caches with their whole identity and actual floor certificate. -/
@[expose] def inputs :
    {value : RouteContact piece location × Budget contact allowance (some ordinary) //
      value = (contact, requested) ∧ Budget.index requested ≤ index} := kept.1

/-- Read the same actual retained old-left/new-right endpoint view. -/
@[expose] def endpoints : EndpointView (ordinary := ordinary) (piece := piece) (location := location) originalLeft :=
  kept.2.1.val

/-- Read the original left primitive cache with only its genuine whole domain transport. -/
@[expose] def leftData : DomainPrimitives contact.left.domain source index (numerator := ordinary.numerator) :=
  kept.2.2.1.val

/-- Read the original right primitive cache with only its genuine whole domain transport. -/
@[expose] def rightData : DomainPrimitives contact.right.domain source index (numerator := ordinary.numerator) :=
  kept.2.2.2.1.val

/-- Read the SAME single original P common-model and entered-reading comparison. -/
@[expose] def comparison : ContactBudget.PolynomialComparison requested.2 kept.leftData kept.rightData :=
  kept.2.2.2.2.1.val

/-- Read the actual cached difference of the supplied two partial endpoint increments. -/
@[expose] def value : Canonical := kept.2.2.2.2.2.val

/-- The complete physical contact and P budget are the actual supplied caches. -/
theorem inputs_eq : kept.inputs.val = (contact, requested) := kept.1.property.1

include kept in
/-- The original cached numerical stage really pays the actual genuine P request. -/
theorem later : Budget.index requested ≤ index := kept.1.property.2

/-- The actual right view retains its one original constructor and supplied whole left cache. -/
theorem endpoints_eq : kept.endpoints =
    EndpointView.build (ordinary := ordinary) (piece := piece) (location := location) originalLeft :=
  kept.2.1.property

/-- The whole left transport preserves the original supplied numerical data. -/
theorem leftData_heq : HEq kept.leftData (EndpointReadings.data kept.endpoints.leftView) :=
  kept.2.2.1.property

/-- The whole right transport preserves the same actual routed-domain numerical data. -/
theorem rightData_heq : HEq kept.rightData kept.endpoints.data := kept.2.2.2.1.property

/-- The full common comparison retains its one original factory on those exact transported input caches. -/
theorem comparison_eq : kept.comparison =
    ContactBudget.comparePolynomial (owner := contact.owner) (prepared := contact.prepared)
      requested.2 kept.leftData kept.rightData := kept.2.2.2.2.1.property

/-- The cached scalar is the actual same-bank partial-fragment increment difference. -/
theorem value_eq : kept.value = piece.value shared - routeValue piece location shared :=
  kept.2.2.2.2.2.property.1

/-- The actual cached difference meets the original allocated positive request. -/
theorem accurate : normSq kept.value < allowance := kept.2.2.2.2.2.property.2

include kept in
/-- Actual source-fragment and selected-route increments satisfy the genuinely requested P bound. -/
theorem increment_accurate : normSq (piece.value shared - routeValue piece location shared) < allowance :=
  Eq.mp (congrArg (fun value : Canonical => normSq value < allowance) kept.value_eq) kept.accurate

end PointComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact
