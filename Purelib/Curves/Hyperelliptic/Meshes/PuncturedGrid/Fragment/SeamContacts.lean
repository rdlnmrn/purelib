module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Requested differences of actual original chart-transition readings

The contact's scalar index is selected from its cached geometry before a
later face bank is read. The estimate consumes the same original domains,
primitive caches, and endpoint values used by the closed seam reduction.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}
  {firstLeft firstRight lastLeft lastRight : RootedWords.LiftedFragment axes
    domains mesh source count target}

namespace ChartContact

/-- Prepare the positive scalar allowance on the actual retained pair of chart owners. -/
@[expose] def budget (contact : ChartContacts.LiftedFragment.ChartContact
  firstLeft firstRight lastLeft lastRight) (allowance : Fraction.Rational)
    (positive : 0 < allowance) : Face.ContactRequests.ContactBudget contact.left
      contact.right allowance :=
  Face.ContactRequests.ContactBudget.build contact.left contact.right allowance
    positive

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts.ChartContact in
/-- At every sufficiently late common face bank, the two actual chart-transition readings differ by less than the
retained contact allowance. -/
theorem accurate (contact : ChartContacts.LiftedFragment.ChartContact
  firstLeft firstRight lastLeft lastRight) {allowance : Fraction.Rational}
    (budget : Face.ContactRequests.ContactBudget contact.left contact.right
      allowance)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (later :
      budget.index ≤ index)
    (firstPresent : firstLeft.last ∈ points) (lastPresent : lastLeft.last ∈ points) :
    Gaussian.Norm.Basic.normSq ((SeamReadings.atPoint lastLeft
      shared lastLeft.last - SeamReadings.atPoint lastRight shared
      lastRight.first) -
      (SeamReadings.atPoint firstLeft shared firstLeft.last -
        SeamReadings.atPoint firstRight shared firstRight.first)) <
        allowance := by
  have estimate :=
    Face.MeshContactRequests.ContactBudget.transition_accurate_of_domains budget
    later firstLeft.assigned.domain firstRight.assigned.domain
    contact.left_sheet contact.right_sheet contact.left_domain contact.right_domain
    (BankReadings.meshReadings firstLeft.assigned shared)
    (BankReadings.meshReadings firstRight.assigned shared)
    firstPresent lastPresent firstPresent lastPresent
  rw [SeamReadings.assigned_atPoint firstLeft shared lastLeft.last,
    SeamReadings.assigned_atPoint firstLeft shared firstLeft.last,
    SeamReadings.assigned_atPoint firstRight shared lastLeft.last,
      SeamReadings.assigned_atPoint firstRight shared firstLeft.last] at estimate
  have leftLast := SeamReadings.atPoint_eq_of_chart shared contact.same_left
    (rfl : lastLeft.last = lastLeft.last)
  have rightLast := SeamReadings.atPoint_eq_of_chart shared
    contact.same_right contact.last_coordinate
  have rightFirst := congrArg (SeamReadings.atPoint firstRight shared)
    contact.first_coordinate
  rw [leftLast, rightLast, rightFirst] at estimate
  exact estimate

end ChartContact

namespace Seam

variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
  {shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics}
  {first last : SeamReadings.Seam (axes := axes) (mesh := mesh) (count :=
    count) (target := target) shared}

/-- The seam's cached value is exactly its original left endpoint reading minus its right endpoint reading. -/
theorem value_spec (seam : SeamReadings.Seam (axes := axes) (mesh := mesh)
  (count := count) (target := target) shared) :
    seam.value = SeamReadings.atPoint seam.left shared seam.left.last -
      SeamReadings.atPoint seam.right shared seam.right.first := by
  rw [seam.value_eq, seam.leftValue_eq, seam.rightValue_eq]

/-- Both endpoint occurrences are taken from the actual retained seams.
No independent root classification is supplied by the caller. -/
@[expose] def contact (first last : SeamReadings.Seam (axes := axes) (mesh
  := mesh) (count := count) (target := target) shared)
    (sameLeft : SeamReadings.chart first.left =
      SeamReadings.chart last.left) (sameRight :
      SeamReadings.chart first.right =
      SeamReadings.chart last.right) :
    ChartContacts.LiftedFragment.ChartContact first.left first.right
      last.left last.right :=
  ChartContacts.LiftedFragment.ChartContact.build first.left first.right
    last.left last.right first.coordinate last.coordinate first.roots sameLeft sameRight

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts.Seam in
set_option genInjectivity false in
/-- Retain the common preparation and its scalar budget for reuse across
later shared banks. Equal-chart hypotheses describe the selected pair. -/
structure Request (first last : SeamReadings.Seam (axes := axes) (mesh :=
  mesh) (count := count) (target := target) shared)
    (allowance : Fraction.Rational) : Type 2 where
  /-- The actual contact on the retained seam endpoint occurrences. -/ contact :
    ChartContacts.LiftedFragment.ChartContact first.left first.right
    last.left last.right
  /-- The scalar accuracy request on those exact original contact owners. -/ budget :
    Face.ContactRequests.ContactBudget contact.left contact.right allowance

constructive_injectivity Request

namespace Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts.Seam in
/-- Retain the actual two-seam contact and its positive scalar budget using the supplied shared chart identities. -/
@[expose] def build (first last : SeamReadings.Seam (axes := axes) (mesh :=
  mesh) (count := count) (target := target) shared)
    (sameLeft : SeamReadings.chart first.left =
      SeamReadings.chart last.left) (sameRight :
      SeamReadings.chart first.right =
      SeamReadings.chart last.right)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
      Request first last allowance :=
  let contact := Seam.contact first last sameLeft sameRight
  ⟨contact, ChartContact.budget contact allowance positive⟩

/-- The original cached seam values differ by less than the retained allowance once the contact index is met. -/
theorem accurate {allowance : Fraction.Rational} (request :
  Request first last allowance) (later :
  request.budget.index ≤ index)
    (firstPresent : first.left.last ∈ points) (lastPresent : last.left.last ∈ points) :
    Gaussian.Norm.Basic.normSq (last.value - first.value) < allowance := by
  rw [Seam.value_spec last,
    Seam.value_spec first]
  exact ChartContact.accurate request.contact request.budget
    shared later firstPresent lastPresent

end Request
end Seam
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts
