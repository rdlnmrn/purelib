module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Data.Vector.Dependent
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames

section

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! A finite prefix-contact family retains fixed domains and one origin
owner. Every scalar request is selected before the shared numerical bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat} {points : Fin (count + 1) → Gaussian.Basic.Canonical} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}

set_option genInjectivity false in
/-- A finite original prefix-contact family over two fixed domains and one retained origin owner.

Every vertex retains its prepared path, both containment certificates and actual cached contact. -/
structure TraceContactBank (leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels
  start owner) (rightEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner)
    (leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet) (rightDomain
      : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet)
    (points : Fin (count + 1) → Gaussian.Basic.Canonical) (differential : Hyperelliptic.Differentials.Basic.Differential
      genus) (parentSheet : Fin 2) where
  /-- The initial retained trace coordinate is the original common path origin. -/ origin_eq : points 0 = start
  /-- The original ambient box for each retained origin-to-vertex path. -/ ambient : Fin (count + 1) →
    Rational.Box
  /-- The original clear paths from the common retained origin to every trace vertex. -/ paths : ∀ vertex,
    Polynomial.Geometry.ClearPath curve.polynomial (ambient vertex) start (points vertex)
  /-- The exact dependent preparations of the retained original paths and root owner. -/ prepared :
    Data.Vector.DependentVector (fun vertex =>
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (paths vertex) owner)
  /-- Every retained original path lies in the first face cell. -/ leftInside : ∀ vertex, (paths vertex).InBox
    firstFace.cell.box
  /-- Every retained original path lies in the second face cell. -/ rightInside : ∀ vertex, (paths vertex).InBox
    lastFace.cell.box
  /-- The original fixed-domain contacts built from those exact retained paths and owners. -/ contacts :
    Data.Vector.DependentVector (fun vertex => Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts.FixedDomainContact
    leftEntry rightEntry leftDomain rightDomain
    (prepared.get vertex) (leftInside vertex) (rightInside vertex) differential parentSheet)

constructive_injectivity TraceContactBank

namespace TraceContactBank

/-- Construct the original per-vertex fixed-domain contacts using the supplied retained path preparations and parent
caches. -/
@[expose] def build (leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start
  owner) (rightEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner)
    (leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet) (rightDomain
      : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet)
    (points : Fin (count + 1) → Gaussian.Basic.Canonical) (origin_eq : points 0 = start)
    (ambient : Fin (count + 1) → Rational.Box)
    (paths : ∀ vertex, Polynomial.Geometry.ClearPath curve.polynomial (ambient vertex) start (points vertex))
    (prepared : Data.Vector.DependentVector (fun vertex =>
      Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (paths vertex) owner))
    (leftInside : ∀ vertex, (paths vertex).InBox firstFace.cell.box)
    (rightInside : ∀ vertex, (paths vertex).InBox lastFace.cell.box)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    (caches : Data.Vector.DependentVector (fun vertex =>
      Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache (prepared.get vertex) differential
      parentSheet)) :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
      points differential parentSheet :=
  ⟨origin_eq, ambient, paths, prepared, leftInside, rightInside, Data.Vector.DependentVector.ofFn fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts.FixedDomainContact.build leftEntry rightEntry leftDomain
      rightDomain (prepared.get vertex)
      (leftInside vertex) (rightInside vertex) differential parentSheet (caches.get vertex)⟩

set_option genInjectivity false in
/-- Paid scalar comparisons for every retained original prefix contact at one sufficient common stage. -/
structure Request
    (contacts : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain
      rightDomain points differential parentSheet)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The actual dependent comparison budgets for all original retained prefix contacts. -/ budgets :
    Data.Vector.DependentVector (fun vertex => Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget
    (contacts.contacts.get vertex).left (contacts.contacts.get vertex).right target)
  /-- The shared sufficient original comparison stage including the retained floor. -/ index : Nat
  /-- The requested original floor is at most the retained common stage. -/ floor_le : floor ≤ index
  /-- Every original per-vertex comparison is ready by the retained shared stage. -/ index_ge : ∀ vertex, (budgets.get
    vertex).index ≤ index

constructive_injectivity Request

namespace Request
variable {contacts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry
  rightEntry leftDomain rightDomain points differential parentSheet}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare every original prefix-contact comparison before taking the maximum with the supplied reading floor. -/
@[expose] def build (contacts : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry
  rightEntry leftDomain rightDomain points differential parentSheet)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request contacts target floor :=
  let budgets := Data.Vector.DependentVector.ofFn fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget.build (contacts.contacts.get vertex).left
      (contacts.contacts.get vertex).right target positive
  let maximum := budgets.maximum (fun _ budget => budget.index)
  ⟨budgets, max floor maximum, Data.Nat.Order.le_max_left _ _, fun vertex =>
    (budgets.get_le_maximum (fun _ budget => budget.index) vertex).trans (Data.Nat.Order.le_max_right _ _)⟩

/-- The two original domain readings of each retained origin-based increment differ by less than the requested
squared-norm tolerance. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank.Request contacts
  target floor) {index : Nat} (later : request.index ≤ index)
    (leftData : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain differential index)
      (rightData : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain differential
      index)
    (leftReadings : Readings.RectangularPointReadings.PointReadings leftData.anchors leftData.offsets points)
    (rightReadings : Readings.RectangularPointReadings.PointReadings rightData.anchors rightData.offsets points)
    (vertex : Fin (count + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values vertex - leftReadings.values 0) -
      (rightReadings.values vertex - rightReadings.values 0)) < target :=
  (contacts.contacts.get vertex).points_accurate (request.budgets.get vertex)
    ((request.index_ge vertex).trans later) leftData rightData leftReadings rightReadings
    0 vertex 0 vertex contacts.origin_eq rfl contacts.origin_eq rfl

end Request
end TraceContactBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks

end
