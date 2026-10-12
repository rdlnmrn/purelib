module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The actual signed face correction receives one finite coefficient
budget, retaining repeated faces and both signs. All triangle requests are
made before evaluating the shared canonical cochain. -/

section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

open Purelib.Topology.Polygon.Stokes

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

/-- The original signed face correction is the finite index sum of its integer-weighted boundary values. -/
private theorem faceValue_sum {count faces : Nat} (triangles : Fin faces → Topology.Polygon.Stokes.OrientedTriangle
  count)
    (value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (terms : List
      (Topology.Surface.Sewing.SewingRetraction.FaceTerm faces)) :
    Topology.Surface.Sewing.SewingRetraction.faceValue triangles value terms = Purelib.Algebra.FiniteSum.Fin.sumFin (fun
      index : Fin terms.length =>
      (terms[index.val].1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value
        (triangles terms[index.val].2).boundary) := open Purelib.Algebra in by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    change (head.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value (triangles
      head.2).boundary + Topology.Surface.Sewing.SewingRetraction.faceValue triangles value tail =
      (head.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value (triangles
        head.2).boundary + _
    rw [ih]
    rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

set_option genInjectivity false in
/-- A coefficient-paid chart request for the actual signed face occurrence list.

Repeated faces and both signs are retained in order, together with their individual triangle requests and one sufficient
stage. -/
structure SignedFaceChartRequest (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (terms : List
  (Topology.Surface.Sewing.SewingRetraction.FaceTerm mesh.triangles.length))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) where
  /-- The requested whole signed correction target is positive. -/ positive : 0 < target
  /-- The retained finite coefficient bound for the actual original integer weights. -/ coefficients :
    Periods.WeightedPeriods.Coefficients (Data.Vector.Basic.vectorOfFn (fun index : Fin terms.length =>
    terms[index.val].1))
  /-- The retained local triangle comparison allowance. -/ component : Fraction.Rational
  /-- The local allowance is the original coefficient-based target allocation. -/ component_eq : component =
    coefficients.perComponent target
  /-- The actual triangle request for each original signed face occurrence. -/ requests : Data.Vector.DependentVector
    (fun index : Fin terms.length =>
    Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.TriangleChartRequest terms[index.val].2 differential
      domains component)
  /-- The cached common sufficient triangle comparison stage. -/ index : Nat
  /-- The stage is exactly the maximum of the retained occurrence request stages. -/ index_eq : index = requests.maximum
    (fun _ request => request.index)

constructive_injectivity SignedFaceChartRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

variable {terms : List (Topology.Surface.Sewing.SewingRetraction.FaceTerm mesh.triangles.length)} {target :
  Fraction.Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest

/-- Retain the original signed weights, allocate their paid component target and prepare every actual triangle
comparison. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (terms : List
  (Topology.Surface.Sewing.SewingRetraction.FaceTerm mesh.triangles.length))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest mesh terms differential domains
      target :=
  let coefficients := Periods.WeightedPeriods.Coefficients.build (Data.Vector.Basic.vectorOfFn (fun index : Fin
    terms.length => terms[index.val].1))
  let component := coefficients.perComponent target
  let requests := Data.Vector.DependentVector.ofFn (fun index : Fin terms.length =>
    Hyperelliptic.Meshes.PuncturedGrid.TriangleChartRequests.TriangleChartRequest.build mesh terms[index.val].2
      differential domains component (coefficients.perComponent_positive positive))
  ⟨positive, coefficients, component, rfl, requests, requests.maximum (fun _ request => request.index), rfl⟩

/-- The canonical signed face correction meets its retained whole target once every original triangle comparison is
valid. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest mesh terms
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.faceValue mesh.triangulation.faces
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values) terms) < target :=
      open Purelib.Algebra in by
  have bounded : ∀ entry : Fin terms.length,
      Gaussian.Basic.Canonical.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values)
        (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary) ≤ request.component := by
    intro entry
    have scalar := ((request.requests.get entry).accurate
      ((request.requests.get_le_maximum (fun _ child => child.index) entry).trans (request.index_eq ▸ later))
        readings).le
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have bound := request.coefficients.normSq_combine_le
    (fun entry => Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary)
    (fun _ => request.component) bounded
  have equal := (request.coefficients.combine_eq
    (fun entry => Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary)).trans
    ((FiniteSum.Fin.sumFin_congr (fun entry => by rw [Data.Vector.Basic.vectorOfFn_apply])).trans
      (Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.faceValue_sum mesh.triangulation.faces
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values) terms).symm)
  rw [equal, request.coefficients.charge_constant] at bound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans_lt ((congrArg (request.coefficients.mass * ·) request.component_eq).trans_lt
    (request.coefficients.mass_mul_perComponent_lt request.positive))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest

end
