module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
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

open Purelib.Topology.Surface.Sewing

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
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

/-- The original signed face correction is the finite index sum of its integer-weighted boundary values. -/
private theorem faceValue_sum {count faces : Nat} (triangles : Fin faces → OrientedTriangle
  count)
    (value : OrientedEdge count → Gaussian.Basic.Canonical) (terms : List
      (SewingRetraction.FaceTerm faces)) :
    SewingRetraction.faceValue triangles value terms = Algebra.FiniteSum.Fin.sumFin (fun
      index : Fin terms.length =>
      (terms[index.val].1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
        (triangles terms[index.val].2).boundary) := open Algebra in by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    change (head.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value (triangles
      head.2).boundary + SewingRetraction.faceValue triangles value tail =
      (head.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value (triangles
        head.2).boundary + _
    rw [ih]
    rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
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
  (SewingRetraction.FaceTerm mesh.triangles.length))
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The requested whole signed correction target is positive. -/ positive : 0 < target
  /-- The retained finite coefficient bound for the actual original integer weights. -/ coefficients :
    Periods.WeightedPeriods.Coefficients (Vector.Basic.vectorOfFn (fun index : Fin terms.length =>
    terms[index.val].1))
  /-- The retained local triangle comparison allowance. -/ component : Fraction.Rational
  /-- The local allowance is the original coefficient-based target allocation. -/ component_eq : component =
    coefficients.perComponent target
  /-- The actual triangle request for each original signed face occurrence. -/ requests : Vector.DependentVector
    (fun index : Fin terms.length =>
    TriangleChartRequests.TriangleChartRequest terms[index.val].2 differential
      domains component polynomial)
  /-- The cached common sufficient triangle comparison stage. -/ index : Nat
  /-- The stage is exactly the maximum of the retained occurrence request stages. -/ index_eq : index = requests.maximum
    (fun _ request => request.index)

constructive_injectivity SignedFaceChartRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests

variable {terms : List (SewingRetraction.FaceTerm mesh.triangles.length)} {target :
  Fraction.Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest

/-- Retain the original signed weights, allocate their paid component target and prepare every actual triangle
comparison. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (terms : List
  (SewingRetraction.FaceTerm mesh.triangles.length))
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
      SignedFaceChartRequest mesh terms differential domains
      target polynomial :=
  let coefficients := Periods.WeightedPeriods.Coefficients.build (Vector.Basic.vectorOfFn (fun index : Fin
    terms.length => terms[index.val].1))
  let component := coefficients.perComponent target
  let requests := Vector.DependentVector.ofFn (fun index : Fin terms.length =>
    TriangleChartRequests.TriangleChartRequest.build mesh terms[index.val].2
      differential domains component (coefficients.perComponent_positive positive) polynomial)
  ⟨positive, coefficients, component, rfl, requests, requests.maximum (fun _ request => request.index), rfl⟩

/-- The original retained coefficient cache pays the signed sum of its actual triangle circulations. -/
private theorem value_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedFaceChartRequest mesh terms differential domains target polynomial)
    {stage : Nat} {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (bounded : ∀ entry : Fin terms.length,
      Gaussian.Basic.Canonical.normSq (SewingRetraction.wordValue
        (CanonicalEdgeValues.edgeValuation mesh readings.values)
        (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary) ≤ request.component) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.faceValue mesh.triangulation.faces
      (CanonicalEdgeValues.edgeValuation mesh readings.values) terms) < target :=
      open Purelib.Algebra in by
  have bound := request.coefficients.normSq_combine_le
    (fun entry => SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary)
    (fun _ => request.component) bounded
  have equal := (request.coefficients.combine_eq
    (fun entry => SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary)).trans
    ((FiniteSum.Fin.sumFin_congr (fun entry => by rw [Vector.Basic.vectorOfFn_apply])).trans
      (SignedFaceChartRequests.faceValue_sum mesh.triangulation.faces
        (CanonicalEdgeValues.edgeValuation mesh readings.values) terms).symm)
  rw [equal, request.coefficients.charge_constant] at bound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans_lt ((congrArg (request.coefficients.mass * ·) request.component_eq).trans_lt
    (request.coefficients.mass_mul_perComponent_lt request.positive))

/-- The canonical signed face correction meets its retained whole target once every original triangle comparison is
valid. -/
theorem accurate (request : SignedFaceChartRequest mesh terms
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.faceValue mesh.triangulation.faces
      (CanonicalEdgeValues.edgeValuation mesh readings.values) terms) < target :=
      open Purelib.Algebra in by
  have bounded : ∀ entry : Fin terms.length,
      Gaussian.Basic.Canonical.normSq (SewingRetraction.wordValue
        (CanonicalEdgeValues.edgeValuation mesh readings.values)
        (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary) ≤ request.component := by
    intro entry
    have scalar := ((request.requests.get entry).accurate
      ((request.requests.get_le_maximum (fun _ child => child.index) entry).trans (request.index_eq ▸ later))
        readings).le
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  exact value_accurate request readings bounded

/-- The exact triangle comparison caches for every original signed face occurrence, retaining repeats and both signs. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedFaceChartRequest mesh terms differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type 1 :=
  Vector.DependentVector (fun entry : Fin terms.length => (request.requests.get entry).Comparison shared)

/-- Execute each original occurrence's triangle comparison once on the SAME supplied polynomial primitive bank. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedFaceChartRequest mesh terms differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared :=
  Vector.DependentVector.ofFn (fun entry : Fin terms.length => (request.requests.get entry).compare shared)

/-- The SAME retained triangle comparison data internally pay the complete signed face correction. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : SignedFaceChartRequest mesh terms differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : request.Comparison shared) (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (SewingRetraction.faceValue mesh.triangulation.faces
      (CanonicalEdgeValues.edgeValuation mesh readings.values) terms) < target := by
  have bounded : ∀ entry : Fin terms.length,
      Gaussian.Basic.Canonical.normSq (SewingRetraction.wordValue
        (CanonicalEdgeValues.edgeValuation mesh readings.values)
        (mesh.triangulation.faces (terms[entry.val]'entry.isLt).2).boundary) ≤ request.component := by
    intro entry
    have scalar := ((request.requests.get entry).comparison_accurate
      ((request.requests.get_le_maximum (fun _ child => child.index) entry).trans (request.index_eq ▸ later))
      (compared.get entry) readings).le
    rewrite [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  exact value_accurate request readings bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedFaceChartRequests.SignedFaceChartRequest

end
