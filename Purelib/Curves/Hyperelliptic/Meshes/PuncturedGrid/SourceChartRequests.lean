module
import Purelib.Data.Nat.Order
public import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Init.Data.Fin.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! Ordered signed source/chart requests. Each retained occurrence preserves
its actual chart location, source equality and orientation. The strict single
reading certificate is available at an explicit bounded occurrence index. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
open Purelib.Data.Rat
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (SignedSourceChartRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {differential : Differential genus}

set_option genInjectivity false in
/-- The dependent ordered list of signed source/chart comparison requests.

Every retained source occurrence keeps its original chart location, orientation and tolerance. -/
inductive SourceChartRequests (differential : Differentials.Basic.Differential genus)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (allowance : Fraction.Rational) :
    List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length) → Type 2 where
  /-- The empty signed source list has no comparison requests. -/ | nil : SourceChartRequests differential domains
    allowance []
  /-- Retain one original signed source request followed by the dependent requests on its exact tail. -/ | cons {source
    sources} (head : SignedSourceChartRequests.SignedSourceChartRequest source differential domains allowance)
      (tail : SourceChartRequests differential domains allowance sources) :
      SourceChartRequests differential domains allowance (source :: sources)

constructive_injectivity SourceChartRequests

namespace SourceChartRequests

variable {allowance : Rational} {sources : List
  (SourceEdge mesh.triangles.length)}

/-- Prepare a signed chart request for every actual nonloop source occurrence at the supplied positive allowance. -/
@[expose] def build (differential : Differentials.Basic.Differential genus) (domains : DomainBanks.FaceDomainBank frames
  base.faces.regulars)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) →
      (∀ source ∈ sources, source.first ≠ source.last) → SourceChartRequests differential domains allowance sources
  | [], _ => .nil
  | source :: sources, nonloop => .cons
      (SignedSourceChartRequest.build source (nonloop source List.mem_cons_self) differential domains allowance
        positive)
      (build differential domains allowance positive sources (fun source member => nonloop source (List.mem_cons_of_mem
        _ member)))

/-- The maximum original stage required by the retained signed source requests, with zero for the empty list. -/
@[expose] def index : {sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)} → SourceChartRequests
  differential domains allowance sources → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.index tail.index

/-- At a paid common stage every retained source increment is strictly close to its actual canonical projected-edge
reading. -/
theorem accurate (requests : SourceChartRequests differential domains allowance sources)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (later : requests.index ≤ stage) : ∀ source ∈ sources,
      normSq (source.increment readings.values - CanonicalEdgeValues.edgeValuation mesh readings.values (source.project
        mesh.triangulation.faces)) < allowance := by
  induction requests with
  | nil => intro source member; exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      intro source member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · have scalar := head.accurate ((Data.Nat.Order.le_max_left _ _).trans later) readings
        rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) source member

/-- The actual retained signed request at an ordered occurrence. The supplied Fin bound is used directly; no default
indexing tactic is invoked. -/
@[expose] def «at» : {sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)} →
    (requests : SourceChartRequests differential domains allowance sources) →
    (occurrence : Fin sources.length) →
    SignedSourceChartRequests.SignedSourceChartRequest (sources[occurrence.val]'occurrence.isLt) differential domains
      allowance
  | [], .nil, occurrence => Fin.elim0 occurrence
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨index + 1, bound⟩ =>
      «at» tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- The actual signed request at a bounded occurrence index needs no later stage than the retained whole list. -/
theorem at_index_le : {sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)} →
    (requests : SourceChartRequests differential domains allowance sources) →
    (occurrence : Fin sources.length) → (requests.at occurrence).index ≤ requests.index
  | [], .nil, occurrence => Fin.elim0 occurrence
  | _ :: _, .cons _ _, ⟨0, _⟩ => Data.Nat.Order.le_max_left _ _
  | _ :: _, .cons _ tail, ⟨index + 1, bound⟩ =>
      (at_index_le tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩).trans (Data.Nat.Order.le_max_right _ _)

/-- The signed source at the supplied retained occurrence index satisfies its strict comparison bound at any paid common
stage. -/
theorem at_accurate (requests : SourceChartRequests differential domains allowance sources)
    (occurrence : Fin sources.length) {stage : Nat}
    {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (later : requests.index ≤ stage) :
    normSq ((sources[occurrence.val]'occurrence.isLt).increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values ((sources[occurrence.val]'occurrence.isLt).project
        mesh.triangulation.faces)) < allowance := by
  have scalar := (requests.at occurrence).accurate ((requests.at_index_le occurrence).trans later) readings
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end SourceChartRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Surface.Sewing
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (SignedSourceChartRequest
  oppositeSource)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : FaceDomainBank owner.frames
    owner.base.faces.regulars}

/-- The projected source of a signed chart request is a supported edge. -/
theorem
  SignedSourceChartRequests.SignedSourceChartRequest.supported
  {differential : Differentials.Basic.Differential genus} {source : SewnPrimitiveContacts.SourceEdge
  owner.mesh.triangles.length}
    {target : Fraction.Rational} (request : SignedSourceChartRequests.SignedSourceChartRequest source differential
      domains target) :
    source.project owner.mesh.triangulation.faces ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
      (source.project owner.mesh.triangulation.faces).reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces
        := by
  cases request with
  | forward request => exact Or.inl (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member request.positive)
  | backward request =>
      refine Or.inr ?_
      have member := Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member request.positive
      rwa [show (SignedSourceChartRequests.oppositeSource source).project owner.mesh.triangulation.faces =
        (source.project owner.mesh.triangulation.faces).reverse from rfl] at member

/-- Every retained source of a chart request list is a supported edge. -/
theorem SourceChartRequests.supported {differential :
  Differentials.Basic.Differential genus} {allowance : Fraction.Rational}
    {sources : List (SewnPrimitiveContacts.SourceEdge owner.mesh.triangles.length)}
    (requests : SourceChartRequests differential domains allowance sources) :
    ∀ source ∈ sources,
      source.project owner.mesh.triangulation.faces ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
        (source.project owner.mesh.triangulation.faces).reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces
          := by
  induction requests with
  | nil => intro source member; exact (List.not_mem_nil member).elim
  | cons head tail inductionHypothesis =>
      intro source member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact head.supported
      · exact inductionHypothesis source member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

end
