module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Topology.Polygon.Stokes

import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
public import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Tactic.Ring

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)

@[expose] public section

/-!
# Constructed shared-primitive box surfaces with total error control

Build the actual dyadic box triangulation at the selected depth, acquire a
finite bank of operational root readings, and assign shared primitive values
from one cached polynomial basis.  The aggregate error is bounded by the
requested tolerance times the squared coefficient norm.  This identifies the
local mesh boundary, not yet the global A/B boundary word.
-/

namespace Purelib.Riemann.Topology

section
open Purelib.Data
namespace PrimitiveBoxSurface

/-- The exact rational carrier of the surface error budgets. -/
private abbrev Coordinate := Rat.Fraction.Rational
/-- The exact Gaussian rational carrier of the surface readings. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

end PrimitiveBoxSurface

end

namespace PrimitiveBoxSurface

open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- The dense Gaussian polynomial carrier of the retained primitive basis. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry.Rational (Box) in
/-- The rational box type of the original surface and root patch. -/
private abbrev Box := Purelib.Geometry.Rational.Box

end PrimitiveBoxSurface

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open _root_.Purelib.Riemann.Integration (PrimitiveBasis)
open _root_.Purelib.Riemann.Integration.PrimitiveBasis (PrimitiveBasisPreflight Coefficients)
open _root_.Purelib.Riemann.Topology (PrimitiveSurfaceBudget)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (TriangulatedPartition boxTriangles)
open Purelib.Riemann.Topology.PreparedSurfacePartitions (BoxPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (rectangleBoundary)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate
    Gaussian
    Polynomial
    Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.LinearAlgebra
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions

open Purelib.Riemann.Topology.PreparedSurfaceCoercivity

set_option genInjectivity false in
open Purelib.Data in
open Purelib.Geometry.Rational (Box) in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- A dyadic box triangulation with its retained primitive-basis error request.

The original box refines the continued-root patch, and the selected budget fixes the actual mesh depth and polynomial
accuracy. The mesh retains its exact parent-box equation. -/
structure PrimitiveBoxSurface {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount count : Nat}
    {patch : ContinuedNeighborhood polynomial siteCount} (preflight : PrimitiveBasisPreflight patch count)
    (box : Purelib.Geometry.Rational.Box) (target : Rat.Fraction.Rational) where
  /-- The original surface box lies within the retained root patch. -/ box_refines : box.Refines patch.box
  /-- The primitive-basis request paying the complete surface error at the selected depth. -/ budget :
    PrimitiveSurfaceBudget preflight box.diagonalSq target
  /-- The actual retained dyadic box triangulation at that budget's depth. -/ mesh :
    PreparedBoxTriangulation.TriangulatedPartition budget.depth
  /-- The triangulation's original parent is the requested surface box. -/ parent_eq : mesh.partition.parent = box

constructive_injectivity PrimitiveBoxSurface

namespace PrimitiveBoxSurface

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount count :
  Nat} {patch :
  ContinuedNeighborhood polynomial siteCount}
  {preflight : PrimitiveBasisPreflight patch count} {box : Purelib.Geometry.Rational.Box} {target :
    Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data in
open Purelib.Geometry.Rational (Box) in
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation in
/-- Acquire the primitive budget and construct its actual dyadic box triangulation.

The positive target and certified box inclusion determine a retained mesh with exact parent readback. -/
def build (preflight : PrimitiveBasisPreflight patch count) (box : Purelib.Geometry.Rational.Box) (refines :
  box.Refines patch.box)
    (target : Rat.Fraction.Rational) (positive : 0 < target) : PrimitiveBoxSurface preflight box target :=
  let budget := PrimitiveSurfaceBudget.acquire preflight box.diagonalSq target box.diagonalSq_nonneg positive
  { box_refines := refines
    budget := budget
    mesh := TriangulatedPartition.build (BoxPartition.build box budget.depth)
    parent_eq := rfl }

/-- Increase polynomial accuracy while retaining the exact constructed triangulation.

The supplied later index updates the budget without repeating point lookup, partitioning or incidence cancellation. -/
def refineIndex (surface : PrimitiveBoxSurface preflight box target) (index : Nat)
    (later : surface.budget.index ≤ index) : PrimitiveBoxSurface preflight box target where
  box_refines := surface.box_refines
  budget := surface.budget.refineIndex index later
  mesh := surface.mesh
  parent_eq := surface.parent_eq

/-- Increasing polynomial accuracy preserves the exact retained mesh. -/
theorem refineIndex_mesh (surface : PrimitiveBoxSurface preflight box target) (index : Nat)
    (later : surface.budget.index ≤ index) : (surface.refineIndex index later).mesh = surface.mesh := rfl

open Purelib.Geometry.Rectangle.Partition in
/-- The number of actual triangles in the retained dyadic box partition. -/
abbrev faceCount (surface : PrimitiveBoxSurface preflight box target) : Nat := (PreparedBoxTriangulation.boxTriangles
  surface.mesh.partition.leaves).length

/-- The retained triangulation has two times four to the selected depth faces. -/
theorem faceCount_eq (surface : PrimitiveBoxSurface preflight box target) : surface.faceCount = 2 * 4 ^
  surface.budget.depth :=
  surface.mesh.faceCount_eq

/-- All three vertices of every retained triangle lie in the original surface box. -/
theorem face_inside (surface : PrimitiveBoxSurface preflight box target) (face : Fin surface.faceCount) :
    box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first) ∧
    box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).second) ∧
    box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).third) := by
  have geometry := surface.mesh.face_geometry face
  rw [surface.parent_eq] at geometry
  exact ⟨geometry.1, geometry.2.1, geometry.2.2.1⟩

open Purelib.Data.Gaussian.Norm in
/-- Every retained triangle lies in the root patch and obeys the selected squared-diameter bounds.

The mesh's exact parent-box equality and budget depth identify the two outgoing edge bounds with the retained leaf
diameter. -/
theorem geometry (surface : PrimitiveBoxSurface preflight box target) (face : Fin surface.faceCount) :
    patch.box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first) ∧
    patch.box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).second) ∧
    patch.box.Contains (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).third) ∧
    normSq (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).second -
      surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first) ≤ surface.budget.leafDiameter ∧
    normSq (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).third -
      surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first) ≤ surface.budget.leafDiameter :=
        by
  have geometry := surface.mesh.face_geometry face
  rw [surface.parent_eq] at geometry
  have diameterEq : surface.mesh.partition.leafDiagonalSq = surface.budget.leafDiameter := by
    rw [surface.mesh.partition.leafDiagonalSq_eq, surface.parent_eq, surface.budget.leafDiameter_eq]
  have second := geometry.2.2.2.1.trans_eq diameterEq
  have third := geometry.2.2.2.2.trans_eq diameterEq
  rw [Basic.normSq_eq_canonical] at second third
  exact ⟨surface.box_refines.contains geometry.1, surface.box_refines.contains geometry.2.1,
    surface.box_refines.contains geometry.2.2.1, second, third⟩

end PrimitiveBoxSurface

namespace PrimitiveBoxSurface

set_option genInjectivity false in
open Purelib.Data in
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- A retained point owner and one actual operational root reading at a specified index.

The point is stored explicitly with patch containment; the possible-value certificate links the cached root to the
original owner's reading state. -/
structure PrimitiveFaceReading {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount : Nat}
    (patch : ContinuedNeighborhood polynomial siteCount) (index : Nat) where
  /-- The cached coordinate of the original face-reading point. -/ point : Gaussian.Basic.Canonical
  /-- The cached point lies in the retained root patch. -/ inside : patch.box.Contains point
  /-- The actual continued-root owner at that point. -/ sample : ContinuedNeighborhood.Point patch point
  /-- The retained possible root value at the specified reading index. -/ root : Gaussian.Basic.Canonical
  /-- The cached root is possible in that owner's actual reading state. -/ possible :
    sample.certificate.value.name.process.Possible (sample.readingState index) root

constructive_injectivity PrimitiveFaceReading

end PrimitiveBoxSurface

namespace PrimitiveBoxSurface.PrimitiveFaceReading

open Purelib.Data in
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- Acquire a root owner and retain an actual possible value at the requested point and index. -/
def acquire {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount :
  Nat} (patch : ContinuedNeighborhood polynomial siteCount)
    (index : Nat) (point : Gaussian.Basic.Canonical) (inside : patch.box.Contains point) : PrimitiveFaceReading patch
      index :=
  let sample := ContinuedNeighborhood.Point.acquire patch point inside
  let witness := sample.certificate.value.name.process.witness (sample.readingState index)
  ⟨point, inside, sample, witness.val, witness.property⟩

open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- Read a new index while reusing the original point and root owner. -/
def atIndex {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount index
  : Nat} {patch : ContinuedNeighborhood polynomial siteCount}
    (reading : PrimitiveFaceReading patch index) (next : Nat) : PrimitiveFaceReading patch next :=
  let witness := reading.sample.certificate.value.name.process.witness (reading.sample.readingState next)
  ⟨reading.point, reading.inside, reading.sample, witness.val, witness.property⟩

open Purelib.Data in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- Certify affine primitive error on a triangle using the retained first-vertex root reading.

The other vertices lie in the same root patch and both squared edge distances obey the selected budget's leaf diameter.
-/
def triangleCertificate {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {siteCount count : Nat} {patch : ContinuedNeighborhood polynomial
  siteCount}
    {preflight : PrimitiveBasisPreflight patch count} {diameter target : Rat.Fraction.Rational}
    (budget : PrimitiveSurfaceBudget preflight diameter target) (reading : PrimitiveFaceReading patch budget.index)
    (coefficients : Coefficients count) {first second third : Gaussian.Basic.Canonical} (pointEq : reading.point =
      first)
    (secondInside : patch.box.Contains second) (thirdInside : patch.box.Contains third)
    (secondDistance : normSq (second - first) ≤ budget.leafDiameter) (thirdDistance : normSq (third - first) ≤
      budget.leafDiameter) :
    Energy.AffineTriangle.AffineTriangleErrorCertificate ((Geometry.EvaluationLower.coefficientPolynomial
      coefficients).eval reading.point / reading.root)
      first second third (budget.basis.value coefficients first) (budget.basis.value coefficients second)
        (budget.basis.value coefficients third) := by
  subst first
  exact budget.triangleCertificate coefficients reading.inside secondInside thirdInside secondDistance thirdDistance
    reading.sample reading.possible

open Purelib.Data in
open Purelib.Polynomial.Dense.Gaussian.Basic in
open Purelib.Riemann in
/-- Read the three exact coefficient-scaled budgets retained by the triangle certificate. -/
theorem triangleCertificate_budgets {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount count : Nat}
    {patch : ContinuedNeighborhood polynomial siteCount} {preflight : PrimitiveBasisPreflight patch count}
    {diameter target : Rat.Fraction.Rational} (budget : PrimitiveSurfaceBudget preflight diameter target)
    (reading : PrimitiveFaceReading patch budget.index) (coefficients : Coefficients count)
    {first second third : Gaussian.Basic.Canonical} (pointEq : reading.point = first)
    (secondInside : patch.box.Contains second) (thirdInside : patch.box.Contains third)
    (secondDistance : normSq (second - first) ≤ budget.leafDiameter)
    (thirdDistance : normSq (third - first) ≤ budget.leafDiameter) :
    let certificate := reading.triangleCertificate budget coefficients pointEq
      secondInside thirdInside secondDistance thirdDistance
    certificate.firstBudget = Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      budget.products.first ∧
    certificate.secondBudget = Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      budget.products.second ∧
    certificate.mixedBudget = Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      budget.products.mixed := by
  subst first
  exact ⟨rfl, rfl, rfl⟩

end PrimitiveBoxSurface.PrimitiveFaceReading

namespace PrimitiveBoxSurface

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount count :
  Nat} {patch :
  ContinuedNeighborhood polynomial siteCount}
  {preflight : PrimitiveBasisPreflight patch count} {box : Purelib.Geometry.Rational.Box} {target :
    Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
open Purelib.Data in
/-- A finite root-reading bank indexed by the actual retained triangle faces.

Each entry stores the exact first-vertex coordinate of its original face, keeping point owners and numerical witnesses
tied to that mesh. -/
structure Readings (surface : PrimitiveBoxSurface preflight box target) where
  /-- The cached operational reading for every actual triangle face. -/ entries : Data.Vector
    (PrimitiveFaceReading patch surface.budget.index) surface.faceCount
  /-- Each reading's cached point is the first vertex of its retained face. -/ point_eq : ∀ face, (entries face).point =
    surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first

constructive_injectivity Readings

namespace Readings

variable {surface : PrimitiveBoxSurface preflight box target}

section
open Purelib.Data
/-- Acquire one actual operational reading at the first vertex of each retained face. -/
def build (surface : PrimitiveBoxSurface preflight box target) : Readings surface where
  entries := Vector.Basic.vectorOfFn fun face => PrimitiveFaceReading.acquire patch surface.budget.index
    (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first) (surface.geometry face).1
  point_eq := fun face => by rw [Vector.Basic.vectorOfFn_apply]; rfl

/-- Refresh reading states at a later index while preserving the original mesh and point owners. -/
def refineIndex (readings : Readings surface) (index : Nat) (later : surface.budget.index ≤ index) :
    Readings (surface.refineIndex index later) where
  entries := Vector.Basic.vectorOfFn fun face => (readings.entries face).atIndex index
  point_eq := fun face => by rw [Vector.Basic.vectorOfFn_apply]; exact readings.point_eq face

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Riemann in
/-- Materialize shared vertex primitives and face coefficients for the retained affine surface.

The structural vectors are evaluated once, and every actual face reuses the same three coefficient-scaled numerical
budgets with its retained root certificate. -/
def sample (readings : Readings surface) (coefficients : Coefficients count) :
    AffineSurfaceSample surface.mesh.mesh.vertices.length surface.faceCount :=
  let numerator := Geometry.EvaluationLower.coefficientPolynomial coefficients
  let primitives := Vector.Basic.vectorOfFn fun vertex => surface.budget.basis.value coefficients
    (surface.mesh.mesh.coordinate vertex)
  let faceCoefficients := Vector.Basic.vectorOfFn fun face => numerator.eval (readings.entries face).point /
    (readings.entries face).root
  let norm := Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  let firstBudget := norm * surface.budget.products.first
  let secondBudget := norm * surface.budget.products.second
  let mixedBudget := norm * surface.budget.products.mixed
  AffineSurfaceSample.ofFaces surface.mesh.mesh.triangulation surface.mesh.mesh.coordinate
    (fun vertex => primitives vertex) (fun face => faceCoefficients face) (fun face => by
      have geometry := surface.geometry face
      let certificate := (readings.entries face).triangleCertificate surface.budget coefficients (readings.point_eq
        face)
        geometry.2.1 geometry.2.2.1 geometry.2.2.2.1 geometry.2.2.2.2
      have budgets := (readings.entries face).triangleCertificate_budgets surface.budget coefficients (readings.point_eq
        face)
        geometry.2.1 geometry.2.2.1 geometry.2.2.2.1 geometry.2.2.2.2
      have firstEq : certificate.firstBudget = firstBudget := budgets.1
      have secondEq : certificate.secondBudget = secondBudget := budgets.2.1
      have mixedEq : certificate.mixedBudget = mixedBudget := budgets.2.2
      exact
        { firstBudget := firstBudget
          secondBudget := secondBudget
          mixedBudget := mixedBudget
          firstBudget_nonnegative := certificate.firstBudget_nonnegative.trans_eq firstEq
          secondBudget_nonnegative := certificate.secondBudget_nonnegative.trans_eq secondEq
          mixedBudget_nonnegative := certificate.mixedBudget_nonnegative.trans_eq mixedEq
          firstProductBound := by
            dsimp only [primitives, faceCoefficients]
            simp only [Vector.Basic.vectorOfFn_apply]
            exact certificate.firstProductBound.trans_eq (congrArg (fun value => value ^ 2) firstEq)
          secondProductBound := by
            dsimp only [primitives, faceCoefficients]
            simp only [Vector.Basic.vectorOfFn_apply]
            exact certificate.secondProductBound.trans_eq (congrArg (fun value => value ^ 2) secondEq)
          mixedProductBound := by
            dsimp only [primitives, faceCoefficients]
            simp only [Vector.Basic.vectorOfFn_apply]
            exact certificate.mixedProductBound.trans_eq (congrArg (fun value => value ^ 2) mixedEq) })

open Purelib.Algebra in
open Purelib.Data in
/-- A finite constant rational sum equals its count times the constant. -/
private theorem sum_constant (size : Nat) (value : Rat.Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin size => value) = (size : Rat.Fraction.Rational) * value := by
  induction size with
  | zero => change (0 : Rat.Fraction.Rational) = 0 * value; ring1
  | succ size ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Riemann in
/-- The sampled surface error is the coefficient norm times the actual face count and retained per-face budget. -/
theorem sample_errorBudget (readings : Readings surface) (coefficients : Coefficients count) :
    (readings.sample coefficients).errorBudget = Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      ((surface.faceCount : Rat.Fraction.Rational) * surface.budget.faceBudget) := by
  change FiniteSum.Fin.sumFin (fun _ : Fin surface.faceCount =>
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * surface.budget.products.first +
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * surface.budget.products.second +
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * surface.budget.products.mixed) = _
  rw [sum_constant, surface.budget.faceBudget_eq]
  ring1

open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann in
/-- The count-paid surface error is at most the target times the squared coefficient norm. -/
theorem sample_error_le (readings : Readings surface) (coefficients : Coefficients count) :
    (readings.sample coefficients).errorBudget ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      target := by
  rw [readings.sample_errorBudget, surface.faceCount_eq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct surface.budget.total_faceBudget_lt.le
    (PrimitiveBasis.coefficientNorm_nonnegative coefficients)

open Purelib.Topology in
/-- Pointwise equality of primitive values preserves the area of any finite oriented edge list. -/
private theorem edgeListArea_congr {size : Nat} (first second : Fin size → Polygon.Stokes.PrimitivePoint)
    (equal : ∀ vertex, first vertex = second vertex) (edges : List (OrientedEdge size)) :
    edgeListArea first edges = edgeListArea second edges := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      simp only [edgeListArea, equal edge.start, equal edge.finish, ih, -eq_self, -iff_self]
      rfl

open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary in
open Purelib.Integration in
/-- The actual shared-primitive mesh boundary equals the original box's four-side dyadic reading.

The retained vertex cache and exact parent-box equation transport the triangulation boundary identity to the requested
rectangle. -/
theorem sample_boundaryArea (readings : Readings surface) (coefficients : Coefficients count) :
    (readings.sample coefficients).boundaryArea =
      PreparedBoxBoundary.rectangleBoundary (fun point => Energy.Polygon.energyPrimitivePoint
        (surface.budget.basis.value coefficients point))
        surface.budget.depth box := by
  rw [(readings.sample coefficients).boundaryArea_eq]
  apply Eq.trans (edgeListArea_congr _
    (fun vertex => Energy.Polygon.energyPrimitivePoint (surface.budget.basis.value coefficients
      (surface.mesh.mesh.coordinate vertex)))
    (fun vertex => by
        change Energy.Polygon.energyPrimitivePoint ((Vector.Basic.vectorOfFn _) vertex) = _;
        rw [Vector.Basic.vectorOfFn_apply]) _)
  exact TriangulatedPartition.boundaryArea_eq_rectangleBoundary surface.mesh
    (fun point => Energy.Polygon.energyPrimitivePoint (surface.budget.basis.value coefficients point)) |>.trans
      (congrArg (PreparedBoxBoundary.rectangleBoundary _ surface.budget.depth) surface.parent_eq)

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Data.Rat in
/-- The retained affine energy minus its paid homogeneous error bounds the actual rectangle boundary energy.

The estimate uses the constructed mesh's four exterior sides, the same primitive basis and coefficient vector, and the
original requested tolerance. -/
theorem sample_energy_le_rectangleBoundary (readings : Readings surface) (coefficients : Coefficients count) :
    (readings.sample coefficients).affineEnergy - Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
      * target ≤
      (PreparedBoxBoundary.rectangleBoundary (fun point => Energy.Polygon.energyPrimitivePoint
        (surface.budget.basis.value coefficients point))
        surface.budget.depth box).im / 4 := by
  have lower := (Fraction.Order.Arithmetic.sub_le_sub_left_direct (readings.sample_error_le coefficients)
    (readings.sample coefficients).affineEnergy).trans
    (readings.sample coefficients).affineEnergy_sub_errorBudget_le_boundaryEnergy
  rw [readings.sample_boundaryArea coefficients] at lower
  exact lower

end Readings

end PrimitiveBoxSurface

end Purelib.Riemann.Topology
