module
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialEnergy
public import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Tactic.Ring

open Purelib.Integration.Path.Dyadic

@[expose] public section

/-! # Exact outer and radial boundaries of sampled root fans -/

namespace Purelib.Riemann.RootContinuation.RootRadialGeometry

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (chord point)

section
open Purelib.Integration
open Purelib.Data
/-- The actual dyadic primitive area along the radius from zero to the supplied root coordinate. -/
def radialArea (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (source :
  Gaussian.Basic.Canonical) : Gaussian :=
  dyadicArea (fun parameter => values (scale parameter source)) depth 0
    1

/-- The actual dyadic primitive area along the chord between the two supplied root coordinates. -/
def arcArea (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (first last :
  Gaussian.Basic.Canonical) : Gaussian :=
  dyadicArea (fun parameter => values (chord first last parameter)) depth 0 1

/-- The dyadic primitive area of a constant path is zero at every depth. -/
private theorem constant_area (value : Gaussian.Basic.Canonical) (depth : Nat) (first last : Rational) :
    dyadicArea (fun _ => value) depth first last = 0 := by
  induction depth generalizing first last with
  | zero => rw [DyadicBoundaryRibbon.dyadicArea_zero]; unfold Path.BoundaryRibbon.area; ring1
  | succ depth ih => rw [DyadicBoundaryRibbon.dyadicArea_succ, ih, ih]; ring1

end

open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- The mapped unit-square boundary is the first radius plus outer chord minus final radius.

The fourth side maps to the constant apex and contributes zero, preserving the exact orientation and subdivision depth.
-/
theorem rectangle_boundary (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (first last :
  Gaussian.Basic.Canonical) :
    rectangleBoundary (fun parameter => energyPrimitivePoint
      (values (point first last parameter)))
      depth RadialTriangles.unitBox =
        radialArea values depth first + arcArea values depth first last - radialArea values depth last := by
  have sourceZero : chord first last 0 = first := by
    apply Gaussian.Basic.ext <;> simp only [chord, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have sourceOne : chord first last 1 = last := by
    apply Gaussian.Basic.ext <;> simp only [chord, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have bottom (parameter : Rational) : point first last ⟨parameter, 0⟩ = scale parameter
    first := by
    change scale parameter (chord first last 0) = _
    rw [sourceZero]
  have top (parameter : Rational) : point first last ⟨parameter, 1⟩ = scale parameter last
    := by
    change scale parameter (chord first last 1) = _
    rw [sourceOne]
  have outer (parameter : Rational) : point first last ⟨1, parameter⟩ = chord first last parameter := by
    apply Gaussian.Basic.ext <;> simp only [point, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have apex (parameter : Rational) : point first last ⟨0, parameter⟩ = 0 := by
    change scale 0 (chord first last parameter) = _
    apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im] <;> ring1
  unfold rectangleBoundary
  change horizontalBoundary _ depth 0 1 0 +
    verticalBoundary _ depth 0 1 1 -
    horizontalBoundary _ depth 0 1 1 -
      verticalBoundary _ depth 0 1 0 = _
  rw [DyadicBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
    DyadicBoundaryRibbon.verticalBoundary_eq_dyadicArea,
    DyadicBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
      DyadicBoundaryRibbon.verticalBoundary_eq_dyadicArea]
  rw [DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (bottom parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (outer parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (top parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (apex parameter)),
      constant_area]
  change radialArea values depth first + arcArea values depth first last - radialArea values depth last - 0 = _
  ring1

end Purelib.Riemann.RootContinuation.RootRadialGeometry

namespace Purelib.Riemann.RootContinuation.RootRadialEnergy

open Purelib.Riemann.RootContinuation.RootRadialGeometry (radialArea arcArea rectangle_boundary point)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes (edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential : Differential genus} {index : Nat} {box :
    Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {first last : Canonical} {depth : Nat} {parameters :
    RadialTriangles.Parameters depth}
  {refinement : Refinement first last parameters} {radius : Data.Rat.Fraction.Rational}

open Purelib.Integration in
open Purelib.Geometry in
/-- The cached root-fan boundary area equals the actual mapped unit-square boundary reading. -/
theorem PolynomialSample.boundary_eq_rectangle
    (evaluated : PolynomialSample refinement sample radius) :
    evaluated.surface.boundaryArea = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
      (fun point => energyPrimitivePoint (sample.primitive.value.eval (RootRadialGeometry.point first
        last point)))
      depth RadialTriangles.unitBox := by
  rw [evaluated.surface_eq]
  change edgeListArea (fun vertex => energyPrimitivePoint (evaluated.values vertex))
    parameters.mesh.mesh.triangulation.boundary = _
  calc
    _ = edgeListArea (fun vertex => energyPrimitivePoint (sample.primitive.value.eval (point first last
      (parameters.mesh.mesh.coordinate vertex))))
        parameters.mesh.mesh.triangulation.boundary := by
      generalize parameters.mesh.mesh.triangulation.boundary = edges
      induction edges with
      | nil => rfl
      | cons edge edges ih =>
          simp only [edgeListArea]
          rw [ih, evaluated.values_eq, evaluated.values_eq, refinement.coordinates_eq, refinement.coordinates_eq]
    _ = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
        (fun point => energyPrimitivePoint (sample.primitive.value.eval (RootRadialGeometry.point first
          last point)))
        depth parameters.mesh.partition.parent :=
          Rectangle.Partition.PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary
          parameters.mesh
          (fun point => energyPrimitivePoint (sample.primitive.value.eval (RootRadialGeometry.point first
            last point)))
    _ = _ := by rw [parameters.parent_eq]

/-- The cached root-fan boundary is exactly the two oriented radial readings and the outer chord reading. -/
theorem PolynomialSample.boundary_eq_arcs (evaluated : PolynomialSample refinement sample radius) :
    evaluated.surface.boundaryArea = radialArea sample.primitive.value.eval depth first +
      arcArea sample.primitive.value.eval depth first last - radialArea sample.primitive.value.eval depth last := by
  rw [evaluated.boundary_eq_rectangle]
  exact rectangle_boundary sample.primitive.value.eval depth first last

end Purelib.Riemann.RootContinuation.RootRadialEnergy
