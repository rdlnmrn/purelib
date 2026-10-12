module
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

@[expose] public section

/-! Exact paired fan boundary readback, including both radial sides. -/
namespace Purelib.Riemann.RootContinuation.RootRadialPairedArcs.Bilinear
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (chord point)
open Purelib.Riemann.RootContinuation.RootRadialGeometry.Bilinear (radialArea)

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- The original dyadic bilinear area along the chord from the first point to the last. -/
def arcArea (values : Basic.Canonical → Stokes.PrimitivePoint) (depth : Nat) (first last : Basic.Canonical) : Gaussian
  :=
  dyadicArea (fun parameter => values (chord first last parameter)) depth 0 1

open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- A constant primitive-point trace has zero dyadic area at every depth. -/
private theorem constant_area (value : Stokes.PrimitivePoint) (depth : Nat) (first last : Fraction.Rational) :
    dyadicArea (fun _ => value) depth first last = 0 := by
  induction depth generalizing first last with
  | zero => rw [DyadicBilinearBoundaryRibbon.dyadicArea_zero]; unfold Stokes.edgeArea; ring1
  | succ depth ih => rw [DyadicBilinearBoundaryRibbon.dyadicArea_succ, ih, ih]; ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The original radial parameter rectangle splits into its first radius, chord and reversed last radius.

The exact unit-box side readbacks retain the original endpoint order and dyadic depth, while the apex side contributes
zero. -/
theorem rectangle_boundary (values : Basic.Canonical → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Basic.Canonical) :
    PreparedBoxBoundary.rectangleBoundary (fun parameter => values (point first last parameter))
      depth RadialTriangles.unitBox =
        radialArea values depth first + arcArea values depth first last - radialArea values depth last := by
  have sourceZero : chord first last 0 = first := by
    apply Basic.ext <;> simp only [chord, Basic.add_re, Basic.add_im, Scale.scale_re, Scale.scale_im] <;> ring1
  have sourceOne : chord first last 1 = last := by
    apply Basic.ext <;> simp only [chord, Basic.add_re, Basic.add_im, Scale.scale_re, Scale.scale_im] <;> ring1
  have bottom (parameter : Fraction.Rational) : point first last ⟨parameter, 0⟩ = Scale.scale parameter first := by
    change Scale.scale parameter (chord first last 0) = _
    rw [sourceZero]
  have top (parameter : Fraction.Rational) : point first last ⟨parameter, 1⟩ = Scale.scale parameter last := by
    change Scale.scale parameter (chord first last 1) = _
    rw [sourceOne]
  have outer (parameter : Fraction.Rational) : point first last ⟨1, parameter⟩ = chord first last parameter := by
    apply Basic.ext <;> simp only [point, Scale.scale_re, Scale.scale_im] <;> ring1
  have apex (parameter : Fraction.Rational) : point first last ⟨0, parameter⟩ = 0 := by
    change Scale.scale 0 (chord first last parameter) = _
    apply Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im, Basic.zero_re, Basic.zero_im] <;> ring1
  unfold PreparedBoxBoundary.rectangleBoundary
  change PreparedBoxBoundary.horizontalBoundary _ depth 0 1 0 + PreparedBoxBoundary.verticalBoundary _ depth 0 1 1 -
    PreparedBoxBoundary.horizontalBoundary _ depth 0 1 1 - PreparedBoxBoundary.verticalBoundary _ depth 0 1 0 = _
  rw [DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
    DyadicBilinearBoundaryRibbon.verticalBoundary_eq_dyadicArea,
    DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
      DyadicBilinearBoundaryRibbon.verticalBoundary_eq_dyadicArea]
  rw [DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (bottom parameter)) depth 0 1,
    DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (outer parameter)) depth 0 1,
    DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (top parameter)) depth 0 1,
    DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (apex parameter)) depth 0 1,
      constant_area]
  change radialArea values depth first + arcArea values depth first last - radialArea values depth last - 0 = _
  ring1

end Purelib.Riemann.RootContinuation.RootRadialPairedArcs.Bilinear

namespace Purelib.Riemann.RootContinuation.RootRadialPairedArcs.PairedPolynomialSample
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes (edgeArea edgeListArea)
open Purelib.Riemann.Normalization
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Riemann.Periods.ReciprocalCapBilinearBounds (pairedValue)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (point)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (BoundedRefinement)
open Purelib.Riemann.RootContinuation.RootRadialPairedBoundary (PairedPolynomialSample)
variable {genus index otherIndex depth : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential other : Differential genus} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox}
  {first last : Purelib.Data.Gaussian.Basic.Canonical} {parameters :
    Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth}
  {refinement : BoundedRefinement first last parameters}
  {left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample
    Purelib.Riemann.RootContinuation.RootRadialGeometry.domain}
  {right : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds otherSample
    Purelib.Riemann.RootContinuation.RootRadialGeometry.domain}

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
/-- The cached original paired boundary area reads back the exact radial parameter rectangle.

The retained coordinate identities and original triangulated boundary identify the same ordered area sum. -/
theorem boundary_eq_rectangle (evaluated : PairedPolynomialSample refinement left right) :
    evaluated.area = PreparedBoxBoundary.rectangleBoundary
      (fun parameter => pairedValue sample otherSample (point first last parameter)) depth RadialTriangles.unitBox := by
  rw [evaluated.area_eq]
  calc
    _ = edgeListArea (fun vertex => pairedValue sample otherSample
        (point first last (parameters.mesh.mesh.coordinate vertex))) parameters.mesh.mesh.triangulation.boundary := by
      induction parameters.mesh.mesh.triangulation.boundary with
      | nil => rfl
      | cons edge rest ih =>
          change edgeArea (evaluated.values edge.start) (evaluated.values edge.finish) + _ =
            edgeArea _ _ + _
          rw [evaluated.values_eq, evaluated.values_eq, refinement.coordinates_eq, refinement.coordinates_eq, ih]
    _ = PreparedBoxBoundary.rectangleBoundary
        (fun parameter => pairedValue sample otherSample (point first last parameter)) depth
          parameters.mesh.partition.parent :=
      PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary parameters.mesh
        (fun parameter => pairedValue sample otherSample (point first last parameter))
    _ = _ := by rw [parameters.parent_eq]

open Purelib.Riemann.RootContinuation in
/-- The cached original paired boundary area is first radius plus chord minus last radius. -/
theorem boundary_eq_arcs (evaluated : PairedPolynomialSample refinement left right) :
    evaluated.area = RootRadialGeometry.Bilinear.radialArea (pairedValue sample otherSample) depth first +
      RootRadialPairedArcs.Bilinear.arcArea (pairedValue sample otherSample) depth first last -
      RootRadialGeometry.Bilinear.radialArea (pairedValue sample otherSample) depth last :=
  boundary_eq_rectangle evaluated |>.trans (RootRadialPairedArcs.Bilinear.rectangle_boundary _ _ _ _)

end Purelib.Riemann.RootContinuation.RootRadialPairedArcs.PairedPolynomialSample
