module

import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries
import Purelib.Integration.Polynomial.Rectangle.StitchedSideAreas

@[expose] public section

/-! Transport a retained perimeter across an exact mesh equality. Its cached
areas and endpoint readings are preserved without evaluating them again. -/
namespace Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport

open Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterEntries.Perimeter
variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} {box :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
  {first last : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts box}
  {values : Fin (columns + 1) → Fin (rows + 1) → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian →
    Purelib.Topology.Polygon.Stokes.PrimitivePoint}
  {assembly : Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly first values}

open Purelib.Riemann.Readings in
/-- Transport a retained stitched perimeter along equality of its original mesh owner.

The operation uses equality elimination, retaining the same assembly data under the transported index. -/
def cast (equal : first = last) (perimeter : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter
  assembly) : RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter (equal ▸ assembly) := by
  cases equal
  exact perimeter

open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Readings in
/-- Transporting the perimeter preserves all four exact side entries. -/
theorem cast_entries (equal : first = last) (perimeter :
  RectangularObservationAssembly.ObservationMesh.ClippedAssembly.Perimeter assembly) :
    ClippedPerimeterEntries.Perimeter.bottomEntry (ClippedPerimeterTransport.cast equal perimeter) =
      ClippedPerimeterEntries.Perimeter.bottomEntry perimeter ∧
    ClippedPerimeterEntries.Perimeter.rightEntry (ClippedPerimeterTransport.cast equal perimeter) =
      ClippedPerimeterEntries.Perimeter.rightEntry perimeter ∧
    ClippedPerimeterEntries.Perimeter.topEntry (ClippedPerimeterTransport.cast equal perimeter) =
      ClippedPerimeterEntries.Perimeter.topEntry perimeter ∧
    ClippedPerimeterEntries.Perimeter.leftEntry (ClippedPerimeterTransport.cast equal perimeter) =
      ClippedPerimeterEntries.Perimeter.leftEntry perimeter := by
  cases equal
  exact ⟨rfl, rfl, rfl, rfl⟩

end Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterTransport
