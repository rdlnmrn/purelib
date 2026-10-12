module

import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
public import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
public import Purelib.Integration.Path.JoinedTraceIndices

@[expose] public section

/-! Each piece starts at a retained occurrence of the paired endpoint polygon.
The positional inclusion preserves owners even when coordinates repeat. -/
namespace Purelib.Riemann.Integration.RectangularEndpointPieceOrigins.VertexTrace

open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.JoinedTraceIndices (concatenateEntry)
open Purelib.Integration.Path.PairedEndpointPolygon (pairedEndpointPolygon pairedChord)

variable {Left Right : Type} {count : Nat}
  (first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace Left) (last : Fin (count + 1) →
    Purelib.Integration.Path.JoinedTrace.VertexTrace Right)

open Purelib.Integration
/-- The original endpoint-polygon position where a retained trace piece starts. -/
def pairedEndpointStart (piece : Fin (count + 1)) : Fin ((Path.PairedEndpointPolygon.pairedEndpointPolygon first
  last).rest.length + 1) :=
  (Path.JoinedTraceIndices.concatenateEntry (fun index => Path.PairedEndpointPolygon.pairedChord (first index) (last
    index)) piece).index 0

/-- The retained start position reads the actual first owners of the paired trace piece. -/
theorem pairedEndpointStart_eq (piece : Fin (count + 1)) :
    (Path.PairedEndpointPolygon.pairedEndpointPolygon first last).indexed (pairedEndpointStart first last piece) =
      ((first piece).first, (last piece).first) :=
  (Path.JoinedTraceIndices.concatenateEntry (fun index => Path.PairedEndpointPolygon.pairedChord (first index) (last
    index)) piece).indexed_eq 0

end Purelib.Riemann.Integration.RectangularEndpointPieceOrigins.VertexTrace

namespace Purelib.Riemann.Integration.RectangularEndpointPieceOrigins.PairedEndpointReadingsGeometry

open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPairedEndpointReadings (PairedEndpointReadingsGeometry)

variable {leftColumns leftRows rightColumns rightRows count : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace (OwnedVertex leftGeometry)}
  {last : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace (OwnedVertex rightGeometry)}
  (geometry : PairedEndpointReadingsGeometry first last) (piece : Fin (count + 1))

open Purelib.Riemann
/-- The left owner at a piece's retained start position is its original first owner. -/
theorem pieceStart_left :
    geometry.leftOwners (Integration.RectangularEndpointPieceOrigins.VertexTrace.pairedEndpointStart first last piece) =
      (first piece).first := by
  rw [geometry.left_eq, Integration.RectangularEndpointPieceOrigins.VertexTrace.pairedEndpointStart_eq]

/-- The right owner at a piece's retained start position is its original first owner. -/
theorem pieceStart_right :
    geometry.rightOwners (Integration.RectangularEndpointPieceOrigins.VertexTrace.pairedEndpointStart first last piece)
      =
      (last piece).first := by
  rw [geometry.right_eq, Integration.RectangularEndpointPieceOrigins.VertexTrace.pairedEndpointStart_eq]

/-- The shared coordinate at a piece's retained start is its original first point. -/
theorem pieceStart_point :
    geometry.points (Integration.RectangularEndpointPieceOrigins.VertexTrace.pairedEndpointStart first last piece) =
      (first piece).first.point := by
  rw [← geometry.left_point, pieceStart_left geometry piece]

end Purelib.Riemann.Integration.RectangularEndpointPieceOrigins.PairedEndpointReadingsGeometry
