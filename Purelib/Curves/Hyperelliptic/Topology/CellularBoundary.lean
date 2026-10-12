module

public import Purelib.Curves.Hyperelliptic.Topology.Cells
import Purelib.Topology.BranchedCover.Double.Attachment
public import Purelib.Topology.Chain.PathBoundary

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology.BranchedCover.Double

open Purelib.Topology.Chain

@[expose] public section

/-!
# Cellular boundary of finite attaching walks

This module turns the explicit face attachments into integral cellular
boundary statements.  Paths are finite inductive objects with exact endpoint
types.  Their vertex boundary telescopes constructively, and every cyclic
hyperelliptic face attachment therefore satisfies `d₁ d₂ = 0` pointwise.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.CellularBoundary

/-- Every odd-degree hyperelliptic face satisfies `d₁ d₂ = 0`. -/
theorem odd_face_boundary_boundary_zero (genus : Nat)
  (face : Attachment.Face)
    (vertex : Cells.OddVertex genus) :
    PathBoundary.wordBoundaryAt Cells.oddEdgeStart Cells.oddEdgeFinish
      (Cells.oddFaceAttachment genus face).edges vertex = 0 := by
  exact PathBoundary.attachment_boundary_zero (Cells.oddFaceAttachment genus face) vertex

/-- Every even-degree hyperelliptic face satisfies `d₁ d₂ = 0`, including at the two separate vertices over infinity. -/
theorem even_face_boundary_boundary_zero (genus : Nat)
  (face : Attachment.Face)
    (vertex : Cells.EvenVertex genus) :
    PathBoundary.wordBoundaryAt Cells.evenEdgeStart Cells.evenEdgeFinish
      (Cells.evenFaceAttachment genus face).edges vertex = 0 := by
  exact PathBoundary.attachment_boundary_zero (Cells.evenFaceAttachment genus face) vertex

end Purelib.Curves.Hyperelliptic.Topology.CellularBoundary

end
