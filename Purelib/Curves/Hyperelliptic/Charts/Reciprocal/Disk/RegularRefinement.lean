module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Nat.Subtraction

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)
open Purelib.Data.Nat

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-!
# Refining the actual retained regular-parent area

The existing comparison supplies its cap area and ownership certificates.
Only the new finite subdivision is evaluated. Its unsigned polynomial area
is compared with the retained area using the energy cache's actual bounds.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRefinement

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {totalTarget areaTarget :
    Normalization.InverseRootPolynomial.Coordinate} {floor index depth : Nat}
  {source : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index} {box :
    Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared totalTarget areaTarget floor}
  {retained : Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth prepared.bank}

set_option genInjectivity false in
/-- The unsigned polynomial is the same one used by cap energy. Its total
is specified independently; only area is invariant under the retained sign. -/
structure UnsignedRefinement (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation
  request retained)
    (bounds : Cap.EnergyBounds capSample) (commonDepth : Nat) where
  /-- The shared depth is at least the original coarse depth plus its retained fine depth. -/ later : cover.mesh.depth +
    depth ≤ commonDepth
  /-- The cached complete unsigned primitive increment path at the shared depth. -/ path : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached path uses the same original polynomial and inverse parent at that depth. -/ path_eq : path =
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => capSample.primitive.value.eval
    ((parent.edge.point parameter)⁻¹)) commonDepth 0 1
  /-- The cached summary of this same unsigned path. -/ summary : Path.IncrementArea.Summary path
  /-- The total is the original endpoint primitive difference independently of sheet sign. -/ total_eq : summary.total =
    capSample.primitive.value.eval ((parent.edge.point 1)⁻¹) -
    capSample.primitive.value.eval ((parent.edge.point 0)⁻¹)
  /-- The area is exactly the original anchored unsigned dyadic area. -/ area_eq : summary.area =
    Path.Dyadic.DyadicBoundaryRibbon.dyadicArea
    (fun parameter => capSample.primitive.value.eval ((parent.edge.point parameter)⁻¹) -
      capSample.primitive.value.eval ((parent.edge.point 0)⁻¹)) commonDepth 0 1
  /-- The refined area differs from the original retained cap by at most its original quarter-radius charge. -/
    area_error : Data.Gaussian.Norm.Basic.normSq (summary.area - evaluated.cap.area) ≤
    Rational.Geometric.Basic.quarterRadius (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds) depth

constructive_injectivity UnsignedRefinement

namespace UnsignedRefinement

/-- Sample the original unsigned primitive at the sufficient shared depth and retain its summary with exact endpoint,
area and refinement certificates. -/
def build (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation request retained)
  (bounds : Cap.EnergyBounds capSample)
    (commonDepth : Nat) (later : cover.mesh.depth + depth ≤ commonDepth) :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularRefinement.UnsignedRefinement evaluated bounds commonDepth := by
  let value (parameter : Normalization.InverseRootPolynomial.Coordinate) := capSample.primitive.value.eval
    ((parent.edge.point parameter)⁻¹)
  let path := Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements value commonDepth 0 1
  let summary := Path.IncrementArea.Summary.build path
  have totalEq : summary.total = value 1 - value 0 := by
    rw [summary.total_eq]
    exact Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum value commonDepth 0 1
  have areaEq : summary.area = Path.Dyadic.DyadicBoundaryRibbon.dyadicArea (fun parameter => value parameter - value 0)
    commonDepth 0 1 := by
    rw [summary.area_eq]
    change Path.IncrementArea.pathArea (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements value commonDepth 0 1) = _
    rw [← Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sub_constant value (value 0)]
    exact Path.Dyadic.DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (Gaussian.Basic.sub_self _)
  refine ⟨later, path, rfl, summary, totalEq, areaEq, ?_⟩
  rw [areaEq, evaluated.cap_area_unsigned]
  have estimate := Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_refinement_bound bounds data.boundary
    (cover.mesh.depth + depth)
    (commonDepth - (cover.mesh.depth + depth))
  rw [Subtraction.add_sub_of_le later] at estimate
  exact estimate.trans (quarterRadius_antitone
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale_nonnegative bounds) (Nat.le_add_left depth
    cover.mesh.depth))

end UnsignedRefinement
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRefinement
