module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods

/-! # Retained actual geometry of a primitive-safe direct refinement

The original parent, requested diameter, whole segment bound, sufficient
depth and checked mesh remain the values supplied by the primitive-cover
producer. Their exact factories tie the same original block to the same
mesh. This geometry payload introduces no source, observation, primitive
row or replacement owner.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (uniformParentMesh checkedParentBlock)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- The SAME computed sufficient-refinement geometry indexed by its original parent and actual stored block.

Existing dependent products retain the original diameter, proper interval,
Bounds, selected depth, sufficient-depth certificate and checked mesh.
The whole checked-block factory ties that SAME mesh to the SAME safe.block;
root agreement or endpoint equality is never substituted for this law.
-/
@[expose] def Refinement (parent : CenteredEdge curve differential) (diameter : Rational)
    (positive : 0 < diameter) (safe : EndpointSafeBlock parent) :=
  Σ keptDiameter : {value : Rational // value = diameter},
  Σ bounds : {value : Bounds parent.edge.segment // value = Bounds.build parent.edge.segment ∧
      parent.edge.left.parameter < parent.edge.request.endpoint.parameter},
  Σ chosenDepth : {value : Nat // value = PrimitiveCover.depth parent bounds.val keptDiameter.val},
  Σ enough : PLift (Riemann.Branches.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint keptDiameter.val ≤ chosenDepth.val),
  {mesh : Riemann.Integration.CheckedDirectGeometry.Mesh parent.edge keptDiameter.val chosenDepth.val
      parent.edge.left parent.edge.request.endpoint //
    mesh = uniformParentMesh parent bounds.property.2 keptDiameter.val
      (Eq.mpr (congrArg (fun radius : Rational => 0 < radius) keptDiameter.property) positive)
      chosenDepth.val enough.down ∧ safe.block = checkedParentBlock parent mesh}

namespace Refinement

variable {parent : CenteredEdge curve differential} {requestedDiameter : Rational}
    {positive : 0 < requestedDiameter} {safe : EndpointSafeBlock parent}
variable (retained : Refinement parent requestedDiameter positive safe)

/-- Read the literal input diameter retained before the checked mesh and source observations. -/
@[expose] def diameter : Rational := retained.1.val

/-- The retained diameter is the original requested value. -/
theorem diameter_eq : retained.diameter = requestedDiameter := retained.1.property

/-- Read the SAME once-built original segment bound. -/
@[expose] def bounds : Bounds parent.edge.segment := retained.2.1.val

/-- The bound retains its original complete constructor equation. -/
theorem bounds_eq : retained.bounds = Bounds.build parent.edge.segment := retained.2.1.property.1

include retained in
/-- Read the actual strict original parameter interval used by the original mesh producer. -/
theorem proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter := retained.2.1.property.2

/-- Read the actual common depth selected before the checked block and new Point readings. -/
@[expose] def chosenDepth : Nat := retained.2.2.1.val

/-- The selected depth has the exact original sufficient-refinement factory. -/
theorem depth_eq : retained.chosenDepth = PrimitiveCover.depth parent retained.bounds retained.diameter :=
  retained.2.2.1.property

/-- The SAME selected depth pays the original uniform root-preparation requirement. -/
theorem enough : Riemann.Branches.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.edge.segment parent.edge.left parent.edge.request.endpoint retained.diameter ≤ retained.chosenDepth :=
  retained.2.2.2.1.down

/-- Read the SAME checked mesh, keeping its original parent, diameter, depth and two parameter endpoint indices. -/
@[expose] def mesh : Riemann.Integration.CheckedDirectGeometry.Mesh parent.edge retained.diameter retained.chosenDepth
    parent.edge.left parent.edge.request.endpoint := retained.2.2.2.2.val

/-- The stored mesh has its exact original uniformParentMesh factory, with all original depth and interval witnesses. -/
theorem mesh_eq : retained.mesh = uniformParentMesh parent retained.proper retained.diameter
    (Eq.mpr (congrArg (fun radius : Rational => 0 < radius) retained.diameter_eq) positive)
    retained.chosenDepth retained.enough := retained.2.2.2.2.property.1

/-- The actual stored block was checked from this SAME mesh; its common original segment frames are not inferred. -/
theorem block_eq : safe.block = checkedParentBlock parent retained.mesh := retained.2.2.2.2.property.2

end Refinement

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

end
