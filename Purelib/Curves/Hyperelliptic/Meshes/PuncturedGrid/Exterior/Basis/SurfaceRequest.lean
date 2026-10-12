module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Approximation

open Purelib.Curves

open Purelib.Riemann

public section

/-! One pre-acquisition budget and polynomial threshold for all retained
exterior components, in their original surface order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

set_option genInjectivity false in
/-- One original exterior component with its retained common-basis preparation and paid request. -/
structure Entry (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (coverFloor floor : Nat) where
  /-- The retained original exterior surface component. -/ component :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential
  /-- The common anchor and basis covers for this exact component preparation. -/ retained :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation component.prepared
  /-- The paid common-basis request using those retained covers. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis target
    coefficientTarget coverFloor floor

constructive_injectivity Entry

namespace Entry

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}

/-- Compute the maximum retained component request stage, starting from the supplied floor. -/
@[expose] def maximum : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains :=
  domains) (differential := differential) basis target coefficientTarget coverFloor floor) → Nat
  | [] => floor
  | head :: tail => max head.request.index
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.maximum tail)

end Entry

set_option genInjectivity false in
/-- A complete paid common-basis request on the original ordered exterior components.

A cached local allowance pays the full component count, and exact readback preserves every component and its request. -/
structure Request (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (coverFloor floor : Nat) where
  /-- The cached common allowance for each original exterior component. -/ localTarget :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The local allowance pays four times the original component count. -/ local_eq : localTarget =
    Rational.Budget.Weighted.allowance target (4 * (prepared.components.length :
    Normalization.InverseRootPolynomial.Coordinate))
  /-- The retained local component allowance is strictly positive. -/ positive : 0 < localTarget
  /-- The complete component-count cost fits the requested surface tolerance. -/ paid : (4 * (prepared.components.length
    : Normalization.InverseRootPolynomial.Coordinate)) * localTarget ≤ target
  /-- The retained component requests in the original surface order. -/ entries : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains) (differential :=
    differential) basis localTarget coefficientTarget coverFloor floor)
  /-- The request entries read back exactly the original component list. -/ components_eq : entries.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.component = prepared.components
  /-- The cached common component-request stage. -/ index : Nat
  /-- The cached stage is the maximum of the retained requests and supplied floor. -/ index_eq : index =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.maximum entries

constructive_injectivity Request

namespace Request

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}

/-- The retained request-entry list has exactly the original surface component count. -/
theorem entries_length (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Request prepared
  basis target coefficientTarget coverFloor floor) :
    request.entries.length = prepared.components.length :=
  (Purelib.Data.List.Map.length_map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.component
    request.entries).symm.trans (congrArg List.length request.components_eq)

end Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
