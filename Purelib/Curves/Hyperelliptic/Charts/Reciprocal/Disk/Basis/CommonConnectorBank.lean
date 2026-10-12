module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Acquire all physical common-interval connectors from one retained reading
bank, preserving their order and the shared numerical threshold. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank

open Purelib.Data

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

/-- Both cached endpoint roots of each original acquired interval lie in its retained padded domain. -/
@[expose] def Inside : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Prop
  | _, .nil, _, _ => True
  | _, .cons _ tail, plans, readings =>
      regular.padded.Contains (readings.1.evaluated.first.root.coordinate * readings.1.evaluated.first.root.coordinate)
        ∧
      regular.padded.Contains (readings.1.evaluated.last.root.coordinate * readings.1.evaluated.last.root.coordinate) ∧
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Inside tail plans.2 readings.2

/-- The ordered dependent bank of actual basis connectors between consecutive original acquired intervals.

Empty and singleton interval lists carry no connector; each remaining entry preserves both adjacent interval owners. -/
@[expose] def Connectors (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat)
  (joinTarget : Normalization.InverseRootPolynomial.Coordinate) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Type
  | _, .nil, _, _ => PUnit
  | _, .cons _ .nil, _, _ => PUnit
  | _, .cons _ (.cons next remaining), plans, readings =>
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector.BasisCommonConnector readings.1 readings.2.1
        coefficients radialDepth joinTarget ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients
          radialDepth joinTarget (.cons next remaining) plans.2 readings.2

/-- Read no new roots or inverse samples. Each connector retains its actual
primitive values and the radial certificate paid by its original join request. -/
@[expose] def connect (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage requests plans) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Inside requests plans readings →
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions basis joinTarget joinFloor requests) →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage requests joins ≤ stage →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth joinTarget
      requests plans readings
  | _, .nil, _, _, _, _, _ => ⟨⟩
  | _, .cons _ .nil, _, _, _, _, _ => ⟨⟩
  | _, .cons _ (.cons next remaining), plans, readings, inside, joins, later =>
      ⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector.BasisCommonConnector.build joins.2.1 readings.1
        readings.2.1 coefficients radialDepth branch
        inside.2.1 inside.2.2.1 ((Nat.Order.le_max_left ..).trans later),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.connect coefficients radialDepth
          branch (.cons next remaining) plans.2 readings.2 inside.2.2 joins.2.2
          ((Nat.Order.le_max_right ..).trans later)⟩

namespace Connectors

variable {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {radialDepth : Nat}

/-- This list is read from the cached connectors in physical interval order. -/
@[expose] def increments : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} →
    {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage requests plans} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth joinTarget
      requests plans readings → List Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _ => []
  | _, .cons _ .nil, _, _, _ => []
  | _, .cons _ (.cons next remaining), _, _, connectors =>
      connectors.1.increment ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors.increments (.cons next
        remaining) connectors.2

end Connectors
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
