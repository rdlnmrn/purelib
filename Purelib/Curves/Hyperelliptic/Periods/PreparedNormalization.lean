module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedObservationSurface
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.BilinearRelations.Certificate

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound
import Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveInverseTail
import Purelib.Riemann.Integration.PreparedRefinementPrograms
public import Purelib.Curves.Hyperelliptic.Periods.Normalization.TailSchedule
public import Purelib.Riemann.Periods.CurveFirstBilinearRelation
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Integration.ScalarTailLower
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.CurveRawRequest
import Purelib.Riemann.Readings.NamedMatrixActionBound
import Purelib.Riemann.Readings.TailSynchronizedEnergy
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Riemann

public section

/-! Retained finite period acquisition and normalization on the same cycle,
raw-program and inverse owners. A tail presentation retains its actual scalar
source and equivalence; it is not identified with the canonical presentation. -/
namespace Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization

open Purelib.Riemann.Periods.PeriodMatrix

open Purelib.Riemann.Integration.PreparedRefinementPrograms (PeriodCycleBasis)
open Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank (RawRequest rawRequest)

open Purelib.Riemann.Topology.PreparedObservationSurface (ObservationBoxEnergy)
open Purelib.Riemann.Readings.NamedMatrixActionBound (UniformActionBound)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Exact equality of the retained raw period parent with the supplied original period data. -/
@[expose, reducible] def RawParentEq (data raw : PeriodData curve) : Prop := raw = data
/-- Exact equality of the retained inverse parent with the supplied original inverse certificate. -/
@[expose, reducible] def InverseParentEq {data : PeriodData curve}
    (inverse parent : ScaledInverseCertificate data.aMatrix) : Prop := parent = inverse
/-- Exact equality to normalization of the original period data by its supplied inverse. -/
@[expose, reducible] def NormalizedParentEq (data : PeriodData curve)
    (inverse : ScaledInverseCertificate data.aMatrix) (normalized : NormalizedPeriodData curve) : Prop :=
  normalized = NormalizedPeriodData.ofScaledInverse data inverse
/-- Exact equality of a retained matrix with its supplied original matrix. -/
@[expose, reducible] def MatrixParentEq (matrix parent : NamedMatrix genus) : Prop := parent = matrix
/-- Exact equality of a retained coherent name with its supplied original name. -/
@[expose, reducible] def NameParentEq (name parent : CoherentNamed) : Prop := parent = name
/-- Exact equality of the retained omega matrix with the original normalized period matrix. -/
@[expose, reducible] def OmegaParentEq (normalized : NormalizedPeriodData curve) (omega : NamedMatrix genus) : Prop :=
  omega = normalized.omega
/-- Exact equality of the retained channel table with the original normalized omega table. -/
@[expose, reducible] def TableParentEq (normalized : NormalizedPeriodData curve)
    (table : Gaussian.Table.Basic.ChannelTable) : Prop := table = normalized.omegaTable

set_option genInjectivity false in
/-- Physical original parents and the named finite calculations are cached
with exact specification equalities. No independent cycle or inverse is chosen. -/
structure Normalization (data : PeriodData curve)
    (inverse : ScaledInverseCertificate data.aMatrix) where
  /-- The retained original raw period data. -/ raw : PeriodData curve
  /-- The cached raw period data has its exact original specification. -/ raw_eq : RawParentEq data raw
  /-- The retained original supplied inverse certificate. -/ inverseParent : ScaledInverseCertificate data.aMatrix
  /-- The cached supplied inverse certificate has its exact original specification. -/ inverse_eq : InverseParentEq
    inverse inverseParent
  /-- The retained original a-period matrix. -/ a : NamedMatrix genus
  /-- The cached a-period matrix has its exact original specification. -/ a_eq : MatrixParentEq data.aMatrix a
  /-- The retained original b-period matrix. -/ b : NamedMatrix genus
  /-- The cached b-period matrix has its exact original specification. -/ b_eq : MatrixParentEq data.bMatrix b
  /-- The retained original inverse scalar name. -/ scalar : CoherentNamed
  /-- The cached inverse scalar name has its exact original specification. -/ scalar_eq : NameParentEq inverse.scalar
    scalar
  /-- The retained original inverse adjugate matrix. -/ adjugate : NamedMatrix genus
  /-- The cached adjugate matrix has its exact original specification. -/ adjugate_eq : MatrixParentEq inverse.adjugate
    adjugate
  /-- The retained shared reciprocal of the original inverse scalar. -/ reciprocal : CoherentNamed
  /-- The cached reciprocal scalar has its exact original specification. -/ reciprocal_eq : NameParentEq (inverseScalar
    inverse) reciprocal
  /-- The retained shared product of the retained adjugate and b-matrix. -/ numerator : NamedMatrix genus
  /-- The cached adjugate-times-b product has its exact original specification. -/ numerator_eq : MatrixParentEq
    (matrixMul adjugate b) numerator
  /-- The retained normalized period data on the same original raw and inverse parents. -/ normalized :
    NormalizedPeriodData curve
  /-- The cached normalized parent data has its exact original specification. -/ normalized_eq : NormalizedParentEq data
    inverse normalized
  /-- The retained cached normalized period matrix. -/ omega : NamedMatrix genus
  /-- The cached omega matrix has its exact original specification. -/ omega_eq : OmegaParentEq normalized omega
  /-- The retained cached channel table for the retained omega matrix. -/ table : Gaussian.Table.Basic.ChannelTable
  /-- The cached omega channel table has its exact original specification. -/ table_eq : TableParentEq normalized table

constructive_injectivity Normalization

namespace Normalization

/-- The shared factors are evaluated once and used by every normalized entry. -/
@[expose] def realize (data : PeriodData curve) (inverse : ScaledInverseCertificate data.aMatrix) :
    Normalization data inverse :=
  let a := data.aMatrix
  let b := data.bMatrix
  let scalar := ScaledInverseCertificate.scalar (matrix := a) inverse
  let adjugate := ScaledInverseCertificate.adjugate (matrix := a) inverse
  let reciprocal := Gaussian.Name.Coherent.CoherentNamed.div
    (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 1) scalar (ScaledInverseCertificate.scalarApart (matrix := a)
      inverse)
  let numerator := matrixMul adjugate b
  let normalized : NormalizedPeriodData curve :=
    { toPeriodData := data, aInverse := inverse }
  let omega := SquareMatrix.matrixOfFn fun row column =>
    Gaussian.Name.Coherent.CoherentNamed.mul (numerator row column) reciprocal
  let table : Gaussian.Table.Basic.ChannelTable := ⟨PeriodData.matrixChannels omega⟩
  { raw := data, raw_eq := rfl
    inverseParent := inverse, inverse_eq := rfl
    a := a, a_eq := rfl, b := b, b_eq := rfl
    scalar := scalar, scalar_eq := rfl, adjugate := adjugate, adjugate_eq := rfl
    reciprocal := reciprocal, reciprocal_eq := rfl, numerator := numerator, numerator_eq := rfl
    normalized := normalized, normalized_eq := rfl
    omega := omega, omega_eq := rfl, table := table, table_eq := rfl }

variable {data : PeriodData curve} {inverse : ScaledInverseCertificate data.aMatrix}
    (owner : Normalization data inverse)

/-- The cached omega matrix is the matrix of normalization by the exact original inverse certificate. -/
theorem omega_spec : owner.omega = (NormalizedPeriodData.ofScaledInverse data inverse).omega :=
  owner.omega_eq.trans (congrArg NormalizedPeriodData.omega owner.normalized_eq)

/-- Each cached omega entry equals the corresponding entry of the original normalized period data. -/
theorem omega_readback (row column : Fin genus) :
    owner.omega row column = (NormalizedPeriodData.ofScaledInverse data inverse).omega row column :=
  congrArg (fun matrix : NamedMatrix genus => matrix row column) owner.omega_spec

/-- The retained normalized data project to exactly the original raw period data. -/
theorem raw_readback : owner.normalized.toPeriodData = data :=
  (congrArg NormalizedPeriodData.toPeriodData owner.normalized_eq).trans
    (NormalizedPeriodData.ofScaledInverse_periodData data inverse)

/-- The retained normalized inverse is heterogeneously equal to the exact original supplied inverse. -/
theorem inverse_readback : HEq owner.normalized.aInverse inverse := by
  rw [owner.normalized_eq]
  exact heq_of_eq (NormalizedPeriodData.ofScaledInverse_aInverse data inverse)

/-- The actual inverse source may be a certified finite tail; this returns
its original operational equivalence, without replacing its representation. -/
@[expose] def scalar_equivalent : NamedEquivalent (canonicalInverseScalar data.aMatrix).name owner.scalar.name := by
  rw [owner.scalar_eq]
  have equivalence := owner.inverseParent.canonicalScalarEquivalent
  rw [owner.inverse_eq] at equivalence
  exact equivalence

/-- The retained adjugate times a-matrix is operationally equivalent to the same retained scalar identity. -/
@[expose] def left_identity (row column : Fin genus) :
    NamedEquivalent (matrixMul owner.adjugate owner.a row column).name
      (scaleIdentity owner.scalar row column).name := by
  rw [owner.adjugate_eq, owner.a_eq, owner.scalar_eq]
  have identity := owner.inverseParent.left_identity row column
  rw [owner.inverse_eq] at identity
  exact identity

/-- The retained a-matrix times adjugate is operationally equivalent to the same retained scalar identity. -/
@[expose] def right_identity (row column : Fin genus) :
    NamedEquivalent (matrixMul owner.a owner.adjugate row column).name
      (scaleIdentity owner.scalar row column).name := by
  rw [owner.a_eq, owner.adjugate_eq, owner.scalar_eq]
  have identity := owner.inverseParent.right_identity row column
  rw [owner.inverse_eq] at identity
  exact identity

/-- Refine one retained omega entry using the shared cached channel table and supplied positive target. -/
@[expose] def refinedEntry (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : Gaussian.Name.Basic.Named :=
  Gaussian.Table.Request.sharedName owner.table.channels (owner.omega row column) target positive

/-- The refined entry is exactly the original normalized-data refinement at the same target. -/
theorem refinedEntry_readback (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : owner.refinedEntry target positive row column =
      owner.normalized.refinedOmegaEntry target positive row column := by
  rw [refinedEntry, owner.table_eq, owner.omega_eq]
  rfl

/-- Prepare one entry using the retained normalization's shared table and factors.

The actual refined name and its ball are each computed once. The original raw
and inverse parents remain on the normalization; the result retains their exact
channel and entry indices without reconstructing that owner. -/
@[expose] def prepareEntry (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : Gaussian.Table.Request.PreparedEntry
      owner.table.channels (owner.omega row column) target positive :=
  Gaussian.Table.Request.prepareEntry owner.table.channels (owner.omega row column) target positive

/-- The prepared name is the original retained normalization's refinement. -/
theorem prepareEntry_name (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : (owner.prepareEntry target positive row column).name =
      owner.refinedEntry target positive row column :=
  (owner.prepareEntry target positive row column).name_eq

/-- The prepared name reads back to the original normalized-data refinement. -/
theorem prepareEntry_name_readback (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : (owner.prepareEntry target positive row column).name =
      owner.normalized.refinedOmegaEntry target positive row column :=
  (owner.prepareEntry_name target positive row column).trans
    (owner.refinedEntry_readback target positive row column)

/-- The retained ball is exactly the original normalized-entry request's enclosure. -/
theorem prepareEntry_ball_readback (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : (owner.prepareEntry target positive row column).ball =
      (owner.normalized.refinedOmegaEntry target positive row column).process.ball
        (owner.normalized.refinedOmegaEntry target positive row column).state :=
  (owner.prepareEntry target positive row column).ball_eq.trans
    (congrArg (fun name : Gaussian.Name.Basic.Named => name.process.ball name.state)
      (owner.prepareEntry_name_readback target positive row column))

/-- The prepared center equals the original normalized omega center. -/
theorem prepareEntry_center_readback (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : (owner.prepareEntry target positive row column).center =
      owner.normalized.omegaCenter target positive row column :=
  congrArg Gaussian.Enclosure.Ball.center (owner.prepareEntry_ball_readback target positive row column)

/-- The prepared radius equals the original normalized omega squared radius. -/
theorem prepareEntry_radiusSq_readback (target : Fraction.Rational) (positive : 0 < target)
    (row column : Fin genus) : (owner.prepareEntry target positive row column).radiusSq =
      owner.normalized.omegaRadiusSq target positive row column :=
  congrArg Gaussian.Enclosure.Ball.radiusSq (owner.prepareEntry_ball_readback target positive row column)

end Normalization

/-- The original prepared-cycle bank's raw request at stage floor zero. -/
@[expose, reducible] def Raw (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) :=
  RawRequest bank 0
/-- The retained lower-bound action on the original raw period request. -/
@[expose, reducible] def Action {bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve}
  (raw : Raw bank) := Hyperelliptic.Periods.Action.LowerBound.ActionLower raw
/-- The original polynomial observation geometry for the curve and its genus. -/
@[expose, reducible] def Geometry (curve : Hyperelliptic.Basic.HyperellipticCurve genus) := ObservationBoxEnergy
  curve.polynomial genus
/-- A uniform action bound on the original period bank's a-matrix. -/
@[expose, reducible] def AAction (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) :=
  UniformActionBound bank.periodData.aMatrix
/-- A retained scalar-tail separation certificate for the original a-matrix. -/
@[expose, reducible] def InverseTail (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank
  curve) := ScalarTailSeparationCertificate bank.periodData.aMatrix
/-- Exact identity of the supplied physical tail with the original action-derived tail certificate. -/
@[expose, reducible] def TailOwnerEq {bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank
  curve} {raw : Raw bank}
    (action : Action raw) (inverseTail : InverseTail bank) : Prop :=
  inverseTail = (Hyperelliptic.Periods.Normalization.CurveInverseTail.ActionLower.scalarTailLower
    action).toScalarTailSeparationCertificate
/-- The first bilinear-relation certificate on the original raw period bank. -/
@[expose, reducible] def PreBilinear (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank
  curve) :=
  BilinearRelations.Certificate.PreNormalizationCertificate bank.periodData
/-- The controlled normalized-energy certificate on the original period data and retained physical inverse tail. -/
@[expose, reducible] def ControlledEnergy (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank
  curve) (inverseTail : InverseTail bank) :=
  Hyperelliptic.Integration.Energy.Prepared.TailControlledCertificate bank.periodData inverseTail

set_option genInjectivity false in
/-- Original acquisition parents, raw action, comparison, inverse tail and
energy remain attached to one supplied prepared-cycle bank. -/
structure PreparedOwner (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) where
  /-- The raw request on the original prepared-cycle bank. -/ raw : Raw bank
  /-- The retained action lower bound on that exact raw request. -/ action : Action raw
  /-- The original curve observation geometry. -/ geometry : Geometry curve
  /-- The uniform action bound on the original a-period matrix. -/ aBound : AAction bank
  /-- The actual retained physical inverse tail. -/ inverseTail : InverseTail bank
  /-- The retained tail is exactly the original action-derived certificate. -/ inverseTail_eq : TailOwnerEq action
    inverseTail
  /-- The bilinear certificate on the same original raw period bank. -/ preBilinear : PreBilinear bank
  /-- The controlled normalized energy attached to the same retained inverse tail. -/ energy : ControlledEnergy bank
    inverseTail

constructive_injectivity PreparedOwner

namespace PreparedOwner

/-- Acquire the original raw request, action, inverse tail, bilinear certificate and controlled energy once on the
supplied prepared-cycle bank. -/
@[expose] def realize (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) :
  PreparedOwner bank :=
  let raw := rawRequest bank 0
  let action := Hyperelliptic.Periods.Action.LowerBound.ActionLower.build raw
  let geometry := Topology.PreparedObservationSurface.curveObservationBoxEnergy curve
  let aBound := UniformActionBound.build bank.periodData.aMatrix
  let inverseTail := (Hyperelliptic.Periods.Normalization.CurveInverseTail.ActionLower.scalarTailLower
    action).toScalarTailSeparationCertificate
  { raw := raw, action := action, geometry := geometry, aBound := aBound
    inverseTail := inverseTail, inverseTail_eq := rfl
    preBilinear := Periods.CurveFirstBilinearRelation.PairedPeriodBank.preNormalization bank
    energy := (Hyperelliptic.Periods.Normalization.TailSchedule.tailScheduleSupplied
      raw action geometry aBound inverseTail rfl).toTailControlledCertificate }

end PreparedOwner

/-- The supplied period data belong to exactly the original prepared-cycle bank. -/
@[expose, reducible] def PeriodOwnerEq (data : PeriodData curve) (bank :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) : Prop :=
  data = bank.periodData
/-- The supplied cycle basis is exactly the basis of the original ordered prepared-cycle bank. -/
@[expose, reducible] def CycleOwnerEq (basis : PeriodCycleBasis curve) (bank :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) : Prop :=
  basis = PeriodCycleBasis.ofOrdered bank

set_option genInjectivity false in
/-- Supplied certificates retain their original owners; automatic acquisition
retains the actual prepared bank and finite comparison parents as executable data. -/
inductive Acquisition (data : PeriodData curve) (basis : PeriodCycleBasis curve) : Type _ where
  /-- The period and cycle certificates were supplied directly. -/ | supplied
  /-- The actual prepared-cycle bank and acquisition owner are retained with exact period and cycle-parent identities.
  -/
  | prepared (bank : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (owner :
    PreparedOwner bank)
      (periods_eq : PeriodOwnerEq data bank) (cycles_eq : CycleOwnerEq basis bank)

constructive_injectivity Acquisition

end Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization
