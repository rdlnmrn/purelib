module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Table.CCL.Request
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.BilinearRelations.Certificate
import Purelib.Topology.Surface.CellularHomology
import Purelib.Curves.Hyperelliptic.Topology.Cells
public import Purelib.Curves.Hyperelliptic.Topology.Profile

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Topology.BranchProfile
import Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology
public import Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization

public import Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Readings.ClearDifferentialObservations
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.PreparedStokes
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Periods.CurveFirstBilinearRelation
import Purelib.Curves.Hyperelliptic.Periods.Normalization.TailSchedule
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Topology.BranchedCover
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Approximation.Matrix
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# The finite hyperelliptic period theorem package

This module assembles the constructive conclusions proved by the finite
topology and persistent-integration layers.  The cell complex, Euler
characteristic, genus, cellular quotient, and symplectic basis are computed
from the curve's degree shape.  The analytic layer constructs its lifted path traces, algebraic observation
programs, fraction-free inverse and finite bilinear witnesses internally from
the curve, retaining their explicit certificates.
-/

namespace Purelib.Riemann.Periods.PeriodTheorem

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm

section
open Purelib.Curves.Hyperelliptic
/-- The odd-degree cell complex and branch-count model have equal vertex, edge and face counts. -/
@[expose] def OddCountAgreement (genus : Nat) : Prop :=
  (Topology.Cells.oddCellComplex genus).vertices.length =
      (Topology.BranchProfile.oddDegreeModel genus).vertices.length /\
    (Topology.Cells.oddCellComplex genus).edges.length =
      (Topology.BranchProfile.oddDegreeModel genus).edges.length /\
    (Topology.Cells.oddCellComplex genus).faces.length =
      (Topology.BranchProfile.oddDegreeModel genus).faces.length

/-- The even-degree cell complex and branch-count model have equal vertex, edge and face counts. -/
@[expose] def EvenCountAgreement (genus : Nat) : Prop :=
  (Topology.Cells.evenCellComplex genus).vertexCount =
      (Topology.BranchProfile.evenDegreeModel genus).vertices.length /\
    (Topology.Cells.evenCellComplex genus).edges.length =
      (Topology.BranchProfile.evenDegreeModel genus).edges.length /\
    (Topology.Cells.evenCellComplex genus).faces.length =
      (Topology.BranchProfile.evenDegreeModel genus).faces.length

end

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Cell-count agreement and cellular homology for the curve's actual degree shape.

The odd and even constructors retain their respective degree equation and original homology certificate, rather than
identifying the two cellular models. -/
inductive TopologyCertificate {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) : Type
  /-- The original odd-degree equation, matching cell counts and symplectic homology certificate. -/ | odd
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
      (cellCounts : OddCountAgreement genus)
      (homology : Topology.OddSymplecticHomology.Certificate genus)
  /-- The original even-degree equation, matching cell counts and cellular homology certificate. -/ | even
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
      (cellCounts : EvenCountAgreement genus)
      (homology : Topology.EvenCellularHomology.Certificate genus)

constructive_injectivity TopologyCertificate

open Purelib.Curves.Hyperelliptic in
/-- Construct the cellular topology certificate from the curve's retained odd or even degree witness. -/
@[expose] def topologyCertificate {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    TopologyCertificate curve := by
  cases shape : curve.degreeShape with
  | odd degreeEqual =>
      exact .odd degreeEqual
        (by
          unfold OddCountAgreement
          exact Topology.Cells.oddCellComplex_matches_countModel genus)
        (Topology.OddSymplecticHomology.certificate genus)
  | even degreeEqual =>
      exact .even degreeEqual
        (by
          unfold EvenCountAgreement
          exact Topology.Cells.evenCellComplex_matches_countModel genus)
        (Topology.EvenCellularHomology.certificate genus)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- Period data with its exact geometric basis realization, inverse and energy certificate.

The pre-normalization bilinear relation and scaled inverse belong to the same retained period data; the energy
certificate is indexed by that precise inverse normalization. -/
structure AnalyticCertificate {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (basis : PreparedRefinementPrograms.PeriodCycleBasis curve) where
  /-- The original period programs and their exact geometric cycle family. -/ periodData : PeriodData curve
  /-- Explicit realization of the retained basis cycles by those original period-data cycles. -/ cycles_realization :
    PreparedRefinementPrograms.SymplecticCycleRealization curve
      periodData.cycles basis.cycles
  /-- The bilinear relation before normalization for the same period-data owner. -/ preBilinear :
    Riemann.BilinearRelations.Certificate.PreNormalizationCertificate periodData
  /-- The scaled inverse certificate for the original A-period matrix. -/ aInverse : ScaledInverseCertificate
    periodData.aMatrix
  /-- Energy positivity indexed by the exact retained inverse normalization. -/
  energy : Curves.Hyperelliptic.Integration.Energy.Certificate
    (NormalizedPeriodData.ofScaledInverse periodData aInverse)

constructive_injectivity AnalyticCertificate

namespace AnalyticCertificate

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration
/-- Read the retained scaled inverse of the original A-period matrix. -/
@[expose] def inverse {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    ScaledInverseCertificate analytic.periodData.aMatrix :=
  analytic.aInverse

/-- Normalize the original period data with the exact retained scaled inverse. -/
@[expose] def normalized {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) : NormalizedPeriodData curve :=
  NormalizedPeriodData.ofScaledInverse analytic.periodData analytic.inverse

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Integration in
/-- Transport the retained energy certificate to the exact normalized period-data readback. -/
@[expose] def normalizedEnergy {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    Curves.Hyperelliptic.Integration.Energy.Certificate analytic.normalized := by
  simpa only [normalized, inverse] using analytic.energy

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Combine the retained pre-normalization relation and normalized energy certificate. -/
@[expose] def bilinear {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    BilinearRelations.Certificate analytic.normalized where
  preNormalization := analytic.preBilinear
  energy := analytic.normalizedEnergy

end AnalyticCertificate

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration
/-- The exact cached normalization owner of the retained period data and scaled inverse. -/
@[expose, reducible] def NormalizationOwner {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) :=
  Periods.PreparedNormalization.Normalization analytic.periodData analytic.inverse

/-- The acquisition evidence for the original period data and geometric basis. -/
@[expose, reducible] def AcquisitionOwner {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {basis : PreparedRefinementPrograms.PeriodCycleBasis curve}
    (analytic : AnalyticCertificate curve basis) :=
  Periods.PreparedNormalization.Acquisition analytic.periodData basis

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- A geometric period basis with retained topology, analytic certificates and normalization caches.

The result links its original basis to the same period data, preserves the cellular Euler characteristic, and records
the exact normalization and acquisition owners used by subsequent requests. -/
structure Result {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The retained geometric period-cycle basis of this curve. -/ basis : PreparedRefinementPrograms.PeriodCycleBasis
    curve
  /-- The degree-specific cell-count and homology certificate of this curve. -/ topology : TopologyCertificate curve
  /-- The cellular Euler characteristic equals two minus twice the genus. -/ eulerCharacteristic :
    curve.cellModel.eulerCharacteristic = (2 : Int) - 2 * genus
  /-- The analytic certificate indexed by this exact retained basis. -/ analytic : AnalyticCertificate curve basis
  /-- The retained normalization cache of the analytic period data and inverse. -/ normalization : NormalizationOwner
    analytic :=
      Periods.PreparedNormalization.Normalization.realize
        analytic.periodData analytic.inverse
  /-- Evidence identifying supplied or actually prepared period-data acquisition. -/ acquisition : AcquisitionOwner
    analytic := .supplied

constructive_injectivity Result

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Package a supplied geometric basis and its analytic certificate with the curve's cellular topology.

The supplied period data and basis realization are retained unchanged; normalization is realized from their existing
inverse, and acquisition records supplied data. -/
@[expose] def riemann_period_theorem_of_basis_certificates {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (basis : PreparedRefinementPrograms.PeriodCycleBasis curve)
    (analytic : AnalyticCertificate curve basis) : Result curve where
  basis := basis
  topology := topologyCertificate curve
  eulerCharacteristic := curve.cellModel_eulerCharacteristic
  analytic := analytic

section
open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Riemann.Integration
/-- Construct a period result from one retained ordered bank and its matching analytic certificates.

The bilinear relation, determinant tail separation and energy certificate all refer to that bank's exact period data and
inverse normalization. -/
@[expose] def riemann_period_theorem_of_retained_bank {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (bank : Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve)
    (preBilinear : Riemann.BilinearRelations.Certificate.PreNormalizationCertificate bank.periodData)
    (inverseTail : ScalarTailSeparationCertificate bank.periodData.aMatrix)
    (energy : Curves.Hyperelliptic.Integration.Energy.Certificate
      (NormalizedPeriodData.ofScaledInverse bank.periodData inverseTail.toScaledInverseCertificate)) :
    Result curve :=
  riemann_period_theorem_of_basis_certificates curve
    (.ofOrdered bank)
    { periodData := bank.periodData
      cycles_realization := PreparedRefinementPrograms.retainedBank_realization bank
      preBilinear := preBilinear, aInverse := inverseTail.toScaledInverseCertificate, energy := energy }

/-- Construct the canonical ordered-bank result from matching supplied bilinear, inverse-tail and energy certificates.
-/
@[expose] def riemann_period_theorem_of_automatic_standard_tail
    {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (preBilinear : Riemann.BilinearRelations.Certificate.PreNormalizationCertificate
      (PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (inverseTail : ScalarTailSeparationCertificate
      (PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (energy : Curves.Hyperelliptic.Integration.Energy.Certificate
      (NormalizedPeriodData.ofScaledInverse
        (PreparedRefinementPrograms.automaticStandardPeriodData curve)
        inverseTail.toScaledInverseCertificate)) :
    Result curve :=
  let bank := Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve
  riemann_period_theorem_of_retained_bank bank preBilinear inverseTail energy

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- Construct the canonical ordered-bank result from inverse-tail and tail-controlled surface energy evidence.

The pre-normalization relation is derived from the same retained bank, while the supplied surface certificate provides
energy at its exact inverse normalization. -/
@[expose] def riemann_period_theorem_of_automatic_standard_tailControlled
    {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (inverseTail : ScalarTailSeparationCertificate
      (PreparedRefinementPrograms.automaticStandardPeriodData curve).aMatrix)
    (surfaceEnergy : Energy.Prepared.TailControlledCertificate
      (PreparedRefinementPrograms.automaticStandardPeriodData curve) inverseTail) :
    Result curve :=
  let bank := Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve
  riemann_period_theorem_of_retained_bank bank
    (CurveFirstBilinearRelation.PairedPeriodBank.preNormalization bank)
    inverseTail surfaceEnergy.toEnergyCertificate

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- Matching inverse-tail and surface-energy certificates for the canonical period data.

The surface certificate retains the same determinant separation witness used by the scaled inverse, keeping its tail
control bound to that normalization. -/
structure PreparedCertificate {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The retained scalar separation witness for the canonical A-period determinant. -/ inverseTail :
    ScalarTailSeparationCertificate
    (PreparedRefinementPrograms.automaticStandardPeriodData curve).aMatrix
  /-- Tail-controlled energy indexed by the same canonical period data and inverse-tail witness. -/ surfaceEnergy :
    Energy.Prepared.TailControlledCertificate
    (PreparedRefinementPrograms.automaticStandardPeriodData curve)
    inverseTail

constructive_injectivity PreparedCertificate

open Purelib.Curves.Hyperelliptic in
/-- Prepare one canonical period bank and read both analytic certificates from its retained normalization owner. -/
@[expose] def PreparedCertificate.ofCurve {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    PreparedCertificate curve :=
  let bank := Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve
  let owner := Periods.PreparedNormalization.PreparedOwner.realize bank
  { inverseTail := owner.inverseTail, surfaceEnergy := owner.energy }

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Prepare a curve's period result with one retained ordered bank and normalization owner.

The basis, bilinear relation, inverse tail and energy all come from these exact caches; the acquisition certificate
records the actual prepared bank and owner with their readback identities. -/
@[expose] def riemann_period_theorem {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) : Result curve :=
  let bank := Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve
  let owner := Periods.PreparedNormalization.PreparedOwner.realize bank
  let basis := PreparedRefinementPrograms.PeriodCycleBasis.ofOrdered bank
  let analytic : AnalyticCertificate curve basis :=
    { periodData := bank.periodData
      cycles_realization := PreparedRefinementPrograms.retainedBank_realization bank
      preBilinear := owner.preBilinear
      aInverse := owner.inverseTail.toScaledInverseCertificate
      energy := owner.energy.toEnergyCertificate }
  { basis := basis, topology := topologyCertificate curve
    eulerCharacteristic := curve.cellModel_eulerCharacteristic, analytic := analytic
    acquisition := .prepared bank owner rfl rfl }

/-! ## Unconditional genus-zero case -/

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Retain the genus-zero cycle family with empty A- and B-period program families. -/
@[expose] def genusZeroPeriodData (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) : PeriodData curve where
  cycles := cycles
  aProgram := fun differential => Fin.elim0 differential
  bProgram := fun differential => Fin.elim0 differential

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
/-- Certify the empty A-matrix determinant with the exact positive lower bound one. -/
@[expose] def genusZeroInverseLower (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) :
    ScalarCandidateLowerCertificate
      (genusZeroPeriodData curve cycles).aMatrix where
  lowerSq := 1
  positive := by decide
  sample_lower := by
    intro index
    change (1 : Coordinate) <=
      Data.Gaussian.Norm.Basic.normSq 1
    rw [Norm.Basic.normSq_one]

section
open Purelib.Curves.Hyperelliptic
open Purelib.Geometry.Path.Gaussian
/-- Build the scaled inverse certificate for the empty A-period matrix. -/
@[expose] def genusZeroInverse (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) :
    ScaledInverseCertificate (genusZeroPeriodData curve cycles).aMatrix :=
  (genusZeroInverseLower curve cycles).toScaledInverseCertificate

/-- Normalize the genus-zero period data with its exact empty-matrix inverse. -/
@[expose] def genusZeroNormalized (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) : NormalizedPeriodData curve where
  toPeriodData := genusZeroPeriodData curve cycles
  aInverse := genusZeroInverse curve cycles

end

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Certify the genus-zero bilinear relation using the empty row and nonzero-vector index types. -/
@[expose] def genusZeroBilinearCertificate (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) :
    BilinearRelations.Certificate
  (genusZeroNormalized curve cycles) where
  preNormalization :=
    { stokesClosure :=
        { closed := fun row => Fin.elim0 row } }
  energy :=
    { certify := fun _vector nonzero => Fin.elim0 nonzero.index }

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Expose the genus-zero bilinear relations from their retained empty-dimensional certificate. -/
@[expose] def genusZeroBilinear (curve : Basic.HyperellipticCurve 0)
    (cycles : Lifted.Family.PairedCycleRefinements 2 0) :
    BilinearRelationsCertificate (genusZeroNormalized curve cycles) :=
  (genusZeroBilinearCertificate curve cycles).toBilinearRelations

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Riemann.Integration in
/-- Construct the genus-zero period result with its original raw symplectic basis and empty analytic data.

The geometric cycles and cellular topology remain present; the empty differential indices supply the realization and
bilinear certificates without preparing positive-dimensional period entries. -/
@[expose] def riemann_period_theorem_genus_zero
    (curve : Basic.HyperellipticCurve 0) : Result curve := by
  let basis := PreparedRefinementPrograms.PeriodCycleBasis.raw (BranchCutLifts.symplecticBasis curve)
  let normalized := genusZeroNormalized curve basis.cycles
  let bilinear := genusZeroBilinearCertificate curve basis.cycles
  let analytic : AnalyticCertificate curve basis :=
    { periodData := normalized.toPeriodData
      cycles_realization :=
        PreparedRefinementPrograms.SymplecticCycleRealization.empty rfl _ _
      preBilinear := bilinear.preNormalization
      aInverse := normalized.aInverse
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse] using bilinear.energy }
  exact
    { basis := basis
      topology := topologyCertificate curve
      eulerCharacteristic := curve.cellModel_eulerCharacteristic
      analytic := analytic }

namespace Result

section
open Purelib.Curves.Hyperelliptic
/-- Read normalized period data from the retained normalization cache. -/
@[expose] def normalized {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve) :
    NormalizedPeriodData curve := result.normalization.normalized

/-- The cached normalization equals the analytic certificate's exact normalized period data. -/
theorem normalized_readback {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve) :
    result.normalized = result.analytic.normalized := result.normalization.normalized_eq

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- The energy certificate type at the result's retained normalized owner. -/
@[expose, reducible] def CachedEnergy {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve) :=
  Curves.Hyperelliptic.Integration.Energy.Certificate result.normalized

open Purelib in
open Purelib.Curves.Hyperelliptic in
/-- The bilinear certificate type at the result's retained normalized owner. -/
@[expose, reducible] def CachedBilinear {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve)
  :=
  BilinearRelations.Certificate result.normalized

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- Transport the analytic energy certificate to the retained normalized cache by its exact readback identity. -/
@[expose] def cachedEnergy {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve) :
    CachedEnergy result := by
  change Curves.Hyperelliptic.Integration.Energy.Certificate result.normalized
  exact result.normalized_readback.symm ▸ result.analytic.normalizedEnergy

open Purelib in
open Purelib.Curves.Hyperelliptic in
/-- Transport the analytic bilinear certificate to the retained normalized cache by its exact readback identity. -/
@[expose] def cachedBilinear {genus : Nat} {curve : Basic.HyperellipticCurve genus} (result : Result curve) :
    CachedBilinear result := by
  change BilinearRelations.Certificate result.normalized
  exact result.normalized_readback.symm ▸ result.analytic.bilinear

open Purelib.Curves.Hyperelliptic in
/-- The retained branch configuration has exactly the polynomial's degree many sites. -/
theorem branchPointCount {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) :
    result.basis.model.family.cuts.configuration.branches.siteCount =
      curve.polynomial.natDegree :=
  result.basis.model.family.cuts.configuration.branches.count_eq

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.CCL.Transducer in
/-- Advancing a retained branch-point name produces the requested prefix length and extends its original output. -/
theorem branchPointRequest {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (index : BranchIsolation.Data.Index
      result.basis.model.family.cuts.configuration.branches)
    (count : Nat) :
    (BranchIsolation.Data.name
        result.basis.model.family.cuts.configuration.branches index).machine.emitted.IsPrefix
      (Machine.Advance.advance
        (BranchIsolation.Data.name
          result.basis.model.family.cuts.configuration.branches index).machine count).emitted /\
    (Machine.Advance.advance
      (BranchIsolation.Data.name
        result.basis.model.family.cuts.configuration.branches index).machine count).emitted.length = count :=
  result.basis.model.family.cuts.configuration.branches.name_productive index count

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the original branch-cut cycle refinement at its retained genus-plus-one index. -/
@[expose] def branchCutLift {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) (index : Fin (genus + 1)) :
    Lifted.Refinement.LiftedCycleRefinement 2 :=
  result.basis.model.family.cycleAt index

open Purelib.Curves.Hyperelliptic in
/-- Each retained branch-cut lift returns to its starting sheet at every refinement. -/
theorem branchCutLift_returns_to_startingSheet {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (index : Fin (genus + 1)) (refinement : Nat) :
    ((result.branchCutLift index).liftedPath refinement).path.sheetTransport.forward
        ((result.branchCutLift index).liftedPath refinement).basepoint.sheet =
      ((result.branchCutLift index).liftedPath refinement).basepoint.sheet :=
  result.basis.model.family.returns_to_startingSheet index refinement

section
open Purelib.Curves.Hyperelliptic
open Purelib.Topology.Surface
/-- Two original A-basis traces have zero cellular intersection. -/
theorem model_a_intersection {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CellularHomology.intersection
      (result.basis.model.aTrace left) (result.basis.model.aTrace right) = 0 :=
  result.basis.model.a_a left right

/-- Two original B-basis traces have zero cellular intersection. -/
theorem model_b_intersection {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CellularHomology.intersection
      (result.basis.model.bTrace left) (result.basis.model.bTrace right) = 0 :=
  result.basis.model.b_b left right

/-- The original A/B trace intersection is the Kronecker pairing on their retained indices. -/
theorem model_a_b_intersection {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CellularHomology.intersection
      (result.basis.model.aTrace left) (result.basis.model.bTrace right) =
        if left = right then 1 else 0 :=
  result.basis.model.a_b left right

end

open Purelib.Curves.Hyperelliptic in
/-- Read the analytic normalization's original unnormalized period data. -/
@[expose] def periodData {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) : PeriodData curve :=
  result.analytic.normalized.toPeriodData

section
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
/-- Read the cached left scaled-inverse identity in the original period-matrix names. -/
@[expose] def aInverse_left_identity {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (row column : Fin genus) :
    Equivalence.NamedEquivalent
      (matrixMul result.analytic.normalized.aInverse.adjugate
        result.periodData.aMatrix row column).name
      (scaleIdentity result.analytic.normalized.aInverse.scalar
        row column).name :=
by
  have identity := result.normalization.left_identity row column
  rw [result.normalization.adjugate_eq, result.normalization.a_eq, result.normalization.scalar_eq] at identity
  exact identity

/-- Read the cached right scaled-inverse identity in the original period-matrix names. -/
@[expose] def aInverse_right_identity {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (row column : Fin genus) :
    Equivalence.NamedEquivalent
      (matrixMul result.periodData.aMatrix
        result.analytic.normalized.aInverse.adjugate row column).name
      (scaleIdentity result.analytic.normalized.aInverse.scalar
        row column).name :=
by
  have identity := result.normalization.right_identity row column
  rw [result.normalization.a_eq, result.normalization.adjugate_eq, result.normalization.scalar_eq] at identity
  exact identity

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- The original period-data cycles retain their explicit realization of the result's geometric basis. -/
theorem periodCycles_realize_basisCycles {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve) :
    PreparedRefinementPrograms.SymplecticCycleRealization curve
      result.periodData.cycles result.basis.cycles :=
  result.analytic.cycles_realization

open Purelib.Curves.Hyperelliptic in
/-- Read the normalized period matrix from the retained normalization cache. -/
@[expose] def omega {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) : NamedMatrix genus :=
  result.normalization.omega

section
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- An A-period request uses the original shared period-table channels and specified positive tolerance. -/
theorem aPeriodRequest {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) (differential cycle : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Table.CCL.Request.RequestContract result.periodData.table.channels
      (result.periodData.aMatrix differential cycle) target positive count :=
  result.periodData.aEntry_sharedRequest
    differential cycle target positive count

/-- A B-period request uses the original shared period-table channels and specified positive tolerance. -/
theorem bPeriodRequest {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) (differential cycle : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Table.CCL.Request.RequestContract result.periodData.table.channels
      (result.periodData.bMatrix differential cycle) target positive count :=
  result.periodData.bEntry_sharedRequest
    differential cycle target positive count

/-- A normalized-period entry request retains the analytic normalization's shared table channels. -/
theorem omegaRequest {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) (row column : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target)
    (count : Nat) :
    Table.CCL.Request.RequestContract
      result.analytic.normalized.omegaTable.channels
      (result.omega row column) target positive count :=
by
  rw [omega, result.normalization.omega_readback row column]
  exact result.analytic.normalized.omegaEntry_sharedRequest row column target positive count

end

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- Symmetry of the retained normalized period matrix as named Gaussian equivalence. -/
@[expose] def omega_symmetric {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (result : Result curve) (row column : Fin genus) :
    Equivalence.NamedEquivalent
      (result.omega row column).name (result.omega column row).name :=
by
  have symmetry := result.cachedBilinear.symmetry.symmetric row column
  change Equivalence.NamedEquivalent
    (result.normalization.normalized.omega row column).name
    (result.normalization.normalized.omega column row).name at symmetry
  rw [← result.normalization.omega_eq] at symmetry
  exact symmetry

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- Request energy positivity for a retained nonzero rational vector at a positive tolerance.

The request comes from the cached energy certificate and is transported along the exact normalization readback,
retaining the same vector, witness and requested target. -/
@[expose] def omega_positive_energy_request {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    Energy.Certificate.RequestCertificate
      result.analytic.normalized vector nonzero target positive :=
by
  let request := result.cachedEnergy.certify vector nonzero target positive
  exact result.normalized_readback ▸ request

section
open Purelib.Curves.Hyperelliptic
/-- Convert the retained energy request into its positivity margin certificate. -/
@[expose] def omega_positive_margin_request {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    Periods.Matrix.Positivity.MarginCertificate
      result.analytic.normalized vector nonzero target positive :=
  (result.omega_positive_energy_request
    vector nonzero target positive).toMarginCertificate

/-- Convert the retained positivity margin into its certified radius request. -/
@[expose] def omega_positive_radius_request {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    Periods.Matrix.Positivity.RadiusCertificate
      result.analytic.normalized vector nonzero
      target positive :=
  (result.omega_positive_margin_request
    vector nonzero target positive).toRadiusCertificate

/-- Read the robust positivity request from the same retained radius certificate. -/
@[expose] def omega_positive_robust_request {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    Periods.Matrix.Positivity.RequestCertificate
      result.analytic.normalized vector nonzero target positive :=
  (result.omega_positive_radius_request vector nonzero target positive).toRequestCertificate

/-- Read the positive quadratic-form request from the retained robust certificate. -/
@[expose] def omega_positive_request {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    PositiveRequestCertificate result.analytic.normalized vector nonzero
      target positive :=
  (result.omega_positive_robust_request vector nonzero target positive).toPositiveRequestCertificate

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Read the exact positive lower bound supplied by the retained positivity request. -/
@[expose] def omega_positive_lower_bound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) : Fraction.Rational :=
  (result.omega_positive_request vector nonzero target positive).epsilon

open Purelib.Curves.Hyperelliptic in
/-- The lower bound from the retained positivity request is strictly positive. -/
theorem omega_positive_lower_bound_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    0 < result.omega_positive_lower_bound vector nonzero target positive :=
  (result.omega_positive_request vector nonzero target positive).epsilon_positive

open Purelib in
open Purelib.Curves.Hyperelliptic in
/-- The requested normalized-matrix center has strictly positive imaginary quadratic form.

The center uses the same request's retained refinement target and positivity witness; its certified lower bound is
positive for the supplied nonzero rational vector. -/
theorem omega_center_imaginaryQuadraticForm_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    let request := result.omega_positive_request vector nonzero target positive
    0 < imaginaryQuadraticForm vector
      (LinearAlgebra.Matrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  dsimp only
  exact (result.omega_positive_request vector nonzero target positive).epsilon_positive.trans
    (result.omega_positive_request vector nonzero target positive).center_positive

end Result

end Purelib.Riemann.Periods.PeriodTheorem
