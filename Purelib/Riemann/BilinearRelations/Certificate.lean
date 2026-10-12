module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Matrix.Operational.Bilinear
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
public import Purelib.Curves.Hyperelliptic.Periods.Pairing
public import Purelib.Integration.Path.Cancellation
import Purelib.Integration.Path.Primitive

section
public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib

namespace Riemann.BilinearRelations.Certificate

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Approximation in
set_option genInjectivity false in
/-- Finite Stokes data identifying the period-pairing cycle sum with a canceling boundary.

The boundary is either retained reversed edge pairs or closed primitive paths. Both constructors retain operational
equivalence to the original unnormalized cycle sum. -/
inductive StokesCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Purelib.Riemann.Periods.PeriodMatrix.PeriodData curve) : Type 2
  /-- Supply finite persistent reversed-edge pairs and their operational cycle-sum comparison. -/ | pairedBoundary
      (edgePairCount : Nat)
      (edgePairs : Fin genus -> Fin genus ->
        Fin edgePairCount -> Path.Cancellation.ProgramBoundaryPair)
      (cycleSum_eq_boundary : forall row column : Fin genus,
        Gaussian.Equivalence.NamedEquivalent (Hyperelliptic.Periods.Pairing.periodPairingCycleSum data row column).name
          (Path.Cancellation.boundarySum (fun index =>
            (edgePairs row column index).toBoundaryPair)).name)
  /-- Supply closed primitive boundaries and their operational cycle-sum comparison. -/ | primitiveBoundary
      (boundaries : Fin genus -> Fin genus -> Path.Primitive.ClosedPrimitiveBoundary)
      (cycleSum_eq_boundary : forall row column : Fin genus,
        Gaussian.Equivalence.NamedEquivalent (Hyperelliptic.Periods.Pairing.periodPairingCycleSum data row column).name
          (boundaries row column).integralSum.name)

constructive_injectivity StokesCertificate

end Riemann.BilinearRelations.Certificate

namespace Curves.Hyperelliptic.Periods.Pairing.StokesClosure

open Purelib.Riemann in
open Purelib.Curves in
/-- Expose the canonical cycle-path closure as a finite Stokes certificate.

Reuse its retained primitive boundary and exact cycle-sum comparison for every pair of period indices. -/
@[expose] def toStokesCertificate {genus : Nat} {curve
  : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : Periods.PeriodMatrix.PeriodData curve} (closure : Hyperelliptic.Periods.Pairing.StokesClosure data) :
    BilinearRelations.Certificate.StokesCertificate data :=
  .primitiveBoundary
    (fun row column => closure.boundary row column)
    (fun row column => closure.cycleSum_eq_boundary row column)

end Curves.Hyperelliptic.Periods.Pairing.StokesClosure

namespace Riemann.BilinearRelations.Certificate.StokesCertificate

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Approximation in
/-- Finite boundary cancellation makes the unnormalized period-pairing residual operationally zero.

The retained reversed-edge certificates or primitive endpoint telescoping establish the same conclusion for the original
period data. -/
@[expose] def pairingResidual_zero {genus : Nat}
  {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : Periods.PeriodMatrix.PeriodData curve} (certificate : BilinearRelations.Certificate.StokesCertificate data)
    (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (Hyperelliptic.Periods.Pairing.periodPairingResidual data row column).name
    (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  cases certificate with
  | pairedBoundary edgePairCount edgePairs cycleSumEquivalent =>
      exact Gaussian.Equivalence.NamedEquivalent.trans
        (Hyperelliptic.Periods.Pairing.periodPairingResidual_equivalent_cycleSum data row column)
        (Gaussian.Equivalence.NamedEquivalent.trans
          (cycleSumEquivalent row column)
          (Path.Cancellation.boundarySum_zero fun index =>
            (edgePairs row column index).toBoundaryPair))
  | primitiveBoundary boundaries cycleSumEquivalent =>
      exact Gaussian.Equivalence.NamedEquivalent.trans
        (Hyperelliptic.Periods.Pairing.periodPairingResidual_equivalent_cycleSum data row column)
        (Gaussian.Equivalence.NamedEquivalent.trans
          (cycleSumEquivalent row column)
          (boundaries row column).integralSum_zero)

open Purelib.Riemann
open Purelib.Curves
open Purelib.Approximation
/-- The finite Stokes certificate gives the operational identity A Bᵀ = B Aᵀ before normalization. -/
@[expose] def periodRelation {genus : Nat} {curve
  : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : Periods.PeriodMatrix.PeriodData curve} (certificate : BilinearRelations.Certificate.StokesCertificate data)
      :
    Periods.PeriodMatrix.MatrixEquivalent
      (Periods.PeriodMatrix.matrixMul data.aMatrix (Periods.PeriodMatrix.transpose data.bMatrix))
      (Periods.PeriodMatrix.matrixMul data.bMatrix (Periods.PeriodMatrix.transpose data.aMatrix)) := by
  intro row column
  exact Gaussian.Coherent.Additive.equivalent_of_sub_zero
    (Periods.PeriodMatrix.matrixMul data.aMatrix (Periods.PeriodMatrix.transpose data.bMatrix) row column)
    (Periods.PeriodMatrix.matrixMul data.bMatrix (Periods.PeriodMatrix.transpose data.aMatrix) row column)
    (by
        simpa only [Hyperelliptic.Periods.Pairing.periodPairingResidual]
          using certificate.pairingResidual_zero row column)

/-- Derive normalized numerator symmetry from the retained Stokes period relation and inverse data. -/
@[expose] def numeratorSymmetry {genus : Nat}
  {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : Periods.PeriodMatrix.NormalizedPeriodData curve}
    (certificate : BilinearRelations.Certificate.StokesCertificate data.toPeriodData) :
    Periods.PeriodMatrix.NormalizedPeriodData.NumeratorSymmetryCertificate data where
  symmetric := by
    intro row column
    have symmetricMatrix := Matrix.Operational.Bilinear.numeratorMatrix_symmetric_of_periodRelation
      data.toPeriodData.aMatrix data.toPeriodData.bMatrix data.aInverse
      certificate.periodRelation
    simpa only [Periods.PeriodMatrix.transpose_apply] using symmetricMatrix row column

end Riemann.BilinearRelations.Certificate.StokesCertificate

namespace Riemann.BilinearRelations.Certificate

open Purelib.Riemann in
open Purelib.Curves in
set_option genInjectivity false in
/-- The canonical finite Stokes closure for unnormalized period data.

The retained closure establishes the first bilinear relation before any A-period inverse or normalized energy request is
supplied. -/
structure PreNormalizationCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : Periods.PeriodMatrix.PeriodData curve) where
  /-- The retained closure of the canonical finite period-pairing boundary. -/ stokesClosure :
    Hyperelliptic.Periods.Pairing.StokesClosure data

constructive_injectivity PreNormalizationCertificate

end Riemann.BilinearRelations.Certificate

namespace Riemann.BilinearRelations.Certificate.PreNormalizationCertificate

open Purelib.Riemann in
open Purelib.Curves in
/-- Read the derived finite Stokes certificate from the retained canonical closure. -/
@[expose] def stokes {genus : Nat}
  {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : Periods.PeriodMatrix.PeriodData curve}
    (certificate : BilinearRelations.Certificate.PreNormalizationCertificate data) :
      BilinearRelations.Certificate.StokesCertificate data :=
  certificate.stokesClosure.toStokesCertificate

end Riemann.BilinearRelations.Certificate.PreNormalizationCertificate

namespace Riemann.BilinearRelations

open Purelib.Riemann in
open Purelib.Curves in
set_option genInjectivity false in
/-- Pre-normalization Stokes closure together with certified normalized finite-cell energy.

Both components concern the same normalized period data and its original unnormalized parent. -/
structure Certificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : Periods.PeriodMatrix.NormalizedPeriodData curve)
      where
  /-- The retained canonical Stokes closure for the original unnormalized period data. -/ preNormalization :
    BilinearRelations.Certificate.PreNormalizationCertificate data.toPeriodData
  /-- The normalized finite-cell energy certificate for these exact period data. -/ energy :
    Curves.Hyperelliptic.Integration.Energy.Certificate data

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Certificate

end Riemann.BilinearRelations

namespace Riemann.BilinearRelations.Certificate

open Purelib.Riemann in
open Purelib.Curves in
/-- Read the finite Stokes certificate from the retained pre-normalization component. -/
@[expose] def stokes {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {data : Periods.PeriodMatrix.NormalizedPeriodData curve}
    (certificate : Certificate data) : BilinearRelations.Certificate.StokesCertificate
      data.toPeriodData :=
  certificate.preNormalization.stokes

open Purelib.Riemann in
open Purelib.Curves in
/-- Derive pointwise matrix positivity from the retained finite-cell energy certificate. -/
@[expose] def positivity {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {data : Periods.PeriodMatrix.NormalizedPeriodData curve}
    (certificate : Certificate data) :
    Hyperelliptic.Periods.Matrix.Positivity.Certificate data :=
  certificate.energy.toPositivity

open Purelib.Riemann in
open Purelib.Curves in
/-- Package derived numerator symmetry and positivity as the bilinear-relations certificate. -/
@[expose] def toBilinearRelations {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {data : Periods.PeriodMatrix.NormalizedPeriodData curve}
    (certificate : Certificate data) : Periods.PeriodMatrix.BilinearRelationsCertificate
      data where
  numeratorSymmetry := certificate.stokes.numeratorSymmetry
  positivity := certificate.positivity.toPointwisePositivity

open Purelib.Riemann in
open Purelib.Curves in
/-- Expose operational normalized-period symmetry derived from finite Stokes cancellation. -/
@[expose] def symmetry {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {data : Periods.PeriodMatrix.NormalizedPeriodData curve}
    (certificate : Certificate data) :
    Periods.PeriodMatrix.NormalizedPeriodData.SymmetryCertificate data :=
  certificate.toBilinearRelations.symmetry

end Riemann.BilinearRelations.Certificate

end Purelib

end
