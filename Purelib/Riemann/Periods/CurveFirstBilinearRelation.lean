module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Periods.Pairing
public import Purelib.Riemann.BilinearRelations.Certificate
public import Purelib.Riemann.Integration.PreparedRefinementPrograms

import Purelib.Approximation.Budget.VanishingSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Polynomial.Dense.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! The unconditional first bilinear relation for the corrected ordered
programs, before any inverse or normalization certificate is available. -/
namespace Purelib.Riemann.Periods.CurveFirstBilinearRelation.Prepared

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Periods.Pairing (synchronizedPeriodPairingResidual)
open Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison (geometricZero_equivalent_exact)
open Purelib.Riemann.Periods.PeriodMatrix (geometricNamed)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (SynchronizedZeroRequest)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- The retained synchronized period-pairing residual is equivalent to the exact zero name.

For every positive target and stage floor, the same prepared geometry, Newton preparation and face domains produce a
certified vanishing sample; this comparison is transported to the residual's geometric name. -/
@[expose] def synchronizedZero (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (preparation :
  NewtonPreparation base.bank.toBranchCellBank)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (first second :
      Fin genus) :
    Equivalence.NamedEquivalent
      (geometricNamed (Periods.Pairing.synchronizedPeriodPairingResidual prepared.periodData first second)).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  (Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Approximation.Budget.VanishingSamples.equivalentZero (Periods.Pairing.synchronizedPeriodPairingResidual
      prepared.periodData first second)
      (fun target positive minimum =>
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedZeroRequest.build prepared preparation domains first
          second target 1 positive (by decide) minimum).sample))).trans
    Geometric.Coherent.Comparison.geometricZero_equivalent_exact

end Purelib.Riemann.Periods.CurveFirstBilinearRelation.Prepared

namespace Purelib.Riemann.Periods.CurveFirstBilinearRelation.PairedPeriodBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.BilinearRelations.Certificate (PreNormalizationCertificate)
open Purelib.Curves.Hyperelliptic.Periods.Pairing (UpperTriangularStokesClosure)
open Purelib.Curves.Hyperelliptic.Periods.Pairing.UpperTriangularStokesClosure (toStokesClosure ofSynchronizedZero)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Construct a pre-normalization certificate for the exact retained paired period bank.

Genus at most one has no strict upper-triangular pairs. Otherwise one retained Newton preparation and face-domain bank
supply synchronized zero certificates for all required pairs before forming the Stokes closure. -/
@[expose] def preNormalization {genus : Nat} {curve : Basic.HyperellipticCurve genus} (bank :
  Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) :
    Riemann.BilinearRelations.Certificate.PreNormalizationCertificate bank.periodData :=
  if small : genus ≤ 1 then
    let upper : Periods.Pairing.UpperTriangularStokesClosure bank.periodData :=
      { closed_of_lt := fun row column less =>
          let columnZero : column.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (column.isLt.trans_le small))
          (Nat.not_lt_zero row.val (less.trans_le columnZero.le)).elim }
    ⟨upper.toStokesClosure⟩
  else
    match bank with
    | .empty zero =>
        ⟨{ closed := fun row _ => Fin.elim0 (Fin.cast zero row) }⟩
    | .retained (base := base) (lifted := lifted) prepared =>
        let preparation := NewtonPreparation.build base.bank.toBranchCellBank
        let domains := Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build lifted.frames base.faces.regulars
        ⟨(Periods.Pairing.UpperTriangularStokesClosure.ofSynchronizedZero prepared.periodData
          (fun row column _ => CurveFirstBilinearRelation.Prepared.synchronizedZero
            prepared preparation domains row column)).toStokesClosure⟩

end Purelib.Riemann.Periods.CurveFirstBilinearRelation.PairedPeriodBank

namespace Purelib.Riemann.Periods.CurveFirstBilinearRelation.PreparedRefinementPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
/-- Certify pre-normalization for the curve's canonical standard period data using its exact retained paired bank. -/
@[expose] def automaticPreNormalizationCertificate {genus : Nat} (curve : Basic.HyperellipticCurve genus) :
    Riemann.BilinearRelations.Certificate.PreNormalizationCertificate
      (PreparedRefinementPrograms.automaticStandardPeriodData curve) :=
  CurveFirstBilinearRelation.PairedPeriodBank.preNormalization
    (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve)

end Purelib.Riemann.Periods.CurveFirstBilinearRelation.PreparedRefinementPrograms
