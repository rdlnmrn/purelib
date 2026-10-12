module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
public import Purelib.Riemann.Normalization.InverseModelRootRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners

open Purelib.Polynomial.Dense.Gaussian

@[expose] public section

/-!
# Actual cap samples on retained exterior root channels

The primitive bank's original inverse polynomial is reused at the actual
inverse boundary point. The disk view supplies a geometric residual bound
and a finite request against its retained root program, with independent
later polynomial and root-reading indices.
-/

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives in
/-- The retained sample's residual decays on the full disk, independently of its original, smaller rectangle's
advertised residual bound. -/
theorem disk_residual_bound (sample : Primitives.Sample cap differential index box)
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (sample.inverse.residual.eval point) ≤ Geometric.Basic.quarterRadius (1 /
      256) index := by
  rw [sample.inverse_eq]
  exact Data.disk_refine_residual cap index inside

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint

/-- A point's certified disk presentation uses the same polynomial sample already materialized by the cap bank. No
second refinement is executed. -/
theorem sample_inverse_eq (disk : Owners.DiskPoint cap point)
    (sample : Primitives.Sample cap differential index box) :
    sample.inverse.value = ((Data.diskPointModel cap point disk.inside).refine index).value := by
  rw [sample.inverse_eq]
  exact (Data.diskModel_refine cap _ _ index).1.symm

/-- Pay the regular-root discrepancy using the existing finite request, while evaluating the actual shared cap inverse
polynomial. -/
theorem inverse_accurate (disk : Owners.DiskPoint cap point)
    (sample : Primitives.Sample cap differential index box)
    {target : InverseRootPolynomial.Coordinate} {floor rootIndex : Nat}
    (request : InverseModelRootRequests.InverseRequest disk.channel target floor)
    (later : request.index ≤ index) (rootLater : request.comparison.rightIndex ≤ rootIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.inverse.value.eval point -
      Data.Gaussian.Field.inv ((Sampling.approximation disk.certificate.value.name).sample rootIndex)) < target
        := by
  rw [disk.sample_inverse_eq sample]
  have scalar := request.accurate later rootLater
  let root := (Sampling.approximation disk.channel.certificate.value.name).sample rootIndex
  have inverseEq : Data.Gaussian.Basic.Canonical.inv root = Data.Gaussian.Field.inv root := by
    change root⁻¹ = Data.Gaussian.Field.inv root
    exact Data.Gaussian.Field.inv_eq root
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, inverseEq] at scalar
  simpa only [DiskPoint.certificate] using scalar

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint
