module
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Vector.Basic
import Purelib.Integration.Program.Gaussian.Basic

public import Purelib.Riemann.Periods.WeightedPeriods

@[expose] public section

/-!
# Operational names of synchronized integer period combinations

The efficient weighted stream is identified with actual CCL multiplication
by exact integer constants and finite addition of component period names.
Its samples are the original programs' samples, not samples taken again
through an intermediate stateful arithmetic name.
-/

namespace Purelib.Riemann.Periods.WeightedPeriodNames

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Periods.PeriodMatrix (geometricNamed sumNamed)
open Purelib.Riemann.Periods.WeightedPeriods (Coefficients GeometricApproximation Gaussian Coordinate)

open Purelib.Integration in
open Purelib.Data in
/-- Read a geometric approximation directly from a retained refinement program's model samples.

Reuse its error scale, later-sample comparison and center bound at the exact original model indices. -/
def programApproximation (program : Program.Gaussian.Basic.RefinementProgram) : GeometricApproximation where
  sample := fun stage => (program.model stage).integralSample
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  later_close := fun order => by
    have scalar := program.later_close order
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := fun index => by
    have scalar := program.sample_bounded index
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

open Purelib.Integration in
open Purelib.Approximation in
/-- The retained program output name is operationally its direct geometric approximation name. -/
def programApproximation_output (program : Program.Gaussian.Basic.RefinementProgram) :
    Gaussian.Equivalence.NamedEquivalent program.output.name (geometricNamed (programApproximation program)).name :=
  Gaussian.Equivalence.NamedEquivalent.refl _

open Purelib.Approximation in
/-- Actual multiplication by an exact Gaussian constant agrees operationally with scaled geometric samples.

Multiplication congruence and the pointwise product readback identify the same retained source approximation. -/
public def scaledName (coefficient : Gaussian) (source : GeometricApproximation) :
    Gaussian.Equivalence.NamedEquivalent (Gaussian.Name.Coherent.CoherentNamed.mul
      (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact coefficient) (geometricNamed source)).name
      (geometricNamed (Gaussian.Geometric.GeometricApproximation.mul
        (Gaussian.Geometric.GeometricApproximation.exact coefficient) source)).name := by
  apply Gaussian.Equivalence.NamedEquivalent.trans
    (Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects _ _ _ _
      (Gaussian.Geometric.Coherent.Comparison.geometricExact_equivalent_exact coefficient).symm
        (Gaussian.Equivalence.NamedEquivalent.refl _))
  exact Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
    (Gaussian.Geometric.GeometricApproximation.exact coefficient).toApproximation
    source.toApproximation
    (Gaussian.Geometric.GeometricApproximation.mul
      (Gaussian.Geometric.GeometricApproximation.exact coefficient) source).toApproximation
    (fun _ => rfl)

namespace Coefficients

variable {count : Nat} {weights : Data.Vector Int count}

open Purelib.Approximation in
/-- Form the finite arithmetic combination of supplied names using the cached integer coefficients. -/
def named (coefficients : Coefficients weights) (values : Fin count → Gaussian.Name.Coherent.CoherentNamed) :
  CoherentNamed :=
  sumNamed fun index => Gaussian.Name.Coherent.CoherentNamed.mul (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
    (coefficients.values index)) (values index)

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- The cached weighted sample stream agrees operationally with the actual arithmetic combination.

Each supplied name is equivalent to its retained geometric source. The proof preserves the cached coefficient bank and
exact component samples in the finite sum. -/
def named_equivalent (coefficients : Coefficients weights) (values : Fin count → Gaussian.Name.Coherent.CoherentNamed)
    (sources : Data.Vector GeometricApproximation count)
    (equivalent : ∀ index, Gaussian.Equivalence.NamedEquivalent (values index).name (geometricNamed (sources
      index)).name) :
    Gaussian.Equivalence.NamedEquivalent (Periods.WeightedPeriodNames.Coefficients.named coefficients values).name
      (geometricNamed (coefficients.approximation sources)).name := by
  let summands := fun index => Gaussian.Geometric.GeometricApproximation.mul
    (Gaussian.Geometric.GeometricApproximation.exact (coefficients.values index)) (sources index)
  have arithmetic := PeriodMatrix.sumNamed_equivalent_geometricSum
    (fun index => Gaussian.Name.Coherent.CoherentNamed.mul (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
      (coefficients.values index)) (values index)) summands
    (fun index => (Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects _ _ _ _
      (Gaussian.Equivalence.NamedEquivalent.refl _) (equivalent index)).trans (scaledName _ _))
  apply arithmetic.trans
  exact Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (Gaussian.Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Gaussian.Geometric.GeometricApproximation.sum summands).toApproximation
      (coefficients.approximation sources).toApproximation (by
        intro stage
        rw [Gaussian.Geometric.GeometricApproximation.toApproximation_sample,
          Gaussian.Geometric.GeometricApproximation.sum_sample]
        exact FiniteSum.Fin.sumFin_congr fun _ => rfl))

end Coefficients

end Purelib.Riemann.Periods.WeightedPeriodNames
