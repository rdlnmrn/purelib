module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Nat.Order

/-! # Original names and genuine finite geometric tails

Discarding a finite prefix preserves the original all-later comparison
procedure. Native named samples and geometric tail indices remain distinct;
the original sampling bridge supplies the operational name comparison.
-/

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

public section

namespace Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

/-- A finite tail uses the same original all-later comparison at genuinely later right indices. -/
def drop_equivalent (source : GeometricApproximation) (floor : Nat) :
    Equivalent source.toApproximation (source.drop floor).toApproximation where
  compare firstStart lastStart target positive := by
    let compared := (Equivalent.refl source.toApproximation).compare firstStart lastStart target positive
    exact
      { leftIndex := compared.leftIndex
        rightIndex := compared.rightIndex
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := by
          intro firstLater lastLater firstAfter lastAfter
          change Purelib.Data.Gaussian.Norm.Basic.normSq
            (source.sample firstLater - (source.drop floor).sample lastLater) < target
          rewrite [drop_sample]
          exact compared.close firstAfter (lastAfter.trans (Nat.le_add_left _ _)) }

end Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

namespace Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

/-- A native tail retains the original channel's sampler and an actual finite starting floor. -/
def nativeTail (channel : CoherentNamed) (floor : Nat) : GeometricApproximation :=
  (GeometricApproximation.ofNamed channel.name).drop floor

/-- Each tail sample is the original native named sample at the retained floor plus its own index. -/
theorem nativeTail_sample (channel : CoherentNamed) (floor index : Nat) :
    (nativeTail channel floor).sample index = (Name.Sampling.approximation channel.name).sample (floor + index) := by
  unfold nativeTail
  rewrite [GeometricApproximation.drop_sample, GeometricApproximation.ofNamed_sample]
  rfl

/-- The original named channel compares with its actual finite tail through the original sampling bridge. -/
def nativeTail_agrees (channel : CoherentNamed) (floor : Nat) :
    NamedEquivalent channel.name (nativeTail channel floor).toApproximation.toNamed := by
  let source := GeometricApproximation.ofNamed channel.name
  let tail := source.drop floor
  let original := source.drop_equivalent floor
  let compared := original.withSamples (Name.Sampling.approximation channel.name) tail.toApproximation
    (fun index => (GeometricApproximation.ofNamed_sample channel.name index).symm) (fun _ => rfl)
  exact compared.trans (Equivalent.toNamed_sampling tail.toApproximation).symm

end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

end
