module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Path.PairedAreaComparison

namespace Test.Curves.Hyperelliptic.ReadingInterfaces

open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (MagnitudeBank)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {owner : OwnedPuncturedMesh curve}
    {domains : DomainFamily owner} {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    {stage : Nat} {leftBank : ReadingBank owner leftDifferential stage domains}
    {rightBank : ReadingBank owner rightDifferential stage domains}
    (left : BankReadings owner leftDifferential stage domains leftBank)
    (right : BankReadings owner rightDifferential stage domains rightBank)

/-- Imported construction preserves the original owner, stage and both primitive-bank identities by reduction. -/
private theorem paired_bank_identity :
    let sample := PairedReadings.ofReadings (owner := owner) left right
    sample.meshOwner = owner ∧ sample.stage = stage ∧ sample.leftBank = leftBank ∧ sample.rightBank = rightBank :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The original first magnitude floor and bound survive packaging without dependent-owner reconstruction. -/
private theorem paired_left_magnitude_identity (fixed : MagnitudeBank owner domains leftDifferential)
    (later : fixed.index ≤ stage) :
    let sample := PairedReadings.ofReadings (owner := owner) left right
    let magnitude := sample.leftMagnitude fixed later
    magnitude.index = fixed.index ∧ magnitude.bound = fixed.bound := ⟨rfl, rfl⟩

/-- The original second magnitude floor and bound are distinct and survive the common-stage package. -/
private theorem paired_right_magnitude_identity (fixed : MagnitudeBank owner domains rightDifferential)
    (later : fixed.index ≤ stage) :
    let sample := PairedReadings.ofReadings (owner := owner) left right
    let magnitude := sample.rightMagnitude fixed later
    magnitude.index = fixed.index ∧ magnitude.bound = fixed.bound := ⟨rfl, rfl⟩

/-- A single reading retains the same original primitive values in its magnitude certificate. -/
private theorem single_magnitude_identity (fixed : MagnitudeBank owner domains leftDifferential)
    (later : fixed.index ≤ stage) :
    let sample := SingleReadings.ofReadings (owner := owner) left
    let magnitude := sample.magnitude fixed later
    magnitude.index = fixed.index ∧ magnitude.bound = fixed.bound := ⟨rfl, rfl⟩

/-- Mixed certification preserves the exact original coefficient and its original quantitative bound expression. -/
private theorem mixed_magnitude_identity (coefficient : Canonical)
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential)
    (leftLater : leftFixed.index ≤ stage) (rightLater : rightFixed.index ≤ stage) :
    let sample := MixedReadings.ofReadings (owner := owner) coefficient left right
    let magnitude := sample.magnitude leftFixed rightFixed leftLater rightLater
    magnitude.bound = EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient := rfl

/-- Paired and conjugate views differ on a non-real first increment while retaining the same second increment. -/
private theorem conjugate_is_distinct :
    (PairedAreaComparison.point .paired (⟨0, 1⟩ : Canonical) 0).left = (⟨0, 1⟩ : Canonical) ∧
    (PairedAreaComparison.point .conjugate (⟨0, 1⟩ : Canonical) 0).left = (⟨0, -1⟩ : Canonical) ∧
    (PairedAreaComparison.point .paired (⟨0, 1⟩ : Canonical) 0).right =
      (PairedAreaComparison.point .conjugate (⟨0, 1⟩ : Canonical) 0).right := ⟨rfl, rfl, rfl⟩

end Test.Curves.Hyperelliptic.ReadingInterfaces
