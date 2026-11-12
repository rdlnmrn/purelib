module
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Original face-bank constructors selected by an ordinary numerator request

Both branches return the original bank on the SAME domains. The default
calls its original constructor, while the supplied ordinary differential
calls its original full-polynomial constructor with the single owned
numerator interpretation.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {faces : List (RegularFace bank)}

/-- Select the literal original default or full-polynomial constructor on the SAME given domain bank. -/
def buildRequested (differential : Differential genus) (index : Nat) (domains : FaceDomainBank frames faces)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    FacePrimitiveBank differential index domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) :=
  match polynomial with
  | none => build differential index domains
  | some ordinary => build differential index domains ordinary.numerator

/-- The default request constructs the whole original bank through its original default producer. -/
theorem buildRequested_none (differential : Differential genus) (index : Nat) (domains : FaceDomainBank frames faces) :
    buildRequested differential index domains none = build differential index domains := by rfl

/-- A supplied ordinary specification constructs the whole original bank with its genuine scaled polynomial. -/
theorem buildRequested_some (differential : Differential genus) (index : Nat) (domains : FaceDomainBank frames faces)
    (ordinary : Ordinary curve.polynomial) :
    buildRequested differential index domains (some ordinary) =
      build differential index domains ordinary.numerator := by rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
