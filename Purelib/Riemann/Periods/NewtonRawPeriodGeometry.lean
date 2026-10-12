module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.NewtonCanonicalSampleComparison
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget

@[expose] public section

/-! Canonical period comparisons consume the raw request's retained geometry. -/
namespace Purelib.Riemann.Periods.NewtonRawPeriodGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {observations : ProtectedObservations original} {preparation : NewtonPreparation original}
  {radius : Purelib.Data.Rat.Fraction.Rational}

/-- Read period geometry from the retained raw-energy grid.

Reuses the original Newton preparation, allocated grid, lift and face-domain bank, with an empty additional-cut list. -/
def periodGeometry (raw : RawEnergyGrid observations preparation radius) : PeriodGeometry original :=
  ⟨preparation, _, _, raw.allocated.family.single.grid, raw.lifted, raw.domains, []⟩

end Purelib.Riemann.Periods.NewtonRawPeriodGeometry
