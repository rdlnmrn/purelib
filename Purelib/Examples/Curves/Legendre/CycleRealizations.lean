module
public import Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement

public section

namespace Purelib.Examples.Curves.Legendre.CycleRealizations

open Purelib.Curves
open Purelib.Examples
open Purelib.Riemann

open Purelib.Examples.Curves.Legendre.Prepared

/-- The canonical lifted A-cycle equals the retained raw Legendre cycle data. -/
private theorem canonicalACycle_eq_rawData :
    (((Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData
      RealMinusOne.curve RealMinusOne.branchData).cycles.aCycle (0 :
        Fin 1)).liftedPath 0) =
        RealMinusOne.rawACycleTarget := by
  change ((RealMinusOne.branchFamily.symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
    RealMinusOne.rawACycleTarget
  unfold RealMinusOne.rawACycleTarget
  unfold RealMinusOne.branchFamily
  rw [Hyperelliptic.Branches.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

/-- The cached prepared Legendre A-cycle realizes its original displayed basis cycle. -/
theorem preparedACycle_realizes_basis :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (RealMinusOne.preparedACycleWitness ()).data
      (((Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData
        RealMinusOne.curve RealMinusOne.branchData).cycles.aCycle (0 :
          Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact (RealMinusOne.preparedACycleWitness ()).realizes

/-- The cached two-bank Legendre fixture realizes the retained connector retrace.

Its raw target is the connector cycle supplied by the fixture, with the same prepared witness and realization proof. -/
theorem preparedBCycle_realizes_connector :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (RealMinusOne.preparedBCycleWitness ()).data
      RealMinusOne.rawBCycleTarget :=
  (RealMinusOne.preparedBCycleWitness ()).realizes

end Purelib.Examples.Curves.Legendre.CycleRealizations
