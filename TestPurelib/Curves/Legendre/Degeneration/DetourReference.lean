module

import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

/-! # Complete numeric detour retained by its reference construction

The private equality reduces the two original unexposed producer bodies.
The import-all owner is the actual four-quarter Assembly, whose full old
numeric result must stay identical before its new reference is attached.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre.Periods
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}

/-- Attaching the genuine reference keeps the complete original numeric four-quarter result. -/
private theorem whole_numeric_detour {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    (let retained := Execution.Cache.detourWithReference execution elimination clearances frame bank
     Sigma.mk retained.1.val (Sigma.mk retained.2.1.val.1 retained.2.1.val.2.2)) =
      Execution.Cache.detour execution elimination clearances bank.grid := by
  unfold Execution.Cache.detourWithReference Execution.Cache.detour
  rfl

namespace Execution.Cache

/-- The complete historical line/numeric/reference body is retained only for all-input kernel comparison. -/
private def formerDetourWithReference {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    Σ lines : { value : Lines execution elimination clearances //
        value = Lines.build execution elimination clearances },
      Σ _cached : Lines.DetourCache lines.val bank.grid,
        Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop (Paths.polynomial parameter)
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) :=
  let lines := Lines.build execution elimination clearances
  let cached := lines.prepareDetour bank.grid
  let reference := lines.referenceAt frame bank cached.1 rfl
    (Geometry.move elimination circuit.first.regular
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
    cached.2.2.property
  ⟨⟨lines, rfl⟩, ⟨cached, rfl⟩, reference⟩

/-- The current original factory preserves its complete former value, including all numeric heads and the reference. -/
private theorem whole_former_reference {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    Execution.Cache.detourWithReference execution elimination clearances frame bank =
      formerDetourWithReference execution elimination clearances frame bank := by
  unfold Execution.Cache.detourWithReference formerDetourWithReference
  rfl

end Execution.Cache

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
