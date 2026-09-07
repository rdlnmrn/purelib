import RFAP.Paper
import CCL.Paper
import CCL.Bridge.General
import CCL.Bridge.Polynomial
import CCL.Bridge.Rational

/-!
# CCL-2 adapters from FTA boxes to finite CCL data

These declarations consume the box theorem through `RFAP.Paper` but live in
the CCL-2 `CCL.Paper` namespace.  Importing RFAP never imports this bridge.
-/

namespace CCL.Paper

abbrev GaussianPolynomial := RFAP.Paper.GaussianPolynomial
abbrev SquarefreeCertificate := RFAP.Paper.SquarefreeCertificate
abbrev IrreducibleCertificate := RFAP.Paper.IrreducibleCertificate
abbrev BoxInput := RFAP.Paper.BoxInput

abbrev GeneralCCLResult (p : GaussianPolynomial) :=
  CCL.GeneralRFAP.CCLResult p

/-- Total CCL-coupled preprocessing and isolation for zero, constant, and
positive-degree displayed polynomials, isolating each pairwise-coprime
squarefree factor once with its exact multiplicity. -/
def isolateGeneralWithCCL (p : GaussianPolynomial) : GeneralCCLResult p :=
  CCL.GeneralRFAP.isolateWithCCL p

/-- Coupled shrinking-box and finite-CCL request result. -/
abbrev CCLResult (p : GaussianPolynomial) :=
  CCL.BoxRFAPBridge.PositiveResult p

abbrev ActiveCCLResult (p : GaussianPolynomial) :=
  CCL.BoxRFAPBridge.Result p
abbrev ExactTerminal (p : GaussianPolynomial) :=
  CCL.BoxRFAPBridge.Terminal p
abbrev TerminalTransducer (p : GaussianPolynomial) :=
  CCL.BoxRFAPBridge.TerminalTransducer p
abbrev EncodingTransducer (fraction : CCL.Integral.Frac) :=
  CCL.Transducer.EncodingTransducer fraction
abbrev PersistentCursor := CCL.PersistentProgressive.Cursor
abbrev PersistentTrackState
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (track : RFAP.ShrinkingTrack.WindingOneTrack p ambient) :=
  CCL.PersistentTrack.State track
abbrev RationalCCLResult
    (numerator denominator : GaussianPolynomial) :=
  CCL.RationalRFAPBridge.Result numerator denominator
abbrev PolynomialRootStreamResult (p : GaussianPolynomial) :=
  CCL.PolynomialRootStreams.Result p
abbrev ApproximationSharpnessTower
    (threshold : RFAP.ConstructiveFraction.Rational)
    (requestedScale totalWindows : Nat) :=
  CCL.ApproximationSharpness.ReservedTower
    threshold requestedScale totalWindows

/-- Coherent prefix-extension cursor for an exact zero/nonzero terminal. -/
def terminalTransducer
    {p : GaussianPolynomial} (terminal : ExactTerminal p) :
    TerminalTransducer p :=
  CCL.BoxRFAPBridge.TerminalTransducer.ofTerminal terminal

/-- Exact degree-many box isolation equipped with total finite CCL requests. -/
def isolateWithCCL
    {p : GaussianPolynomial} (input : BoxInput p) : CCLResult p :=
  CCL.BoxRFAPBridge.provePositive input

/-- Degree-greater-than-one box/CCL theorem from explicit finite squarefree
Bezout data. -/
def isolateDegreeGtOneWithCCL
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : CCLResult p :=
  CCL.BoxRFAPBridge.provePositiveDegreeGtOne squarefree degree

/-- CCL-coupled isolation with squarefreeness derived from finite
proper-divisor irreducibility. -/
def isolateIrreducibleWithCCL
    {p : GaussianPolynomial} (irreducible : IrreducibleCertificate p) :
    CCLResult p :=
  isolateWithCCL
    { squarefree :=
        RFAP.Irreducible.squarefreeOfIrreducible irreducible
      degreePositive := irreducible.degreePositive }

/-- Total polynomial-facing root-stream construction.  The zero polynomial
is returned explicitly; every nonzero polynomial receives a displayed finite
index of exact or higher RAT sites, their multiplicities, and persistent CCL
requests with proved prefix growth and sidecar error. -/
def polynomialRootStreams
    (p : GaussianPolynomial) : PolynomialRootStreamResult p :=
  CCL.PolynomialRootStreams.isolate p

/-- Reserve one arbitrary finite robust approximation-sharpness run and one
finite CCL encoding, from which later calculations can reveal coherent
window and word prefixes without changing the displayed source sample. -/
def finiteApproximationSharpnessTower
    {threshold : RFAP.ConstructiveFraction.Rational}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    ApproximationSharpnessTower threshold requestedScale totalWindows :=
  CCL.ApproximationSharpness.finiteSharpnessTower
    certificate requestedScale totalWindows

/-- Total rational-function argument principle with CCL observations attached
to every exact or shrinking zero and pole site returned by Paper I.  Every
site exposes a persistent arithmetic cursor with exact raw-parser semantics;
later requests append to its same prefix and contract its projective sidecar,
while higher sites simultaneously return nested Paper-I boxes. -/
def rationalFunctionArgumentPrincipleWithCCL
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalCCLResult numerator denominator :=
  CCL.RationalRFAPBridge.prove numerator denominator
    denominatorNonzero

end CCL.Paper
