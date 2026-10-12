module
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Data.CCL.Encoding.Transducer
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Build
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.History
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build
public import Purelib.RootIsolation.CCL.Persistent.Track.Basic
import Purelib.RootIsolation.FTA.Multiplicity.CCL.Basic
public import Purelib.RootIsolation.FTA.Multiplicity.CCL.Build
import Purelib.RootIsolation.FTA.Positive.CCL.Basic
import Purelib.RootIsolation.FTA.Positive.CCL.Build
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build
import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
public import Purelib.RootIsolation.Roots.CCL.Terminal.Encoding
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Irreducible

public import papers.RFAP.Chapters.Paper
import papers.CCL.Chapters.Paper

@[expose] public section

/-!
# CCL-2 adapters from FTA boxes to finite CCL data

These declarations consume the box theorem through `Purelib.Papers.RFAP.Paper` but live in
the CCL-2 `papers.CCL.Chapters.Paper` namespace. Importing RFAP never imports this bridge.
-/

namespace papers.CCL.Chapters.Paper

section
open Purelib.Papers
/-- Dense polynomials with executable Gaussian-rational coefficients. -/
abbrev GaussianPolynomial := RFAP.Paper.GaussianPolynomial
/-- Finite Bézout evidence that the polynomial and its derivative are coprime. -/
abbrev SquarefreeCertificate := RFAP.Paper.SquarefreeCertificate
/-- Constructive positive-degree irreducibility against proper polynomial divisors. -/
abbrev IrreducibleCertificate := RFAP.Paper.IrreducibleCertificate
/-- Squarefree data and a positive-degree certificate for finite box isolation. -/
abbrev BoxInput := RFAP.Paper.BoxInput

end

section
open Purelib.RootIsolation.FTA.Multiplicity.CCL
/-- Total polynomial isolation with multiplicities and finite CCL observations. -/
abbrev GeneralCCLResult (p : GaussianPolynomial) :=
  Basic.CCLResult p

/-- Total CCL-coupled preprocessing and isolation for zero, constant, and
positive-degree displayed polynomials, isolating each pairwise-coprime
squarefree factor once with its exact multiplicity. -/
def isolateGeneralWithCCL (p : GaussianPolynomial) : GeneralCCLResult p :=
  Build.isolateWithCCL p

end

open Purelib.RootIsolation.FTA.Positive.CCL in
/-- Coupled shrinking-box and finite-CCL request result. -/
abbrev CCLResult (p : GaussianPolynomial) :=
  Basic.PositiveResult p

open Purelib.RootIsolation.FTA in
/-- The retained squarefree box-isolation adapter result. -/
abbrev ActiveCCLResult (p : GaussianPolynomial) :=
  Squarefree.AdapterResult p
section
open Purelib.RootIsolation.Roots.CCL.Terminal
/-- An exact root terminal tied to its original polynomial. -/
abbrev ExactTerminal (p : GaussianPolynomial) :=
  Purelib.RootIsolation.Roots.CCL.Terminal p
/-- The coherent finite-encoding transducer of an exact root terminal. -/
abbrev TerminalTransducer (p : GaussianPolynomial) :=
  Encoding.TerminalTransducer p
end

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- A persistent finite encoder for the supplied Gaussian fraction. -/
abbrev EncodingTransducer (fraction : GaussianInt.Fraction) :=
  Transducer.EncodingTransducer fraction
open Purelib.Data.CCL.Progressive.Cursor in
/-- The retained progressive finite-word request cursor. -/
abbrev PersistentCursor := Purelib.Data.CCL.Progressive.Cursor.Request.State
open Purelib.Geometry.Rational (Box) in
open Purelib.RootIsolation.CCL.Persistent.Track in
open Purelib.RootIsolation.Track in
/-- The CCL state attached to the exact retained winding-one track. -/
abbrev PersistentTrackState
    {p : GaussianPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) :=
  Basic.State track
open Purelib.RationalFunctions.ArgumentPrinciple.CCL in
/-- Finite zero and pole isolation with CCL observations for the original numerator and denominator. -/
abbrev RationalCCLResult
    (numerator denominator : GaussianPolynomial) :=
  Basic.Result numerator denominator
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial in
/-- The total multiplicity-aware collection of persistent polynomial root streams. -/
abbrev PolynomialRootStreamResult (p : GaussianPolynomial) :=
  Basic.Result p
open Purelib.Data.Rat in
open Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve in
/-- A finite approximation-sharpness tower retaining its threshold, requested scale and reserved windows. -/
abbrev ApproximationSharpnessTower
    (threshold : Fraction.Rational)
    (requestedScale totalWindows : Nat) :=
  Basic.ReservedTower
    threshold requestedScale totalWindows

open Purelib.RootIsolation.Roots.CCL.Terminal.Encoding in
/-- Coherent prefix-extension cursor for an exact zero/nonzero terminal. -/
def terminalTransducer
    {p : GaussianPolynomial} (terminal : ExactTerminal p) :
    TerminalTransducer p :=
  TerminalTransducer.ofTerminal terminal

section
open Purelib.RootIsolation.FTA.Positive.CCL
/-- Exact degree-many box isolation equipped with total finite CCL requests. -/
def isolateWithCCL
    {p : GaussianPolynomial} (input : BoxInput p) : CCLResult p :=
  Build.provePositive input

/-- Degree-greater-than-one box/CCL theorem from explicit finite squarefree
Bezout data. -/
def isolateDegreeGtOneWithCCL
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : CCLResult p :=
  Build.provePositiveDegreeGtOne squarefree degree

end

open Purelib.Polynomial.Dense.Gaussian.Squarefree in
/-- CCL-coupled isolation with squarefreeness derived from finite
proper-divisor irreducibility. -/
def isolateIrreducibleWithCCL
    {p : GaussianPolynomial} (irreducible : IrreducibleCertificate p) :
    CCLResult p :=
  isolateWithCCL
    { squarefree :=
        Irreducible.squarefreeOfIrreducible irreducible
      degreePositive := irreducible.degreePositive }

open Purelib.RootIsolation.Multiplicity.CCL.Polynomial in
/-- Total polynomial-facing root-stream construction.  The zero polynomial
is returned explicitly; every nonzero polynomial receives a displayed finite
index of exact or higher RAT sites, their multiplicities, and persistent CCL
requests with proved prefix growth and sidecar error. -/
def polynomialRootStreams
    (p : GaussianPolynomial) : PolynomialRootStreamResult p :=
  Build.isolate p

open Purelib.Data.Rat in
open Purelib.NumberTheory.Approximation.Dirichlet.Critical in
open Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve in
/-- Reserve one arbitrary finite robust approximation-sharpness run and one
finite CCL encoding, from which later calculations can reveal coherent
window and word prefixes without changing the displayed source sample. -/
def approximationSharpnessTower
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    ApproximationSharpnessTower threshold requestedScale totalWindows :=
  Build.sharpnessTower
    certificate requestedScale totalWindows

open Purelib.RationalFunctions.ArgumentPrinciple.CCL in
/-- Total rational-function argument principle with CCL observations attached
to every exact or shrinking zero and pole site returned by Paper I.  Every
site exposes a persistent arithmetic cursor with exact raw-parser semantics;
later requests append to its same prefix and contract its projective sidecar,
while higher sites simultaneously return nested Paper-I boxes. -/
def rationalFunctionArgumentPrincipleWithCCL
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalCCLResult numerator denominator :=
  Build.prove numerator denominator
    denominatorNonzero

end papers.CCL.Chapters.Paper
