module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Riemann.BilinearRelations.Certificate

import Purelib.Riemann.Integration.PreparedRefinementPrograms
public import Purelib.Riemann.Periods.CurveFirstBilinearRelation
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-! Unconditional first-relation certificates for the strict-upper pair on
both concrete genus-two degree shapes. No inverse or energy input is used. -/
namespace Purelib.Examples.Curves.Hyperelliptic.Periods.FirstBilinear

open Purelib.Riemann.BilinearRelations.Certificate (PreNormalizationCertificate)

open Purelib.Riemann.Integration
open Purelib.Riemann.Periods

open Purelib.Riemann.Integration.PreparedRefinementPrograms (automaticStandardPeriodData)
open Purelib.Riemann.Periods.CurveFirstBilinearRelation.PreparedRefinementPrograms
  (automaticPreNormalizationCertificate)
open Purelib.Riemann.Periods.PeriodCurves

section
open Purelib
/-- The original pre-normalization certificate for the displayed quintic curve.

Retains its automatically prepared standard period data and exact finite Stokes closure. -/
def quinticPreNormalization : PreNormalizationCertificate
  (PreparedRefinementPrograms.automaticStandardPeriodData PeriodCurves.quinticCurve) :=
  CurveFirstBilinearRelation.PreparedRefinementPrograms.automaticPreNormalizationCertificate PeriodCurves.quinticCurve

/-- The original pre-normalization certificate for the displayed sextic curve.

Retains its automatically prepared standard period data and exact finite Stokes closure. -/
def sexticPreNormalization : PreNormalizationCertificate
  (PreparedRefinementPrograms.automaticStandardPeriodData PeriodCurves.sexticCurve) :=
  CurveFirstBilinearRelation.PreparedRefinementPrograms.automaticPreNormalizationCertificate PeriodCurves.sexticCurve

end

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Curves.Hyperelliptic
open Purelib.Examples
/-- The quintic primitive period pairing at indices zero and one is equivalent to zero.

Uses the retained pre-normalization certificate's original Stokes closure and period names. -/
def quinticFirstBilinear : Equivalence.NamedEquivalent
    (Periods.Pairing.periodPairingPrimitiveFinish (PreparedRefinementPrograms.automaticStandardPeriodData
      PeriodCurves.quinticCurve) (0 : Fin 2) (1 : Fin 2)).name
    (Coherent.CoherentNamed.Coherence.exact 0).name :=
  quinticPreNormalization.stokesClosure.closed 0 1

/-- The sextic primitive period pairing at indices zero and one is equivalent to zero.

Uses the retained pre-normalization certificate's original Stokes closure and period names. -/
def sexticFirstBilinear : Equivalence.NamedEquivalent
    (Periods.Pairing.periodPairingPrimitiveFinish (PreparedRefinementPrograms.automaticStandardPeriodData
      PeriodCurves.sexticCurve) (0 : Fin 2) (1 : Fin 2)).name
    (Coherent.CoherentNamed.Coherence.exact 0).name :=
  sexticPreNormalization.stokesClosure.closed 0 1

end Purelib.Examples.Curves.Hyperelliptic.Periods.FirstBilinear
