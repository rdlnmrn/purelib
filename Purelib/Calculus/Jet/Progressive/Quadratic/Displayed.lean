module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Calculus.Jet.Quadratic.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Progressive CCL observations of quadratic jet certificates

This module connects the displayed quadratic-change certificates to the
productive CCL layer.  A `CertifiedCalculation` stores one finite rational
certificate, not five unrelated channels.  Its input increment, base value,
output value, slope, and remainder are then exposed as terminating coherent
CCL names.  One request returns certified enclosures and persistent raw CCL
prefixes for all five fields.

This is the exact-input specialization needed by the general progressive jet
construction.  Nothing here turns a non-rational result into a completed
value: the only exact channels introduced below are fields already present in
the supplied Gaussian-rational certificate.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Displayed

open Purelib.Data in
open Purelib.Calculus.Jet in
set_option genInjectivity false in
/-- A retained quadratic certificate at one displayed Gaussian increment.

The wrapper keeps the exact expansion and its remainder bound together. Its channel projections use only the rational
values already stored in that certificate. -/
structure CertifiedCalculation (increment :
  Canonical) where
  /-- The exact quadratic expansion certificate at the indexed increment. -/ displayed : Quadratic.Basic.Certificate
    increment

constructive_injectivity CertifiedCalculation

namespace CertifiedCalculation

section
open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed
/-- Return the exact coherent channel for the indexed increment. -/
def incrementChannel {increment :
  Canonical}
    (_calculation : CertifiedCalculation increment) : CoherentNamed :=
  CoherentNamed.Coherence.exact increment

/-- Return the exact coherent channel for the retained base value. -/
def baseChannel {increment :
  Canonical}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CoherentNamed.Coherence.exact
    calculation.displayed.base

/-- Return the exact coherent channel for the retained output value. -/
def valueChannel {increment :
  Canonical}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CoherentNamed.Coherence.exact
    calculation.displayed.output

/-- Return the exact coherent channel for the retained slope. -/
def slopeChannel {increment :
  Canonical}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CoherentNamed.Coherence.exact
    calculation.displayed.slope

/-- Return the exact coherent channel for the retained remainder. -/
def remainderChannel {increment :
  Canonical}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CoherentNamed.Coherence.exact
    calculation.displayed.remainder
end

end CertifiedCalculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Displayed

end
