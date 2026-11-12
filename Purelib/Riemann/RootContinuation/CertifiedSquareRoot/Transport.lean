module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Clearance
public import Purelib.Approximation.Gaussian.Name.Coherent.Transport

/-! # Equal-parameter transport of retained root certificates and observations

Exact radicand equality reindexes the complete original certificate and
its paid observation. The coherent value, actual observation, witness and
selected sampling indices remain the original ones. Paired clearance is
transported with those same observations; no certificate, process state or
comparison is reconstructed.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

namespace Certificate

/-- Reindex the complete original certificate along exact equality of its radicand parameter. -/
@[expose] def castParameter {first last : Canonical} (equal : first = last)
    (root : Certificate first) : Certificate last :=
  Eq.mp (congrArg Certificate equal) root

/-- Parameter reindexing retains the identical complete original coherent value cache. -/
theorem castParameter_value {first last : Canonical} (equal : first = last) (root : Certificate first) :
    (root.castParameter equal).value = root.value := by
  cases equal
  rfl

end Certificate

namespace Sampling

namespace ResidualObservation

/-- Reindex the same paid observation together with its complete original root certificate. -/
@[expose] def castParameter {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    ResidualObservation (root.castParameter equal) accuracy := by
  cases equal
  exact sample

/-- The parameter cast retains the complete actual original observation cache. -/
theorem castParameter_observation {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    (sample.castParameter equal).observation = sample.observation := by
  cases equal
  rfl

/-- The parameter cast preserves the same actual process state under the original complete value equality. -/
theorem castParameter_state {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    Name.Coherent.CoherentNamed.castState (root.castParameter_value equal)
      (sample.castParameter equal).state = sample.state := by
  cases equal
  rfl

/-- The same retained witness is read after reindexing the original root parameter. -/
theorem castParameter_reading {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    (sample.castParameter equal).reading = sample.reading := by
  cases equal
  rfl

/-- Reindexing retains the identical selected original left sampling index. -/
theorem castParameter_leftIndex {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    (sample.castParameter equal).comparison.leftIndex = sample.comparison.leftIndex := by
  cases equal
  rfl

/-- Reindexing retains the original minimum sampling index that pays the residual spread. -/
theorem castParameter_minimumIndex {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    (sample.castParameter equal).minimumIndex = sample.minimumIndex := by
  cases equal
  rfl

/-- Reindexing retains the identical selected original right comparison index. -/
theorem castParameter_rightIndex {first last : Canonical} {root : Certificate first} {accuracy : AccuracyRequest}
    (equal : first = last) (sample : ResidualObservation root accuracy) :
    (sample.castParameter equal).comparison.rightIndex = sample.comparison.rightIndex := by
  cases equal
  rfl

end ResidualObservation

namespace Clearance

/-- Reindex the complete paired clearance with the same two original observations and radicand equalities. -/
@[expose] def castParameters {firstParameter firstTarget lastParameter lastTarget : Canonical}
    {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    {first : ResidualObservation firstRoot firstAccuracy} {last : ResidualObservation lastRoot lastAccuracy}
    (firstEqual : firstParameter = firstTarget) (lastEqual : lastParameter = lastTarget)
    (clearance : Clearance first last) : Clearance (first.castParameter firstEqual) (last.castParameter lastEqual) := by
  cases firstEqual
  cases lastEqual
  exact clearance

/-- The paired parameter cast retains the original quantitative source margin. -/
theorem castParameters_sourceFloor {firstParameter firstTarget lastParameter lastTarget : Canonical}
    {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    {first : ResidualObservation firstRoot firstAccuracy} {last : ResidualObservation lastRoot lastAccuracy}
    (firstEqual : firstParameter = firstTarget) (lastEqual : lastParameter = lastTarget)
    (clearance : Clearance first last) :
    (clearance.castParameters firstEqual lastEqual).sourceFloor = clearance.sourceFloor := by
  cases firstEqual
  cases lastEqual
  rfl

/-- The same paired parameter cast retains the distinct original target margin. -/
theorem castParameters_targetFloor {firstParameter firstTarget lastParameter lastTarget : Canonical}
    {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    {first : ResidualObservation firstRoot firstAccuracy} {last : ResidualObservation lastRoot lastAccuracy}
    (firstEqual : firstParameter = firstTarget) (lastEqual : lastParameter = lastTarget)
    (clearance : Clearance first last) :
    (clearance.castParameters firstEqual lastEqual).targetFloor = clearance.targetFloor := by
  cases firstEqual
  cases lastEqual
  rfl

/-- The paired cast preserves the same actual-observation sum margin. -/
theorem castParameters_sumFloor {firstParameter firstTarget lastParameter lastTarget : Canonical}
    {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    {first : ResidualObservation firstRoot firstAccuracy} {last : ResidualObservation lastRoot lastAccuracy}
    (firstEqual : firstParameter = firstTarget) (lastEqual : lastParameter = lastTarget)
    (clearance : Clearance first last) :
    (clearance.castParameters firstEqual lastEqual).sumFloor = clearance.sumFloor := by
  cases firstEqual
  cases lastEqual
  rfl

end Clearance

end Sampling

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot
