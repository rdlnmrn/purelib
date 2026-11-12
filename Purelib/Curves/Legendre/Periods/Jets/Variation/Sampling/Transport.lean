module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport

/-! # Exact spatial-index transport of the original sampled parameter jet

An equality of spatial points reindexes both complete original root
certificates and the same sampled jet. The source and target observations,
their selected process states and indices, clearance and inverse/cubic
caches remain identical; no constructor or sampling request is repeated.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.SampledJet

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Riemann.RootContinuation

variable {parameter increment first last : Canonical}
variable {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter first)}
variable {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) first)}
variable {unit : Norm.Basic.normSq increment ≤ 1}

/-- Reindex the same sampled jet along exact spatial equality and both original certificate parameter casts. -/
@[expose] def castPoint (equal : first = last) (jet : SampledJet parameter increment first source target unit) :
    SampledJet parameter increment last
      (source.castParameter (congrArg (Polynomials.curveValue parameter) equal))
      (target.castParameter (congrArg (Polynomials.curveValue (parameter + increment)) equal)) unit := by
  cases equal
  exact jet

/-- Exact spatial reindexing retains the original residual accuracy request. -/
theorem castPoint_accuracy (equal : first = last) (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).accuracy = jet.accuracy := by
  cases equal
  rfl

/-- The complete original source residual-observation record survives its exact spatial-index transport. -/
theorem castPoint_sourceSample (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    HEq (jet.castPoint equal).sourceSample jet.sourceSample := by
  cases equal
  rfl

/-- Spatial reindexing retains the entire distinct original target residual-observation record. -/
theorem castPoint_targetSample (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    HEq (jet.castPoint equal).targetSample jet.targetSample := by
  cases equal
  rfl

/-- Spatial reindexing preserves the complete actual source observation without another root request. -/
theorem castPoint_sourceObservation (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).sourceSample.observation = jet.sourceSample.observation := by
  cases equal
  rfl

/-- Spatial reindexing retains the complete distinct original target observation. -/
theorem castPoint_targetObservation (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).targetSample.observation = jet.targetSample.observation := by
  cases equal
  rfl

/-- The same actual selected source reading is used after the original spatial-index transport. -/
theorem castPoint_sourceReading (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).sourceSample.reading = jet.sourceSample.reading := by
  cases equal
  rfl

/-- The distinct original selected target reading is unchanged by the same spatial-index transport. -/
theorem castPoint_targetReading (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).targetSample.reading = jet.targetSample.reading := by
  cases equal
  rfl

/-- The original source process state is retained under the complete original certificate-value equality. -/
theorem castPoint_sourceState (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    Name.Coherent.CoherentNamed.castState
      (source.castParameter_value (congrArg (Polynomials.curveValue parameter) equal))
      (jet.castPoint equal).sourceSample.state = jet.sourceSample.state := by
  cases equal
  rfl

/-- The distinct original target process state survives its matching complete certificate-value equality. -/
theorem castPoint_targetState (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    Name.Coherent.CoherentNamed.castState
      (target.castParameter_value (congrArg (Polynomials.curveValue (parameter + increment)) equal))
      (jet.castPoint equal).targetSample.state = jet.targetSample.state := by
  cases equal
  rfl

/-- The original selected source square-comparison index is unchanged by spatial reindexing. -/
theorem castPoint_sourceIndex (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).sourceSample.comparison.leftIndex = jet.sourceSample.comparison.leftIndex := by
  cases equal
  rfl

/-- The distinct original selected target square-comparison index is retained. -/
theorem castPoint_targetIndex (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).targetSample.comparison.leftIndex = jet.targetSample.comparison.leftIndex := by
  cases equal
  rfl

/-- The same selected source square-comparison right index is preserved. -/
theorem castPoint_sourceRightIndex (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).sourceSample.comparison.rightIndex = jet.sourceSample.comparison.rightIndex := by
  cases equal
  rfl

/-- The independently selected target square-comparison right index is retained. -/
theorem castPoint_targetRightIndex (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).targetSample.comparison.rightIndex = jet.targetSample.comparison.rightIndex := by
  cases equal
  rfl

/-- Spatial reindexing preserves the actual source minimum index paying its original spread request. -/
theorem castPoint_sourceMinimum (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).sourceSample.minimumIndex = jet.sourceSample.minimumIndex := by
  cases equal
  rfl

/-- The independently paid original target minimum index is unchanged. -/
theorem castPoint_targetMinimum (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).targetSample.minimumIndex = jet.targetSample.minimumIndex := by
  cases equal
  rfl

/-- The spatial cast keeps the complete original shared inverse certificate cache. -/
theorem castPoint_inverse (equal : first = last) (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).inverse = jet.inverse := by
  cases equal
  rfl

/-- The same original cubic certificate cache survives the exact spatial-index transport. -/
theorem castPoint_cubic (equal : first = last) (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).cubic = jet.cubic := by
  cases equal
  rfl

/-- Each value row reads the original cached scalar certificate after spatial transport. -/
theorem castPoint_value (equal : first = last) (jet : SampledJet parameter increment first source target unit)
    (coordinate : Fin 2) : (jet.castPoint equal).value coordinate = jet.value coordinate := by
  cases equal
  rfl

/-- Each first derivative row uses its same original scalar certificate cache after reindexing. -/
theorem castPoint_first (equal : first = last) (jet : SampledJet parameter increment first source target unit)
    (coordinate : Fin 2) : (jet.castPoint equal).first coordinate = jet.first coordinate := by
  cases equal
  rfl

/-- The complete original paired-clearance record retains both observation owners after spatial reindexing. -/
theorem castPoint_clearance (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    HEq (jet.castPoint equal).clearance jet.clearance := by
  cases equal
  rfl

/-- The exact spatial-index transport preserves the source candidate floor on the identical observation. -/
theorem castPoint_sourceFloor (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).clearance.sourceFloor = jet.clearance.sourceFloor := by
  cases equal
  rfl

/-- The target candidate margin remains on the same distinct original observation. -/
theorem castPoint_targetFloor (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).clearance.targetFloor = jet.clearance.targetFloor := by
  cases equal
  rfl

/-- The original paired-observation sum margin is unchanged by exact spatial transport. -/
theorem castPoint_sumFloor (equal : first = last)
    (jet : SampledJet parameter increment first source target unit) :
    (jet.castPoint equal).clearance.sumFloor = jet.clearance.sumFloor := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.SampledJet
