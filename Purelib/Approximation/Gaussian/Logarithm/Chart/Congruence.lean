module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
public import Purelib.Approximation.Gaussian.Logarithm.Local.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Process.Coherence.Apart
import Purelib.Approximation.Gaussian.Process.Coherence.Division
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian.Logarithm.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Name.Coherent.Division

section
@[expose] public section

/-!
# Operational congruence for anchored logarithm charts

Two finite chart constructions may use different based process state types and
different proofs of denominator and disk safety.  When their inputs are
operationally equivalent and they retain the same rational factor and
operationally equivalent branch corrections, their actual charted logarithm
outputs are operationally equivalent.

This is the schedule-coherence bridge needed by retryable anchored logarithm
preflight.  It compares finite programs directly; it does not identify
independently selected branches from equality of their exponentials.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Congruence

/-- Scaling by the same exact rational factor respects operational equality of the two coherent inputs. -/
def scaled_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent
      (Reduction.scaled left.name leftBranch.chart.factor)
      (Reduction.scaled right.name rightBranch.chart.factor) := by
  let leftFactor := Coherence.exact
    leftBranch.chart.factor
  let rightFactor := Coherence.exact
    rightBranch.chart.factor
  have factorEquivalent : Gaussian.Equivalence.NamedEquivalent leftFactor.name rightFactor.name := by
    dsimp only [leftFactor, rightFactor]
    rw [factorEqual]
    exact NamedEquivalent.refl _
  simpa only [Reduction.scaled, leftFactor, rightFactor,
    CoherentNamed.mul,
    Coherence.exact] using
    Congruence.coherentMul_respects
      leftFactor rightFactor left right factorEquivalent inputEquivalent

/-- The chart numerators respect input equivalence when the factors agree. -/
def numerator_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent (Coherent.numeratorName left leftBranch).name
      (Coherent.numeratorName right rightBranch).name := by
  let leftScaled : Coherent.CoherentNamed :=
    { name := Reduction.scaled left.name leftBranch.chart.factor
      coherent := Coherent.scaledCoherent
        left.name leftBranch.chart left.coherent }
  let rightScaled : Coherent.CoherentNamed :=
    { name := Reduction.scaled right.name rightBranch.chart.factor
      coherent := Coherent.scaledCoherent
        right.name rightBranch.chart right.coherent }
  let one := Coherence.exact 1
  have scaledEquivalent : Gaussian.Equivalence.NamedEquivalent leftScaled.name rightScaled.name :=
    scaled_respects left right leftBranch rightBranch inputEquivalent
      factorEqual
  simpa only [Coherent.numeratorName, Reduction.numerator, leftScaled,
    rightScaled, one, Reduction.exactOne,
    CoherentNamed.sub,
    Coherence.exact] using
    (Law.Arithmetic.subtraction_respects
      leftScaled rightScaled one one scaledEquivalent
      (NamedEquivalent.refl one.name)).equivalent

/-- The unprepared chart denominators respect input equivalence when the factors agree. -/
def denominator_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent (Coherent.denominatorName left leftBranch).name
      (Coherent.denominatorName right rightBranch).name := by
  let leftScaled : Coherent.CoherentNamed :=
    { name := Reduction.scaled left.name leftBranch.chart.factor
      coherent := Coherent.scaledCoherent
        left.name leftBranch.chart left.coherent }
  let rightScaled : Coherent.CoherentNamed :=
    { name := Reduction.scaled right.name rightBranch.chart.factor
      coherent := Coherent.scaledCoherent
        right.name rightBranch.chart right.coherent }
  let one := Coherence.exact 1
  have scaledEquivalent : Gaussian.Equivalence.NamedEquivalent leftScaled.name rightScaled.name :=
    scaled_respects left right leftBranch rightBranch inputEquivalent
      factorEqual
  simpa only [Coherent.denominatorName, Reduction.denominator, leftScaled,
    rightScaled, one, Reduction.exactOne,
    Coherent.CoherentNamed.add,
    Coherence.exact] using
    Congruence.coherentAdd_respects
      leftScaled rightScaled one one scaledEquivalent
      (NamedEquivalent.refl one.name)

/-- Independently apartified versions of equivalent chart denominators remain operationally equivalent. -/
def preparedDenominator_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent (Coherent.preparedDenominatorName left leftBranch).name
      (Coherent.preparedDenominatorName right rightBranch).name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (CoherentNamed.apartifyEquivalent
        (Coherent.denominatorName left leftBranch) leftBranch.chart.denominatorApart))
    (NamedEquivalent.trans
      (denominator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      (CoherentNamed.apartifyEquivalent
        (Coherent.denominatorName right rightBranch)
        rightBranch.chart.denominatorApart))

/-- The reduced Möbius arguments of two fixed-factor charts respect operational input equivalence. -/
def reduced_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent (Coherent.reducedName left leftBranch).name
      (Coherent.reducedName right rightBranch).name := by
  simpa only [Coherent.reducedName, Coherent.numeratorName, Coherent.preparedDenominatorName,
    Coherent.denominatorName, CoherentNamed.apartify,
    CoherentNamed.div,
    Reduction.reduced,
    Reduction.preparedDenominator,
    Reduction.preparedDenominatorApart] using
    Equivalence.coherentDiv_respects
      (Coherent.numeratorName left leftBranch) (Coherent.numeratorName right rightBranch)
      (Coherent.preparedDenominatorName left leftBranch)
      (Coherent.preparedDenominatorName right rightBranch)
      (Reduction.preparedDenominatorApart left.name
        leftBranch.chart.factor leftBranch.chart.denominatorApart)
      (Reduction.preparedDenominatorApart right.name
        rightBranch.chart.factor rightBranch.chart.denominatorApart)
      (numerator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      (preparedDenominator_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)

/-- The local finite logarithms respect fixed-factor chart input equivalence, independently of the particular
disk-certificate proofs. -/
def localOutput_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor) :
    Gaussian.Equivalence.NamedEquivalent (Coherent.localOutputName left leftBranch).name
      (Coherent.localOutputName right rightBranch).name :=
  Congruence.localLogNamed_respects
    leftBranch.chart.reducedDisk rightBranch.chart.reducedDisk
    (reduced_respects left right leftBranch rightBranch
      inputEquivalent factorEqual)

/-- Full anchored chart congruence. Correction equivalence is an explicit premise because matching exponentials alone
does not identify a logarithm branch. -/
def output_respects
    (left right : Coherent.CoherentNamed)
    (leftBranch : Anchored.AnchoredChart left) (rightBranch : Anchored.AnchoredChart right)
    (inputEquivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name)
    (factorEqual : leftBranch.chart.factor = rightBranch.chart.factor)
    (correctionEquivalent : Gaussian.Equivalence.NamedEquivalent
      leftBranch.chart.correction rightBranch.chart.correction) :
    Gaussian.Equivalence.NamedEquivalent leftBranch.output.name rightBranch.output.name := by
  simpa only [AnchoredChart.output,
    Name.named, Name.localOutput,
    Coherent.localOutputName, Coherent.correctionName,
    Coherent.CoherentNamed.add] using
    Congruence.coherentAdd_respects
      (Coherent.localOutputName left leftBranch) (Coherent.localOutputName right rightBranch)
      (Coherent.correctionName leftBranch) (Coherent.correctionName rightBranch)
      (localOutput_respects left right leftBranch rightBranch
        inputEquivalent factorEqual)
      correctionEquivalent
end Purelib.Approximation.Gaussian.Logarithm.Chart.Congruence

end
