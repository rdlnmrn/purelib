module

import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation

/-! # Original root certificates retain their actual pair-table stages and gaps -/

namespace TestPurelib.Riemann.RootTailSeparation

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
variable {firstAmbient secondAmbient : CoherentRoot.Box}
variable {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
variable {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
variable {firstStart secondStart : Nat} {count : Nat} {candidates : Fin count → Sequence.ApproximationData}

example (certificate : CoherentRoot.PairSeparation first second firstStart secondStart)
    (left right : Fin count) (left_eq : candidates left = first.approximation)
    (right_eq : candidates right = second.approximation) :
    (certificate.toPairBound candidates left right left_eq right_eq).leftIndex = certificate.leftIndex := rfl

example (certificate : CoherentRoot.PairSeparation first second firstStart secondStart)
    (left right : Fin count) (left_eq : candidates left = first.approximation)
    (right_eq : candidates right = second.approximation) (different : left ≠ right)
    (leftLater rightLater : Nat) (leftOrder : certificate.leftIndex ≤ leftLater)
    (rightOrder : certificate.rightIndex ≤ rightLater) :
    certificate.separation.gap ^ 2 ≤
      normSq ((candidates left).sample leftLater - (candidates right).sample rightLater) :=
  (certificate.toPairBound candidates left right left_eq right_eq).lower different leftLater rightLater
    leftOrder rightOrder

example {point : CoherentRoot.Gaussian} (certificate : CoherentRoot.PointSeparation first point firstStart)
    (left right : Fin count) (left_eq : candidates left = first.approximation)
    (right_read : ∀ index, (candidates right).sample index = point) :
    (certificate.toPairBound candidates left right left_eq right_read).rightIndex = 0 := rfl

example {point : CoherentRoot.Gaussian} (certificate : CoherentRoot.PointSeparation first point firstStart)
    (left right : Fin count) (left_eq : candidates left = first.approximation)
    (right_read : ∀ index, (candidates right).sample index = point) (different : left ≠ right)
    (leftLater rightLater : Nat) (leftOrder : certificate.index ≤ leftLater) :
    certificate.separation.gap ^ 2 ≤
      normSq ((candidates left).sample leftLater - (candidates right).sample rightLater) :=
  (certificate.toPairBound candidates left right left_eq right_read).lower different leftLater rightLater
    leftOrder (Nat.zero_le _)

example (pairs : Sequence.Selection.Pairs candidates) (first second : Fin count)
    (different : first ≠ second) (firstLater secondLater : Nat)
    (firstOrder : pairs.start ≤ firstLater) (secondOrder : pairs.start ≤ secondLater) :
    pairs.gap ≤ normSq ((candidates first).sample firstLater - (candidates second).sample secondLater) :=
  pairs.separated.lower first second different firstLater secondLater firstOrder secondOrder

end TestPurelib.Riemann.RootTailSeparation
