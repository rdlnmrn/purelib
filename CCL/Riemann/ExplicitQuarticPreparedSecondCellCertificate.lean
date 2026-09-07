import CCL.Riemann.ExplicitQuarticPreparedSecondCellCompletion

namespace CCL.Riemann.ExplicitQuarticBranches

private theorem finEightCasesCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  omega0

theorem secondEdgeOrdered (edge : Fin 8) :
    (secondMeshEndpoint (secondEdgeSource edge)).parameter ≤
      (secondEdgeRequest edge).endpoint.parameter := by
  rcases finEightCasesCertificate edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals with_unfolding_all decide

def secondParameterEdge (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge :=
  ⟨secondMeshEndpoint (secondEdgeSource edge),
    (secondEdgeRequest edge).endpoint⟩

def secondTailEight :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 8) secondOwnerEight :=
  .stop (secondMeshEndpoint 8) secondOwnerEight

def secondTailSeven :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 7) secondOwnerSeven :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 7) secondOwnerSeven (secondEdgeRequest 7)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 7) secondOwnerSeven
          (secondEdgeRequest 7)) (secondEdgeOrdered 7)
      secondEdgeSevenStep.canonicalSmall secondEdgeSevenStep.canonicalSmall
        secondTailEight

def secondTailSix :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 6) secondOwnerSix :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 6) secondOwnerSix (secondEdgeRequest 6)
      secondLateCachedSource (secondEdgeOrdered 6) secondLateCanonicalSmall
        secondLateCanonicalSmall secondTailSeven

def secondTailFive :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 5) secondOwnerFive :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 5) secondOwnerFive (secondEdgeRequest 5)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 5) secondOwnerFive
          (secondEdgeRequest 5)) (secondEdgeOrdered 5)
      secondEdgeFiveStep.canonicalSmall secondEdgeFiveStep.canonicalSmall
        secondTailSix

def secondTailFour :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 4) secondOwnerFour :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 4) secondOwnerFour (secondEdgeRequest 4)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 4) secondOwnerFour
          (secondEdgeRequest 4)) (secondEdgeOrdered 4)
      secondEdgeFourStep.canonicalSmall secondEdgeFourStep.canonicalSmall
        secondTailFive

def secondTailThree :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 3) secondOwnerThree :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 3) secondOwnerThree (secondEdgeRequest 3)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 3) secondOwnerThree
          (secondEdgeRequest 3)) (secondEdgeOrdered 3)
      secondEdgeThreeStep.canonicalSmall secondEdgeThreeStep.canonicalSmall
        secondTailFour

def secondTailTwo :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 2) secondOwnerTwo :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 2) secondOwnerTwo (secondEdgeRequest 2)
      secondFirstCachedSource (secondEdgeOrdered 2) secondFirstCanonicalSmall
        secondFirstCanonicalSmall secondTailThree

def secondTailOne :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin (secondMeshEndpoint 1) secondOwnerOne :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
    secondWithin (secondMeshEndpoint 1) secondOwnerOne (secondEdgeRequest 1)
      (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
        secondSegment (secondMeshEndpoint 1) secondOwnerOne
          (secondEdgeRequest 1)) (secondEdgeOrdered 1)
      secondEdgeOneStep.canonicalSmall secondEdgeOneStep.canonicalSmall
        secondTailTwo

private def ownerAtDisplayedStart
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box}
    {start finish : RFAP.ConstructiveGaussian.Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start finish)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt 0))) :
    CCL.Riemann.SquareRootContinuationChain.Owner (polynomial.eval start) := by
  simpa only [CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero] using owner

def secondCellInputOwner :=
  ownerAtDisplayedStart secondSegment secondOwnerZero

theorem secondCellStartOwnerEq :
    CCL.Riemann.PreparedClearPathModels.ownerAtStart secondSegment
      secondCellInputOwner = secondOwnerZero := by
  unfold CCL.Riemann.PreparedClearPathModels.ownerAtStart secondCellInputOwner
    ownerAtDisplayedStart
  rfl

def secondSubdivision :
    CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
      secondWithin CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedClearPathModels.ownerAtStart secondSegment
          secondCellInputOwner) := by
  rw [secondCellStartOwnerEq]
  exact
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached secondSegment
      secondWithin (secondMeshEndpoint 0) secondOwnerZero (secondEdgeRequest 0)
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          secondSegment (secondMeshEndpoint 0) secondOwnerZero
            (secondEdgeRequest 0)) (secondEdgeOrdered 0)
        secondEdgeZeroStep.canonicalSmall secondEdgeZeroStep.canonicalSmall
          secondTailOne

theorem secondTailEightParameterEdges :
    secondTailEight.parameterEdges = [] := rfl

theorem secondTailSevenParameterEdges :
    secondTailSeven.parameterEdges = secondParameterEdge 7 :: [] := by
  simp only [secondTailSeven,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailSixParameterEdges :
    secondTailSix.parameterEdges =
      secondParameterEdge 6 :: secondTailSeven.parameterEdges := by
  simp only [secondTailSix,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailFiveParameterEdges :
    secondTailFive.parameterEdges =
      secondParameterEdge 5 :: secondTailSix.parameterEdges := by
  simp only [secondTailFive,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailFourParameterEdges :
    secondTailFour.parameterEdges =
      secondParameterEdge 4 :: secondTailFive.parameterEdges := by
  simp only [secondTailFour,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailThreeParameterEdges :
    secondTailThree.parameterEdges =
      secondParameterEdge 3 :: secondTailFour.parameterEdges := by
  simp only [secondTailThree,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailTwoParameterEdges :
    secondTailTwo.parameterEdges =
      secondParameterEdge 2 :: secondTailThree.parameterEdges := by
  simp only [secondTailTwo,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondTailOneParameterEdges :
    secondTailOne.parameterEdges =
      secondParameterEdge 1 :: secondTailTwo.parameterEdges := by
  simp only [secondTailOne,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    secondParameterEdge, secondEdgeSource]
  rfl

theorem secondSubdivisionParameterEdges :
    secondSubdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint := by
  calc
    secondSubdivision.parameterEdges =
        secondParameterEdge 0 :: secondTailOne.parameterEdges := by
      simp only [secondSubdivision,
        secondParameterEdge, secondEdgeSource]
      rfl
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondTailTwo.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        secondTailOneParameterEdges
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondTailThree.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          secondTailTwoParameterEdges)
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondParameterEdge 3 ::
          secondTailFour.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          (congrArg (List.cons (secondParameterEdge 2))
            secondTailThreeParameterEdges))
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondParameterEdge 3 ::
          secondParameterEdge 4 :: secondTailFive.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          (congrArg (List.cons (secondParameterEdge 2))
            (congrArg (List.cons (secondParameterEdge 3))
              secondTailFourParameterEdges)))
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondParameterEdge 3 ::
          secondParameterEdge 4 :: secondParameterEdge 5 ::
            secondTailSix.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          (congrArg (List.cons (secondParameterEdge 2))
            (congrArg (List.cons (secondParameterEdge 3))
              (congrArg (List.cons (secondParameterEdge 4))
                secondTailFiveParameterEdges))))
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondParameterEdge 3 ::
          secondParameterEdge 4 :: secondParameterEdge 5 ::
            secondParameterEdge 6 :: secondTailSeven.parameterEdges :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          (congrArg (List.cons (secondParameterEdge 2))
            (congrArg (List.cons (secondParameterEdge 3))
              (congrArg (List.cons (secondParameterEdge 4))
                (congrArg (List.cons (secondParameterEdge 5))
                  secondTailSixParameterEdges)))))
    _ = secondParameterEdge 0 :: secondParameterEdge 1 ::
        secondParameterEdge 2 :: secondParameterEdge 3 ::
          secondParameterEdge 4 :: secondParameterEdge 5 ::
            secondParameterEdge 6 :: secondParameterEdge 7 :: [] :=
      congrArg (List.cons (secondParameterEdge 0))
        (congrArg (List.cons (secondParameterEdge 1))
          (congrArg (List.cons (secondParameterEdge 2))
            (congrArg (List.cons (secondParameterEdge 3))
              (congrArg (List.cons (secondParameterEdge 4))
                (congrArg (List.cons (secondParameterEdge 5))
                  (congrArg (List.cons (secondParameterEdge 6))
                    secondTailSevenParameterEdges))))))
    _ = CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint := by
      with_unfolding_all rfl

theorem secondSubdivisionStrictParameterEdges :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.StrictParameterEdges
      secondSubdivision.parameterEdges := by
  rw [secondSubdivisionParameterEdges]
  exact CCL.Riemann.PreparedClearPathModels.PreparedPath.dyadicEdges_strictParameterEdges
    3 CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      CCL.Riemann.PreparedClearPathModels.oneEndpoint (by decide)

theorem secondSubdivisionStepCount :
    secondSubdivision.stepCount = 2 ^ 3 := by
  calc
    secondSubdivision.stepCount = secondSubdivision.parameterEdges.length :=
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.parameterEdges_length
        secondSubdivision).symm
    _ = (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint).length :=
      congrArg List.length secondSubdivisionParameterEdges
    _ = 2 ^ 3 :=
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges_length 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint

theorem secondDyadicRequests :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
          workingRootDiameter_positive =
      [secondEdgeRequest 0, secondEdgeRequest 1, secondEdgeRequest 2,
        secondEdgeRequest 3, secondEdgeRequest 4, secondEdgeRequest 5,
        secondEdgeRequest 6, secondEdgeRequest 7] := by
  with_unfolding_all rfl

theorem secondTailEightRequests : secondTailEight.requests = [] := rfl

theorem secondTailSevenRequests :
    secondTailSeven.requests = [secondEdgeRequest 7] := by
  simp only [secondTailSeven,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  exact congrArg (List.cons (secondEdgeRequest 7)) secondTailEightRequests

theorem secondTailSixRequests :
    secondTailSix.requests = secondEdgeRequest 6 :: secondTailSeven.requests := by
  simp only [secondTailSix,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondTailFiveRequests :
    secondTailFive.requests = secondEdgeRequest 5 :: secondTailSix.requests := by
  simp only [secondTailFive,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondTailFourRequests :
    secondTailFour.requests = secondEdgeRequest 4 :: secondTailFive.requests := by
  simp only [secondTailFour,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondTailThreeRequests :
    secondTailThree.requests = secondEdgeRequest 3 :: secondTailFour.requests := by
  simp only [secondTailThree,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondTailTwoRequests :
    secondTailTwo.requests = secondEdgeRequest 2 :: secondTailThree.requests := by
  simp only [secondTailTwo,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondTailOneRequests :
    secondTailOne.requests = secondEdgeRequest 1 :: secondTailTwo.requests := by
  simp only [secondTailOne,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem secondSubdivisionRequests :
    secondSubdivision.requests =
      CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
            workingRootDiameter_positive := by
  calc
    secondSubdivision.requests =
        secondEdgeRequest 0 :: secondTailOne.requests := by
      simp only [secondSubdivision]
      rfl
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 ::
        secondTailTwo.requests :=
      congrArg (List.cons (secondEdgeRequest 0)) secondTailOneRequests
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 :: secondEdgeRequest 2 ::
        secondTailThree.requests :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1)) secondTailTwoRequests)
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 :: secondEdgeRequest 2 ::
        secondEdgeRequest 3 :: secondTailFour.requests :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1))
          (congrArg (List.cons (secondEdgeRequest 2))
            secondTailThreeRequests))
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 :: secondEdgeRequest 2 ::
        secondEdgeRequest 3 :: secondEdgeRequest 4 ::
          secondTailFive.requests :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1))
          (congrArg (List.cons (secondEdgeRequest 2))
            (congrArg (List.cons (secondEdgeRequest 3))
              secondTailFourRequests)))
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 :: secondEdgeRequest 2 ::
        secondEdgeRequest 3 :: secondEdgeRequest 4 :: secondEdgeRequest 5 ::
          secondTailSix.requests :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1))
          (congrArg (List.cons (secondEdgeRequest 2))
            (congrArg (List.cons (secondEdgeRequest 3))
              (congrArg (List.cons (secondEdgeRequest 4))
                secondTailFiveRequests))))
    _ = secondEdgeRequest 0 :: secondEdgeRequest 1 :: secondEdgeRequest 2 ::
        secondEdgeRequest 3 :: secondEdgeRequest 4 :: secondEdgeRequest 5 ::
          secondEdgeRequest 6 :: secondTailSeven.requests :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1))
          (congrArg (List.cons (secondEdgeRequest 2))
            (congrArg (List.cons (secondEdgeRequest 3))
              (congrArg (List.cons (secondEdgeRequest 4))
                (congrArg (List.cons (secondEdgeRequest 5))
                  secondTailSixRequests)))))
    _ = [secondEdgeRequest 0, secondEdgeRequest 1, secondEdgeRequest 2,
        secondEdgeRequest 3, secondEdgeRequest 4, secondEdgeRequest 5,
        secondEdgeRequest 6, secondEdgeRequest 7] :=
      congrArg (List.cons (secondEdgeRequest 0))
        (congrArg (List.cons (secondEdgeRequest 1))
          (congrArg (List.cons (secondEdgeRequest 2))
            (congrArg (List.cons (secondEdgeRequest 3))
              (congrArg (List.cons (secondEdgeRequest 4))
                (congrArg (List.cons (secondEdgeRequest 5))
                  (congrArg (List.cons (secondEdgeRequest 6))
                    secondTailSevenRequests))))))
    _ = CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
            workingRootDiameter_positive := secondDyadicRequests.symm

structure SecondSubdivisionCache where
  data : CCL.Riemann.PreparedSheetContinuation.Subdivision secondSegment
    secondWithin CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      (CCL.Riemann.PreparedClearPathModels.ownerAtStart secondSegment
        secondCellInputOwner)
  endpoint_eq : data.endpoint.parameter = 1
  parameterEdges_eq : data.parameterEdges =
    CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint
  strictParameterEdges :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.StrictParameterEdges
      data.parameterEdges
  stepCount_eq : data.stepCount = 2 ^ 3
  requests_eq : data.requests =
    CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
          workingRootDiameter_positive

opaque secondSubdivisionCache : SecondSubdivisionCache :=
  { data := secondSubdivision
    endpoint_eq := by
      simp only [secondSubdivision, secondTailOne, secondTailTwo,
        secondTailThree, secondTailFour, secondTailFive, secondTailSix,
        secondTailSeven, secondTailEight]
      rfl
    parameterEdges_eq := secondSubdivisionParameterEdges
    strictParameterEdges := secondSubdivisionStrictParameterEdges
    stepCount_eq := secondSubdivisionStepCount
    requests_eq := secondSubdivisionRequests }

def secondCompleteSegment :
    CCL.Riemann.PreparedClearPathModels.CompleteSegment secondSegment
      secondWithin secondCellInputOwner where
  subdivision := secondSubdivisionCache.data
  endpoint_eq := secondSubdivisionCache.endpoint_eq

def secondCellPath :=
  CCL.Riemann.BranchCuts.ClearPath.cons secondSegment
    (CCL.Riemann.BranchCuts.ClearPath.nil _)

theorem secondCellPathWithin :
    CCL.Riemann.BranchCuts.ClearPath.WithinAmbient secondCellPath :=
  .cons secondWithin (.nil _)

def secondCellPrepared :
  CCL.Riemann.PreparedClearPathModels.PreparedPath secondCellPath
      secondCellInputOwner :=
  .cons secondSegment (.nil _) secondCellInputOwner
    secondWithin secondCompleteSegment
      (.nil _ secondCompleteSegment.finishOwner)

theorem secondCellPreparedAllEdgesProper :
  CCL.Riemann.PreparedClearPathModels.PreparedPath.AllEdgesProper
      secondCellPrepared := by
  change CCL.Riemann.PreparedClearPathModels.PreparedPath.StrictParameterEdges
      secondSubdivisionCache.data.parameterEdges ∧ True
  exact ⟨secondSubdivisionCache.strictParameterEdges, trivial⟩

theorem secondCellPreparedStepCount :
    secondCellPrepared.stepCount = secondSubdivisionCache.data.stepCount := rfl

theorem secondCellPathSegmentCount : secondCellPath.segmentCount = 1 := rfl

theorem secondCompleteSegmentClearPathEq :
    secondCompleteSegment.clearPath =
      CCL.Riemann.PreparedClearPathModels.dyadicRefineSegment secondSegment
        secondWithin 3 := by
  apply CCL.Riemann.PreparedClearPathModels.CompleteSegment.clearPath_eq_dyadicRefineSegment_of_parameterEdges
  exact secondSubdivisionCache.parameterEdges_eq

theorem secondCellPreparedToClearPath :
    secondCellPrepared.toClearPath =
      CCL.Riemann.PreparedClearPathModels.dyadicRefinePath secondCellPath
        secondCellPathWithin 3 := by
  simp only [secondCellPrepared,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.toClearPath]
  rw [secondCompleteSegmentClearPathEq]
  unfold secondCellPath
  have withinEqual : secondCellPathWithin =
      CCL.Riemann.BranchCuts.ClearPath.WithinAmbient.cons secondWithin
        (.nil _) := Subsingleton.elim _ _
  rw [withinEqual]
  rfl

def secondCellCertifiedDyadic :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.CertifiedDyadic 3
      workingRootDiameter workingRootDiameter_positive secondCellPath
        secondCellInputOwner where
  within := secondCellPathWithin
  prepared := secondCellPrepared
  generated := by
    change secondSubdivisionCache.data.requests =
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
              workingRootDiameter_positive ∧ True
    exact ⟨secondSubdivisionCache.requests_eq, trivial⟩
  prepared_allEdgesProper := secondCellPreparedAllEdgesProper
  prepared_stepCount := by
    rw [secondCellPreparedStepCount, secondSubdivisionCache.stepCount_eq,
      secondCellPathSegmentCount]
    rfl
  prepared_toClearPath := secondCellPreparedToClearPath

end CCL.Riemann.ExplicitQuarticBranches
