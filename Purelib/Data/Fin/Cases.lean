module

-- Retain the existing public field-law contract for current finite-case clients.
public import Purelib.Algebra.Field.ExplicitField
-- Fin numeral signatures retain the owned successor nonzero certificates.
public import Purelib.Data.Nat.Order
import Purelib.Data.Fin

/-!
# Displayed coordinate cases for bounded finite indices

These certificates enumerate the coordinates of the displayed finite types and
split successor-size indices into their first coordinate or retained predecessor.
Each proof uses natural constructor cases and the supplied strict finite bound.
-/

namespace Purelib.Examples.Riemann.ExplicitLegendreConnectors

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreConnectors

namespace Purelib.Examples.Riemann.ExplicitLegendreFrame

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreFrame

namespace Purelib.Examples.Riemann.ExplicitLegendreLoopBaseBranches

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreLoopBaseBranches

namespace Purelib.Examples.Riemann.ExplicitLegendreOneLoop

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreOneLoop

namespace Purelib.Examples.Riemann.ExplicitLegendrePreparedPeriods

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendrePreparedPeriods

namespace Purelib.Examples.Riemann.ExplicitLegendreSegment

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreSegment

namespace Purelib.Examples.Riemann.ExplicitLegendreZeroLoop

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

end Purelib.Examples.Riemann.ExplicitLegendreZeroLoop

namespace Purelib.Data.Fin.Cases

public section

/-- Every index of `Fin 3` equals one of its 3 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem three (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (rfl))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (bound)))))

/-- Every index of `Fin 2` equals one of its 2 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finTwo_cases (index : Fin 2) : index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (rfl)
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))

/-- Every seven-coordinate finite index equals one of its displayed coordinates.

Natural constructor cases retain the original coordinate and strict bound. That
bound excludes every successor beyond the seven displayed values. -/
public theorem seven (index : Fin 7) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem aBackwardSampleFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 2` equals one of its 2 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem bBackwardSampleFinTwoCases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (rfl)
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem bBackwardSampleFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 2` equals one of its 2 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem bBackwardSumFinTwoCases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (rfl)
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem bBackwardSumFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 2` equals one of its 2 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem bForwardSampleFinTwoCases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (rfl)
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem bForwardSampleFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 2` equals one of its 2 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem bForwardSumFinTwoCases (index : Fin 2) :
    index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (rfl)
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem bForwardSumFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 4` equals one of its 4 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem quarticCycleFinFourCases (index : Fin 4) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (rfl)))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem horizontalFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem horizontalSumFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesABackwardHorizontalSecond (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCases (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesEighth (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesEighth (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesEighthCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesFifth (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesFifth (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesFifthCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesFourth (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesFourth (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesFourthCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 6` equals one of its 6 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finSixCasesHorizontal (index : Fin 6) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finEightCasesCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesSecond (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finEightCasesSecond (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesSeventh (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesSeventh (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesSeventhCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesSixth (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesSixth (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesSixthCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 9` equals one of its 9 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finNineCasesThird (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesThird (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
private theorem finEightCasesThirdCertificate (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 4` equals one of its 4 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinFourCases (index : Fin 4) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (rfl)))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every index of `Fin 4` equals one of its 4 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryFinFourCases (index : Fin 4) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (rfl)))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))

/-- Every index of `Fin 8` equals one of its 8 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
theorem ExplicitQuarticPreparedARightSampleCertificatesPart1.aRightBoundaryFinEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (bound))))))))))

/-- Every successor-size finite index is first or the successor of a predecessor.

The natural coordinate determines the branch. The successor branch retains
the predecessor coordinate and its bound from the supplied finite index. -/
public theorem fin_eq_zero_or_eq_succ {count : Nat}
    (index : Fin (count + 1)) :
    index = 0 ∨ ∃ previous : Fin count, index = previous.succ := by
  refine Purelib.Data.Fin.cases_induction ?_ (fun previous => ?_) index
  · exact Or.inl rfl
  · exact Or.inr ⟨previous, rfl⟩

/-- Every index of `Fin 5` equals one of its 5 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finFiveCases (index : Fin 5) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (rfl))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))

/-- Every index of `Fin 5` equals one of its 5 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finFive_cases (index : Fin 5) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (rfl))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound)))))))

/-- Every index of `Fin 6` equals one of its 6 displayed coordinates.

Natural constructor cases identify each coordinate with its displayed finite
value. The retained strict bound excludes every further successor. -/
public theorem finSix_cases (index : Fin 6) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 := by
  rcases index with ⟨value, bound⟩
  rcases value with _ | value
  · exact Or.inl rfl
  rcases value with _ | value
  · exact Or.inr (Or.inl rfl)
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inl rfl))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rcases value with _ | value
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))
  exact False.elim (Nat.not_lt_zero value (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (bound))))))))

end

end Purelib.Data.Fin.Cases
