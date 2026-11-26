import PEqualNP.Defs

set_option maxRecDepth 35000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18833 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 14 => decide ((u.val < 7 ∧ v.val < 7 ∧ (v.val + 7 - u.val) % 7 ∈ [0, 1, 3]) ∨ (7 ≤ u.val ∧ 7 ≤ v.val ∧ (u.val + 7 - v.val) % 7 ∈ [0, 1, 3]))) 41 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0, 21]⟩,
      ⟨.or, [1, 22]⟩,
      ⟨.or, [2, 23]⟩,
      ⟨.or, [3, 24]⟩,
      ⟨.or, [4, 25]⟩,
      ⟨.or, [5, 26]⟩,
      ⟨.or, [6, 27]⟩,
      ⟨.or, [14, 7]⟩,
      ⟨.or, [15, 8]⟩,
      ⟨.or, [16, 9]⟩,
      ⟨.or, [17, 10]⟩,
      ⟨.or, [18, 11]⟩,
      ⟨.or, [19, 12]⟩,
      ⟨.or, [20, 13]⟩,
      ⟨.or, [35, 36]⟩,
      ⟨.or, [42, 38]⟩,
      ⟨.and, [28, 43]⟩,
      ⟨.or, [36, 37]⟩,
      ⟨.or, [45, 39]⟩,
      ⟨.and, [29, 46]⟩,
      ⟨.or, [37, 38]⟩,
      ⟨.or, [48, 40]⟩,
      ⟨.and, [30, 49]⟩,
      ⟨.or, [38, 39]⟩,
      ⟨.or, [51, 41]⟩,
      ⟨.and, [31, 52]⟩,
      ⟨.or, [39, 40]⟩,
      ⟨.or, [54, 35]⟩,
      ⟨.and, [32, 55]⟩,
      ⟨.or, [40, 41]⟩,
      ⟨.or, [57, 36]⟩,
      ⟨.and, [33, 58]⟩,
      ⟨.or, [41, 35]⟩,
      ⟨.or, [60, 37]⟩,
      ⟨.and, [34, 61]⟩,
      ⟨.or, [44, 47]⟩,
      ⟨.or, [63, 50]⟩,
      ⟨.or, [64, 53]⟩,
      ⟨.or, [65, 56]⟩,
      ⟨.or, [66, 59]⟩,
      ⟨.or, [67, 62]⟩], 68⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro u
    fin_cases u <;> decide +kernel
