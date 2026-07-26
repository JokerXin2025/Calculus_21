/-
    «Calculus_21».Continuity.ClosedInterval
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
set_option linter.style.header false


/-! # Continuous Functions on Closed Interval -/

/-- Minimum Values Theorem -/
theorem Min_Existence {F : Function} {l r : ℝ}
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMinimumPoint F m
:= sorry

/-- Maximum Values Theorem -/
theorem Max_Existence {F : Function} {l r : ℝ}
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMaximumPoint F m
:= sorry

/-- Intermediate Value Theorem -/
theorem Interm_Existence {F : Function} {l r C : ℝ}
    (h_l_lt_r : l < r)
    (h_l_in_dom : l ∈ F.domain)
    (h_r_in_dom : r ∈ F.domain)
    (h_interm : F.map l < C ∧ C < F.map r
                ∨ F.map r < C ∧ C < F.map l)
    (h_cont : isContinuousInIcc F l r)
  : ∃ c ∈ Ioo l r, F.map c = C
:= sorry
