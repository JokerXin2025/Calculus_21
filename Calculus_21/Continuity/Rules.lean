/-
    «Calculus_21».Continuity.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
import «Calculus_21».Limit.Rules
set_option linter.style.header false


/-! # Properties of Function's Continuity -/

/-- Function Limit Composition (Special Version)
    - This version requires outer function `F` to be continuous at `u₀` -/
theorem FuncLimit.CompSV {x₀ u₀ : ℝ} {F G : Function}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F_cont : isContinuousAt F u₀)
  : FuncLimit (F ⊙ G) x₀ (F.map u₀)
:= sorry

/-- Function Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be continuous at `u₀` -/
theorem FuncLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- Left Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be left continuous at `u₀` -/
theorem LeftLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₋ g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim₋ (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- Right Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be right continuous at `u₀` -/
theorem RightLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₊ g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim₊ (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- Continuity of Function Addition -/
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Add h_F.2 h_G.2⟩

/-- Continuity of Function Subtraction -/
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Sub h_F.2 h_G.2⟩

/-- Continuity of Function Multiplication -/
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Mul h_F.2 h_G.2⟩

/-- Continuity of Function Division -/
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= ⟨⟨⟨h_F.1, h_G.1⟩, h_Gx₀_ne_0⟩, FuncLimit.Div h_F.2 h_G.2 h_Gx₀_ne_0⟩

/-- Continuity of Function Composition -/
theorem Continuity.Comp {F G : Function} {x₀ u₀ : ℝ}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F : isContinuousAt F u₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F ⊙ G) x₀
:= by
  have hu_eq : u₀ = G.map x₀ := FuncLimit_Unique h_u₀ h_G.2
  simp_all only []
  constructor
  · exact ⟨h_G.1, h_F.1⟩
  · exact FuncLimit.CompSV h_u₀ h_F
