/-
    «Calculus_21».Differential.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr
import «Calculus_21».Differential.Defs
set_option linter.style.header false


/-! # Derivative Expression -/

noncomputable section

open Classical in
/-- Derivative Expression -/
def DerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- Left Derivative Expression -/
def LeftDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- Right Derivative Expression -/
def RightDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- N-th Order Derivative Expression -/
def NthDerivExpr (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isNthDerivableAt n ⟨f, Iii⟩ x₀ then the (choose h)
  else none

end

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)
macro "Dₙ" : term => `(NthDerivExpr)


/-! # Bridges between Derivative & Derivative Expression -/

open Classical in
/-- Derivative → Derivative Expression -/
theorem Deriv_to_DerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : Deriv ⟨f, I⟩ x₀ A)
  : D f x₀ = the A
:= FuncLimit_to_FuncLimitExpr h_deriv

open Classical in
/-- Derivative Expression → Derivative -/
theorem DerivExpr_to_Deriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D f x₀ = the A)
  : Deriv ⟨f, I⟩ x₀ A
:= sorry

open Classical in
/-- Left Derivative → Left Derivative Expression -/
theorem LeftDeriv_to_LeftDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : LeftDeriv ⟨f, I⟩ x₀ A)
  : D₋ f x₀ = the A
:= LeftLimit_to_LeftLimitExpr h_deriv

open Classical in
/-- Left Derivative Expression → Left Derivative -/
theorem LeftDerivExpr_to_LeftDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₋ f x₀ = the A)
  : LeftDeriv ⟨f, I⟩ x₀ A
:= sorry

open Classical in
/-- Right Derivative → Right Derivative Expression -/
theorem RightDeriv_to_RightDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : RightDeriv ⟨f, I⟩ x₀ A)
  : D₊ f x₀ = the A
:= RightLimit_to_RightLimitExpr h_deriv

open Classical in
/-- Right Derivative Expression → Right Derivative -/
theorem RightDerivExpr_to_RightDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₊ f x₀ = the A)
  : RightDeriv ⟨f, I⟩ x₀ A
:= sorry

open Classical in
/-- N-th Order Derivative → N-th Order Derivative Expression -/
theorem NthDeriv_to_NthDerivExpr {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : NthDeriv n ⟨f, Iii⟩ x₀ A)
  : Dₙ n f x₀ = the A
:= sorry

open Classical in
/-- N-th Order Derivative Expression → N-th Order Derivative -/
theorem NthDerivExpr_to_NthDeriv {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Dₙ n f x₀ = the A)
  : NthDeriv n ⟨f, Iii⟩ x₀ A
:= sorry

/-- Derivative → Left Derivative (Expression) -/
theorem DerivExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : D₋ f x₀ =? D f x₀
:= FuncLimitExpr_toLeft

/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : D₊ f x₀ =? D f x₀
:= FuncLimitExpr_toRight
