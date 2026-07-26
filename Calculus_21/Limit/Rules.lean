/-
    «Calculus_21».Limit.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr
set_option linter.style.header false


/-! # Basic Limits -/

/-! For more limits, please refer to `Continuity.Elementary`. -/


/-! # Limit Calculation Rules -/

/-!
The rules for __Function's Multiplicative Scalar Power__ are not provided here,
which can be regarded as a composite function by the following conclusion:
```lean
example {f : ℝ → ℝ} {n : ℕ} : f ^ n = npow n ∘ f := rfl
```
-/

/-- Sequence Limit of Scalar Multiplication -/
theorem SeqLimit.SMul {A : Sequence} {k L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (k • A) (k * L₁)
:= sorry

/-- Sequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul {a : ℕ → ℝ} {k : ℝ}
  : limₙ (k • a) =? the k * limₙ a
:= sorry

/-- Function Limit of Scalar Multiplication -/
theorem FuncLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Function Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim (k • f) x₀ =? the k * lim f x₀
:= sorry

/-- Left Limit of Scalar Multiplication -/
theorem LeftLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₋ (k • f) x₀ =? the k * lim₋ f x₀
:= sorry

/-- Right Limit of Scalar Multiplication -/
theorem RightLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₊ (k • f) x₀ =? the k * lim₊ f x₀
:= sorry

/-- Sequence Limit of Additive Inverse -/
theorem SeqLimit.Neg {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (-A) (-L₁)
:= sorry

/-- Sequence Limit of Additive Inverse (Expression) -/
theorem SeqLimitExpr.Neg {a : ℕ → ℝ}
  : limₙ (-a) =? - limₙ a
:= sorry

/-- Function Limit of Additive Inverse -/
theorem FuncLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (-F) x₀ (-L₁)
:= sorry

/-- Function Limit of Additive Inverse (Expression) -/
theorem FuncLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim (-f) x₀ =? - lim f x₀
:= sorry

/-- Left Limit of Additive Inverse -/
theorem LeftLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (-F) x₀ (-L₁)
:= sorry

/-- Left Limit of Additive Inverse (Expression) -/
theorem LeftLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (-f) x₀ =? - lim₋ f x₀
:= sorry

/-- Right Limit of Additive Inverse -/
theorem RightLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (-F) x₀ (-L₁)
:= sorry

/-- Right Limit of Additive Inverse (Expression) -/
theorem RightLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (-f) x₀ =? - lim₊ f x₀
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power -/
theorem SeqLimit.MSPow {A : Sequence} {n : ℕ} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (A ^ n) (L₁ ^ n)
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power (Expression) -/
theorem SeqLimitExpr.MSPow {a : ℕ → ℝ} {n : ℕ}
  : limₙ (a ^ n) =? limₙ a ^ the (n : ℝ)
:= sorry

/-- Sequence Limit of Multiplicative Inverse -/
theorem SeqLimit.Inv {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
    (h_L₁_ne0 : L₁ ≠ 0)
  : SeqLimit A⁻¹ L₁⁻¹
:= sorry

/-- Sequence Limit of Multiplicative Inverse (Expression) -/
theorem SeqLimitExpr.Inv {a : ℕ → ℝ}
  : limₙ a⁻¹ =? (limₙ a)⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse -/
theorem FuncLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
    (h_L₁_ne0 : L₁ ≠ 0)
  : FuncLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse (Expression) -/
theorem FuncLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim f⁻¹ x₀ =? (lim f x₀)⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse -/
theorem LeftLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
    (h_L₁_ne0 : L₁ ≠ 0)
  : LeftLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse (Expression) -/
theorem LeftLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f⁻¹ x₀ =? (lim₋ f x₀)⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse -/
theorem RightLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
    (h_L₁_ne0 : L₁ ≠ 0)
  : RightLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse (Expression) -/
theorem RightLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f⁻¹ x₀ =? (lim₊ f x₀)⁻¹
:= sorry

/-- Sequence Limit Addition -/
theorem SeqLimit.Add {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A + B) (L₁ + L₂)
:= sorry

/-- Sequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add {a b : ℕ → ℝ}
  : limₙ (a + b) =? limₙ a + limₙ b
:= sorry

/-- Function Limit Addition -/
theorem FuncLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Function Limit Addition (Expression) -/
theorem FuncLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f + g) x₀ =? lim f x₀ + lim g x₀
:= sorry

/-- Left Limit Addition -/
theorem LeftLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f + g) x₀ =? lim₋ f x₀ + lim₋ g x₀
:= sorry

/-- Right Limit Addition -/
theorem RightLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f + g) x₀ =? lim₊ f x₀ + lim₊ g x₀
:= sorry

/-- Sequence Limit Subtraction -/
theorem SeqLimit.Sub {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A - B) (L₁ - L₂)
:= sorry

/-- Sequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub {a b : ℕ → ℝ}
  : limₙ (a - b) =? limₙ a - limₙ b
:= sorry

/-- Function Limit Subtraction -/
theorem FuncLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Function Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f - g) x₀ =? lim f x₀ - lim g x₀
:= sorry

/-- Left Limit Subtraction -/
theorem LeftLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f - g) x₀ =? lim₋ f x₀ - lim₋ g x₀
:= sorry

/-- Right Limit Subtraction -/
theorem RightLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f - g) x₀ =? lim₊ f x₀ - lim₊ g x₀
:= sorry

/-- Sequence Limit Multiplication -/
theorem SeqLimit.Mul {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A * B) (L₁ * L₂)
:= sorry

/-- Sequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul {a b : ℕ → ℝ}
  : limₙ (a * b) =? limₙ a * limₙ b
:= sorry

/-- Function Limit Multiplication -/
theorem FuncLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Function Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f * g) x₀ =? lim f x₀ * lim g x₀
:= sorry

/-- Left Limit Multiplication -/
theorem LeftLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f * g) x₀ =? lim₋ f x₀ * lim₋ g x₀
:= sorry

/-- Right Limit Multiplication -/
theorem RightLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f * g) x₀ =? lim₊ f x₀ * lim₊ g x₀
:= sorry

/-- Sequence Limit Division -/
theorem SeqLimit.Div {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : SeqLimit (A / B) (L₁ / L₂)
:= sorry

/-- Sequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div {a b : ℕ → ℝ}
  : limₙ (a / b) =? limₙ a / limₙ b
:= sorry

/-- Function Limit Division -/
theorem FuncLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : FuncLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Function Limit Division (Expression) -/
theorem FuncLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f / g) x₀ =? lim f x₀ / lim g x₀
:= sorry

/-- Left Limit Division -/
theorem LeftLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : LeftLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f / g) x₀ =? lim₋ f x₀ / lim₋ g x₀
:= sorry

/-- Right Limit Division -/
theorem RightLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : RightLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Right Limit Division (Expression) -/
theorem RightLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f / g) x₀ =? lim₊ f x₀ / lim₊ g x₀
:= sorry

/-- Function Limit Composition -/
theorem FuncLimit.Comp {x₀ u₀ L₁ : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_G_ne_u₀ : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, G.map x ≠ u₀)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_L : FuncLimit F u₀ L₁)
  : FuncLimit (F ⊙ G) x₀ L₁
:= sorry

/-- Squeeze Theorem for Sequence Limit -/
theorem SeqLimit_Squeeze {A B C : Sequence} {L : ℝ}
    (h_A : SeqLimit A L) (h_C : SeqLimit C L)
    (h_B_inf : B.final = none)
    (h_sqz : ∃ N : ℕ, ∀ n > N, A.map n ≤ B.map n ∧ B.map n ≤ C.map n)
  : SeqLimit B L
:= sorry

/-- Squeeze Theorem for Sequence Limit (Expression) -/
theorem SeqLimit.Squeeze {a b c : ℕ → ℝ} {L₁ : ℝ}
    (h_a : limₙ a = the L₁) (h_c : limₙ c = the L₁)
    (h_sqz : ∃ N : ℕ, ∀ n > N, a n ≤ b n ∧ b n ≤ c n)
  : limₙ b = the L₁
:= sorry

/-- Squeeze Theorem for Function Limit -/
theorem FuncLimit_Squeeze {F G H : Function} {x₀ L : ℝ}
    (h_F : FuncLimit F x₀ L) (h_H : FuncLimit H x₀ L)
    (h_G_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain)
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, F.map x ≤ G.map x ∧ G.map x ≤ H.map x)
  : FuncLimit G x₀ L
:= sorry

/-- Squeeze Theorem for Function Limit (Expression) -/
theorem FuncLimit.Squeeze {f g h : ℝ → ℝ} {x₀ L₁ : ℝ}
    (h_f : lim f x₀ = the L₁) (h_h : lim h x₀ = the L₁)
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≤ g x ∧ g x ≤ h x)
  : lim g x₀ = the L₁
:= sorry
