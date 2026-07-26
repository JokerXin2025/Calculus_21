/-
    «Calculus_21».Limit.Tactics.Calc
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Tactics
import «Calculus_21».Continuity.Elementary
import «Calculus_21».Limit.Tactics.Congr
set_option linter.style.header false


/-! # Preparations -/

class AutoLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim f x₀ = the val

class AutoLeftLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₋ f x₀ = the val

class AutoRightLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₊ f x₀ = the val

private instance funclimit_patch₁ {k x₀ : ℝ}
  : AutoLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim (k + ·) x₀
         =? lim (const k) x₀ + lim id x₀
            := FuncLimitExpr.Add
      _  =  the k + the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k + x₀)
            := rfl

private instance leftlimit_patch₁ {k x₀ : ℝ}
  : AutoLeftLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim₋ (k + ·) x₀
         =? lim₋ (const k) x₀ + lim₋ id x₀
            := LeftLimitExpr.Add
      _  =  the k + the x₀
            := by rw [LeftLimitExpr.Constant, LeftLimitExpr.Identity]
      _  =  the (k + x₀)
            := rfl

private instance rightlimit_patch₁ {k x₀ : ℝ}
  : AutoRightLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim₊ (k + ·) x₀
         =? lim₊ (const k) x₀ + lim₊ id x₀
            := RightLimitExpr.Add
      _  =  the k + the x₀
            := by rw [RightLimitExpr.Constant, RightLimitExpr.Identity]
      _  =  the (k + x₀)
            := rfl

private instance funclimit_patch₁' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance leftlimit_patch₁' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance rightlimit_patch₁' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoLeftLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance funclimit_patch₂ {k x₀ : ℝ}
  : AutoLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim (k - ·) x₀
         =? lim (const k) x₀ - lim id x₀
            := FuncLimitExpr.Sub
      _  =  the k - the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k - x₀)
            := rfl

private instance leftlimit_patch₂ {k x₀ : ℝ}
  : AutoLeftLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim₋ (k - ·) x₀
         =? lim₋ (const k) x₀ - lim₋ id x₀
            := LeftLimitExpr.Sub
      _  =  the k - the x₀
            := by rw [LeftLimitExpr.Constant, LeftLimitExpr.Identity]
      _  =  the (k - x₀)
            := rfl

private instance rightlimit_patch₂ {k x₀ : ℝ}
  : AutoRightLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim₊ (k - ·) x₀
         =? lim₊ (const k) x₀ - lim₊ id x₀
            := RightLimitExpr.Sub
      _  =  the k - the x₀
            := by rw [RightLimitExpr.Constant, RightLimitExpr.Identity]
      _  =  the (k - x₀)
            := rfl

private instance funclimit_patch₂' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance leftlimit_patch₂' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance rightlimit_patch₂' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance funclimit_patch₃ {k x₀ : ℝ}
  : AutoLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim (k * ·) x₀
         =? lim (const k) x₀ * lim id x₀
            := FuncLimitExpr.Mul
      _  =  the k * the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k * x₀)
            := rfl

private instance leftlimit_patch₃ {k x₀ : ℝ}
  : AutoLeftLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim₋ (k * ·) x₀
         =? lim₋ (const k) x₀ * lim₋ id x₀
            := LeftLimitExpr.Mul
      _  =  the k * the x₀
            := by rw [LeftLimitExpr.Constant, LeftLimitExpr.Identity]
      _  =  the (k * x₀)
            := rfl

private instance rightlimit_patch₃ {k x₀ : ℝ}
  : AutoRightLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim₊ (k * ·) x₀
         =? lim₊ (const k) x₀ * lim₊ id x₀
            := RightLimitExpr.Mul
      _  =  the k * the x₀
            := by rw [RightLimitExpr.Constant, RightLimitExpr.Identity]
      _  =  the (k * x₀)
            := rfl

private instance funclimit_patch₃' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance leftlimit_patch₃' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance rightlimit_patch₃' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance funclimit_patch₄ {k x₀ : ℝ}
  : AutoLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (k / ·) x₀
         =? lim (const k) x₀ / lim id x₀
            := FuncLimitExpr.Div
      _  =  the k / the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k / x₀)
            := by rw [UdEqual.calc_div h_x₀_ne0]

private instance leftlimit_patch₄ {k x₀ : ℝ}
  : AutoLeftLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₋ (k / ·) x₀
         =? lim₋ (const k) x₀ / lim₋ id x₀
            := LeftLimitExpr.Div
      _  =  the k / the x₀
            := by rw [LeftLimitExpr.Constant, LeftLimitExpr.Identity]
      _  =  the (k / x₀)
            := by rw [UdEqual.calc_div h_x₀_ne0]

private instance rightlimit_patch₄ {k x₀ : ℝ}
  : AutoRightLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₊ (k / ·) x₀
         =? lim₊ (const k) x₀ / lim₊ id x₀
            := RightLimitExpr.Div
      _  =  the k / the x₀
            := by rw [RightLimitExpr.Constant, RightLimitExpr.Identity]
      _  =  the (k / x₀)
            := by rw [UdEqual.calc_div h_x₀_ne0]

private instance funclimit_patch₄' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance leftlimit_patch₄' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance rightlimit_patch₄' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance funclimit_patch₅ {x₀ : ℝ}
  : AutoLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim (-·) x₀
         =? - lim id x₀
            := FuncLimitExpr.Neg
      _  =  - the x₀
            := by rw [FuncLimitExpr.Identity]
      _  =  the (-x₀)
            := rfl

private instance leftlimit_patch₅ {x₀ : ℝ}
  : AutoLeftLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim₋ (-·) x₀
         =? - lim₋ id x₀
            := LeftLimitExpr.Neg
      _  =  - the x₀
            := by rw [LeftLimitExpr.Identity]
      _  =  the (-x₀)
            := rfl

private instance rightlimit_patch₅ {x₀ : ℝ}
  : AutoRightLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim₊ (-·) x₀
         =? - lim₊ id x₀
            := RightLimitExpr.Neg
      _  =  - the x₀
            := by rw [RightLimitExpr.Identity]
      _  =  the (-x₀)
            := rfl

private instance funclimit_patch₅' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance leftlimit_patch₅' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance rightlimit_patch₅' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance funclimit_patch₆ {x₀ : ℝ}
  : AutoLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (·⁻¹) x₀
         =? (lim id x₀)⁻¹
            := FuncLimitExpr.Inv
      _  =  (the x₀)⁻¹
            := by rw [FuncLimitExpr.Identity]
      _  =  the x₀⁻¹
            := by rw [UdEqual.calc_inv h_x₀_ne0]

private instance leftlimit_patch₆ {x₀ : ℝ}
  : AutoLeftLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₋ (·⁻¹) x₀
         =? (lim₋ id x₀)⁻¹
            := LeftLimitExpr.Inv
      _  =  (the x₀)⁻¹
            := by rw [LeftLimitExpr.Identity]
      _  =  the x₀⁻¹
            := by rw [UdEqual.calc_inv h_x₀_ne0]

private instance rightlimit_patch₆ {x₀ : ℝ}
  : AutoRightLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₊ (·⁻¹) x₀
         =? (lim₊ id x₀)⁻¹
            := RightLimitExpr.Inv
      _  =  (the x₀)⁻¹
            := by rw [RightLimitExpr.Identity]
      _  =  the x₀⁻¹
            := by rw [UdEqual.calc_inv h_x₀_ne0]

private instance funclimit_patch₆' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance leftlimit_patch₆' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance rightlimit_patch₆' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance funclimit_Constant {C x₀ : ℝ}
  : AutoLimit (const C) x₀ C True where
  eq := directly FuncLimitExpr.Constant

private instance funclimit_Constant' {C x₀ : ℝ}
  : AutoLimit (fun _ ↦ C) x₀ C True where
  eq := funclimit_Constant.eq

private instance leftlimit_Constant {C x₀ : ℝ}
  : AutoLeftLimit (const C) x₀ C True where
  eq := directly LeftLimitExpr.Constant

private instance leftlimit_Constant' {C x₀ : ℝ}
  : AutoLeftLimit (fun _ ↦ C) x₀ C True where
  eq := leftlimit_Constant.eq

private instance rightlimit_Constant {C x₀ : ℝ}
  : AutoRightLimit (const C) x₀ C True where
  eq := directly RightLimitExpr.Constant

private instance rightlimit_Constant' {C x₀ : ℝ}
  : AutoRightLimit (fun _ ↦ C) x₀ C True where
  eq := rightlimit_Constant.eq

private instance funclimit_Identity {x₀ : ℝ}
  : AutoLimit id x₀ x₀ True where
  eq := directly FuncLimitExpr.Identity

private instance funclimit_Identity' {x₀ : ℝ}
  : AutoLimit (·) x₀ x₀ True where
  eq := funclimit_Identity.eq

private instance leftlimit_Identity {x₀ : ℝ}
  : AutoLeftLimit id x₀ x₀ True where
  eq := directly LeftLimitExpr.Identity

private instance leftlimit_Identity' {x₀ : ℝ}
  : AutoLeftLimit (·) x₀ x₀ True where
  eq := leftlimit_Identity.eq

private instance rightlimit_Identity {x₀ : ℝ}
  : AutoRightLimit id x₀ x₀ True where
  eq := directly RightLimitExpr.Identity

private instance rightlimit_Identity' {x₀ : ℝ}
  : AutoRightLimit (·) x₀ x₀ True where
  eq := rightlimit_Identity.eq

private instance funclimit_SMul {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim (k • f) x₀
         =? the k * lim f x₀
            := FuncLimitExpr.SMul
      _  =  the k * the L₁
            := by rw [AutoLimit.eq h_cond]
      _  =  the (k * L₁)
            := rfl

private instance leftlimit_SMul {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim₋ (k • f) x₀
         =? the k * lim₋ f x₀
            := LeftLimitExpr.SMul
      _  =  the k * the L₁
            := by rw [AutoLeftLimit.eq h_cond]
      _  =  the (k * L₁)
            := rfl

private instance rightlimit_SMul {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim₊ (k • f) x₀
         =? the k * lim₊ f x₀
            := RightLimitExpr.SMul
      _  =  the k * the L₁
            := by rw [AutoRightLimit.eq h_cond]
      _  =  the (k * L₁)
            := rfl

private instance funclimit_Neg {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim (-f) x₀
         =? - lim f x₀
            := FuncLimitExpr.Neg
      _  =  - the L₁
            := by rw [AutoLimit.eq h_cond]
      _  =  the (-L₁)
            := rfl

private instance funclimit_Neg' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := funclimit_Neg.eq

private instance leftlimit_Neg {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim₋ (-f) x₀
         =? - lim₋ f x₀
            := LeftLimitExpr.Neg
      _  =  - the L₁
            := by rw [AutoLeftLimit.eq h_cond]
      _  =  the (-L₁)
            := rfl

private instance leftlimit_Neg' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := leftlimit_Neg.eq

private instance rightlimit_Neg {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim₊ (-f) x₀
         =? - lim₊ f x₀
            := RightLimitExpr.Neg
      _  =  - the L₁
            := by rw [AutoRightLimit.eq h_cond]
      _  =  the (-L₁)
            := rfl

private instance rightlimit_Neg' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := rightlimit_Neg.eq

private instance funclimit_Inv {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim f⁻¹ x₀
         =? (lim f x₀)⁻¹
            := FuncLimitExpr.Inv
      _  =  (the L₁)⁻¹
            := by rw [AutoLimit.eq h_cond]
      _  =  the L₁⁻¹
            := by rw [UdEqual.calc_inv h_L_ne0]

private instance funclimit_Inv' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := funclimit_Inv.eq

private instance leftlimit_Inv {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim₋ f⁻¹ x₀
         =? (lim₋ f x₀)⁻¹
            := LeftLimitExpr.Inv
      _  =  (the L₁)⁻¹
            := by rw [AutoLeftLimit.eq h_cond]
      _  =  the L₁⁻¹
            := by rw [UdEqual.calc_inv h_L_ne0]

private instance leftlimit_Inv' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := leftlimit_Inv.eq

private instance rightlimit_Inv {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim₊ f⁻¹ x₀
         =? (lim₊ f x₀)⁻¹
            := RightLimitExpr.Inv
      _  =  (the L₁)⁻¹
            := by rw [AutoRightLimit.eq h_cond]
      _  =  the L₁⁻¹
            := by rw [UdEqual.calc_inv h_L_ne0]

private instance rightlimit_Inv' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := rightlimit_Inv.eq

private instance funclimit_Add {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f + g) x₀
         =? lim f x₀ + lim g x₀
            := FuncLimitExpr.Add
      _  =  the L₁ + the L₂
            := by rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
      _  =  the (L₁ + L₂)
            := rfl

private instance funclimit_Add' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := funclimit_Add.eq

private instance leftlimit_Add {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f + g) x₀
         =? lim₋ f x₀ + lim₋ g x₀
            := LeftLimitExpr.Add
      _  =  the L₁ + the L₂
            := by rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
      _  =  the (L₁ + L₂)
            := rfl

private instance leftlimit_Add' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Add.eq

private instance rightlimit_Add {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f + g) x₀
         =? lim₊ f x₀ + lim₊ g x₀
            := RightLimitExpr.Add
      _  =  the L₁ + the L₂
            := by rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
      _  =  the (L₁ + L₂)
            := rfl

private instance rightlimit_Add' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Add.eq

private instance funclimit_Sub {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f - g) x₀
         =? lim f x₀ - lim g x₀
            := FuncLimitExpr.Sub
      _  =  the L₁ - the L₂
            := by rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
      _  =  the (L₁ - L₂)
            := rfl

private instance funclimit_Sub' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := funclimit_Sub.eq

private instance leftlimit_Sub {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f - g) x₀
         =? lim₋ f x₀ - lim₋ g x₀
            := LeftLimitExpr.Sub
      _  =  the L₁ - the L₂
            := by rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
      _  =  the (L₁ - L₂)
            := rfl

private instance leftlimit_Sub' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Sub.eq

private instance rightlimit_Sub {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f - g) x₀
         =? lim₊ f x₀ - lim₊ g x₀
            := RightLimitExpr.Sub
      _  =  the L₁ - the L₂
            := by rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
      _  =  the (L₁ - L₂)
            := rfl

private instance rightlimit_Sub' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Sub.eq

private instance funclimit_Mul {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f * g) x₀
         =? lim f x₀ * lim g x₀
            := FuncLimitExpr.Mul
      _  =  the L₁ * the L₂
            := by rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
      _  =  the (L₁ * L₂)
            := rfl

private instance funclimit_Mul' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := funclimit_Mul.eq

private instance leftlimit_Mul {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f * g) x₀
         =? lim₋ f x₀ * lim₋ g x₀
            := LeftLimitExpr.Mul
      _  =  the L₁ * the L₂
            := by rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
      _  =  the (L₁ * L₂)
            := rfl

private instance leftlimit_Mul' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Mul.eq

private instance rightlimit_Mul {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f * g) x₀
         =? lim₊ f x₀ * lim₊ g x₀
            := RightLimitExpr.Mul
      _  =  the L₁ * the L₂
            := by rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
      _  =  the (L₁ * L₂)
            := rfl

private instance rightlimit_Mul' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Mul.eq

private instance funclimit_Div {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim (f / g) x₀
         =? lim f x₀ / lim g x₀
            := FuncLimitExpr.Div
      _  =  the L₁ / the L₂
            := by rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
      _  =  the (L₁ / L₂)
            := by rw [UdEqual.calc_div h_L₂_ne0]

private instance funclimit_Div' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := funclimit_Div.eq

private instance leftlimit_Div {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim₋ (f / g) x₀
         =? lim₋ f x₀ / lim₋ g x₀
            := LeftLimitExpr.Div
      _  =  the L₁ / the L₂
            := by rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
      _  =  the (L₁ / L₂)
            := by rw [UdEqual.calc_div h_L₂_ne0]

private instance leftlimit_Div' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := leftlimit_Div.eq

private instance rightlimit_Div {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim₊ (f / g) x₀
         =? lim₊ f x₀ / lim₊ g x₀
            := RightLimitExpr.Div
      _  =  the L₁ / the L₂
            := by rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
      _  =  the (L₁ / L₂)
            := by rw [UdEqual.calc_div h_L₂_ne0]

private instance rightlimit_Div' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := rightlimit_Div.eq

private instance funclimit_Abs {x₀ : ℝ}
  : AutoLimit abs x₀ |x₀| True where
  eq := directly FuncLimitExpr.Abs

private instance leftlimit_Abs {x₀ : ℝ}
  : AutoLeftLimit abs x₀ |x₀| True where
  eq := directly LeftLimitExpr.Abs

private instance rightlimit_Abs {x₀ : ℝ}
  : AutoRightLimit abs x₀ |x₀| True where
  eq := directly RightLimitExpr.Abs

private instance funclimit_Sqrt {x₀ : ℝ}
  : AutoLimit sqrt x₀ √x₀ (x₀ > 0) where
  eq := FuncLimitExpr.Sqrt

private instance leftlimit_Sqrt {x₀ : ℝ}
  : AutoLeftLimit sqrt x₀ √x₀ (x₀ > 0) where
  eq := LeftLimitExpr.Sqrt

private instance rightlimit_Sqrt {x₀ : ℝ}
  : AutoRightLimit sqrt x₀ √x₀ (x₀ ≥ 0) where
  eq := RightLimitExpr.Sqrt

private instance funclimit_Power {a x₀ : ℝ}
  : AutoLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  eq := FuncLimitExpr.Power

private instance leftlimit_Power {a x₀ : ℝ}
  : AutoLeftLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  eq := LeftLimitExpr.Power

private instance rightlimit_Power {a x₀ : ℝ}
  : AutoRightLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0 ∨ a > 0 ∧ x₀ = 0) where
  eq := RightLimitExpr.Power

private instance funclimit_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := FuncLimitExpr.Power_ℤ

private instance leftlimit_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := LeftLimitExpr.Power_ℤ

private instance rightlimit_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := RightLimitExpr.Power_ℤ

private instance funclimit_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply FuncLimitExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance leftlimit_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply LeftLimitExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance rightlimit_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply RightLimitExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance funclimit_Exp {x₀ : ℝ}
  : AutoLimit exp x₀ (exp x₀) True where
  eq := directly FuncLimitExpr.Exp

private instance leftlimit_Exp {x₀ : ℝ}
  : AutoLeftLimit exp x₀ (exp x₀) True where
  eq := directly LeftLimitExpr.Exp

private instance rightlimit_Exp {x₀ : ℝ}
  : AutoRightLimit exp x₀ (exp x₀) True where
  eq := directly RightLimitExpr.Exp

private instance funclimit_Expow {a x₀ : ℝ}
  : AutoLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := FuncLimitExpr.Expow

private instance leftlimit_Expow {a x₀ : ℝ}
  : AutoLeftLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := LeftLimitExpr.Expow

private instance rightlimit_Expow {a x₀ : ℝ}
  : AutoRightLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := RightLimitExpr.Expow

private instance funclimit_Ln {x₀ : ℝ}
  : AutoLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := FuncLimitExpr.Ln

private instance leftlimit_Ln {x₀ : ℝ}
  : AutoLeftLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := LeftLimitExpr.Ln

private instance rightlimit_Ln {x₀ : ℝ}
  : AutoRightLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := RightLimitExpr.Ln

private instance funclimit_Log {a x₀ : ℝ}
  : AutoLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := FuncLimitExpr.Log

private instance leftlimit_Log {a x₀ : ℝ}
  : AutoLeftLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := LeftLimitExpr.Log

private instance rightlimit_Log {a x₀ : ℝ}
  : AutoRightLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := RightLimitExpr.Log

private instance funclimit_Sin {x₀ : ℝ}
  : AutoLimit sin x₀ (sin x₀) True where
  eq := directly FuncLimitExpr.Sin

private instance leftlimit_Sin {x₀ : ℝ}
  : AutoLeftLimit sin x₀ (sin x₀) True where
  eq := directly LeftLimitExpr.Sin

private instance rightlimit_Sin {x₀ : ℝ}
  : AutoRightLimit sin x₀ (sin x₀) True where
  eq := directly RightLimitExpr.Sin

private instance funclimit_Cos {x₀ : ℝ}
  : AutoLimit cos x₀ (cos x₀) True where
  eq := directly FuncLimitExpr.Cos

private instance leftlimit_Cos {x₀ : ℝ}
  : AutoLeftLimit cos x₀ (cos x₀) True where
  eq := directly LeftLimitExpr.Cos

private instance rightlimit_Cos {x₀ : ℝ}
  : AutoRightLimit cos x₀ (cos x₀) True where
  eq := directly RightLimitExpr.Cos

private instance funclimit_Tan {x₀ : ℝ}
  : AutoLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := FuncLimitExpr.Tan

private instance leftlimit_Tan {x₀ : ℝ}
  : AutoLeftLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := LeftLimitExpr.Tan

private instance rightlimit_Tan {x₀ : ℝ}
  : AutoRightLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := RightLimitExpr.Tan

private instance funclimit_Cot {x₀ : ℝ}
  : AutoLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := FuncLimitExpr.Cot

private instance leftlimit_Cot {x₀ : ℝ}
  : AutoLeftLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := LeftLimitExpr.Cot

private instance rightlimit_Cot {x₀ : ℝ}
  : AutoRightLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := RightLimitExpr.Cot

private instance funclimit_Sec {x₀ : ℝ}
  : AutoLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := FuncLimitExpr.Sec

private instance leftlimit_Sec {x₀ : ℝ}
  : AutoLeftLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := LeftLimitExpr.Sec

private instance rightlimit_Sec {x₀ : ℝ}
  : AutoRightLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := RightLimitExpr.Sec

private instance funclimit_Csc {x₀ : ℝ}
  : AutoLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := FuncLimitExpr.Csc

private instance leftlimit_Csc {x₀ : ℝ}
  : AutoLeftLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := LeftLimitExpr.Csc

private instance rightlimit_Csc {x₀ : ℝ}
  : AutoRightLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := RightLimitExpr.Csc

private instance funclimit_Sinh {x₀ : ℝ}
  : AutoLimit sinh x₀ (sinh x₀) True where
  eq := directly FuncLimitExpr.Sinh

private instance leftlimit_Sinh {x₀ : ℝ}
  : AutoLeftLimit sinh x₀ (sinh x₀) True where
  eq := directly LeftLimitExpr.Sinh

private instance rightlimit_Sinh {x₀ : ℝ}
  : AutoRightLimit sinh x₀ (sinh x₀) True where
  eq := directly RightLimitExpr.Sinh

private instance funclimit_Cosh {x₀ : ℝ}
  : AutoLimit cosh x₀ (cosh x₀) True where
  eq := directly FuncLimitExpr.Cosh

private instance leftlimit_Cosh {x₀ : ℝ}
  : AutoLeftLimit cosh x₀ (cosh x₀) True where
  eq := directly LeftLimitExpr.Cosh

private instance rightlimit_Cosh {x₀ : ℝ}
  : AutoRightLimit cosh x₀ (cosh x₀) True where
  eq := directly RightLimitExpr.Cosh

private instance funclimit_Tanh {x₀ : ℝ}
  : AutoLimit tanh x₀ (tanh x₀) True where
  eq := directly FuncLimitExpr.Tanh

private instance leftlimit_Tanh {x₀ : ℝ}
  : AutoLeftLimit tanh x₀ (tanh x₀) True where
  eq := directly LeftLimitExpr.Tanh

private instance rightlimit_Tanh {x₀ : ℝ}
  : AutoRightLimit tanh x₀ (tanh x₀) True where
  eq := directly RightLimitExpr.Tanh

private instance funclimit_Coth {x₀ : ℝ}
  : AutoLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := FuncLimitExpr.Coth

private instance leftlimit_Coth {x₀ : ℝ}
  : AutoLeftLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := LeftLimitExpr.Coth

private instance rightlimit_Coth {x₀ : ℝ}
  : AutoRightLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := RightLimitExpr.Coth

private instance funclimit_Sech {x₀ : ℝ}
  : AutoLimit sech x₀ (sech x₀) True where
  eq := directly FuncLimitExpr.Sech

private instance leftlimit_Sech {x₀ : ℝ}
  : AutoLeftLimit sech x₀ (sech x₀) True where
  eq := directly LeftLimitExpr.Sech

private instance rightlimit_Sech {x₀ : ℝ}
  : AutoRightLimit sech x₀ (sech x₀) True where
  eq := directly RightLimitExpr.Sech

private instance funclimit_Csch {x₀ : ℝ}
  : AutoLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := FuncLimitExpr.Csch

private instance leftlimit_Csch {x₀ : ℝ}
  : AutoLeftLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := LeftLimitExpr.Csch

private instance rightlimit_Csch {x₀ : ℝ}
  : AutoRightLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := RightLimitExpr.Csch

private instance funclimit_Arcsin {x₀ : ℝ}
  : AutoLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := FuncLimitExpr.Arcsin

private instance leftlimit_Arcsin {x₀ : ℝ}
  : AutoLeftLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ ≤ 1) where
  eq := LeftLimitExpr.Arcsin

private instance rightlimit_Arcsin {x₀ : ℝ}
  : AutoRightLimit arcsin x₀ (arcsin x₀) (x₀ ≥ -1 ∧ x₀ < 1) where
  eq := RightLimitExpr.Arcsin

private instance funclimit_Arccos {x₀ : ℝ}
  : AutoLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := FuncLimitExpr.Arccos

private instance leftlimit_Arccos {x₀ : ℝ}
  : AutoLeftLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ ≤ 1) where
  eq := LeftLimitExpr.Arccos

private instance rightlimit_Arccos {x₀ : ℝ}
  : AutoRightLimit arccos x₀ (arccos x₀) (x₀ ≥ -1 ∧ x₀ < 1) where
  eq := RightLimitExpr.Arccos

private instance funclimit_Arctan {x₀ : ℝ}
  : AutoLimit arctan x₀ (arctan x₀) True where
  eq := directly FuncLimitExpr.Arctan

private instance leftlimit_Arctan {x₀ : ℝ}
  : AutoLeftLimit arctan x₀ (arctan x₀) True where
  eq := directly LeftLimitExpr.Arctan

private instance rightlimit_Arctan {x₀ : ℝ}
  : AutoRightLimit arctan x₀ (arctan x₀) True where
  eq := directly RightLimitExpr.Arctan

private instance funclimit_Arccot {x₀ : ℝ}
  : AutoLimit arccot x₀ (arccot x₀) True where
  eq := directly FuncLimitExpr.Arccot

private instance leftlimit_Arccot {x₀ : ℝ}
  : AutoLeftLimit arccot x₀ (arccot x₀) True where
  eq := directly LeftLimitExpr.Arccot

private instance rightlimit_Arccot {x₀ : ℝ}
  : AutoRightLimit arccot x₀ (arccot x₀) True where
  eq := directly RightLimitExpr.Arccot

private instance funclimit_Arcsec {x₀ : ℝ}
  : AutoLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := FuncLimitExpr.Arcsec

private instance leftlimit_Arcsec {x₀ : ℝ}
  : AutoLeftLimit arcsec x₀ (arcsec x₀) (x₀ ≤ -1 ∨ x₀ > 1) where
  eq := LeftLimitExpr.Arcsec

private instance rightlimit_Arcsec {x₀ : ℝ}
  : AutoRightLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ ≥ 1) where
  eq := RightLimitExpr.Arcsec

private instance funclimit_Arccsc {x₀ : ℝ}
  : AutoLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := FuncLimitExpr.Arccsc

private instance leftlimit_Arccsc {x₀ : ℝ}
  : AutoLeftLimit arccsc x₀ (arccsc x₀) (x₀ ≤ -1 ∨ x₀ > 1) where
  eq := LeftLimitExpr.Arccsc

private instance rightlimit_Arccsc {x₀ : ℝ}
  : AutoRightLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ ≥ 1) where
  eq := RightLimitExpr.Arccsc

private instance funclimit_compAbs {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance funclimit_compAbs' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := funclimit_compAbs.eq

private instance leftlimit_compAbs {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance leftlimit_compAbs' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := leftlimit_compAbs.eq

private instance rightlimit_compAbs {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance rightlimit_compAbs' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := rightlimit_compAbs.eq

private instance funclimit_compSqrt {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance funclimit_compSqrt' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := funclimit_compSqrt.eq

private instance leftlimit_compSqrt {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance leftlimit_compSqrt' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := leftlimit_compSqrt.eq

private instance rightlimit_compSqrt {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance rightlimit_compSqrt' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := rightlimit_compSqrt.eq

private instance funclimit_compPower {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance funclimit_compPower' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance funclimit_compPower'' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance leftlimit_compPower {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance leftlimit_compPower' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := leftlimit_compPower.eq

private instance leftlimit_compPower'' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := leftlimit_compPower.eq

private instance rightlimit_compPower {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance rightlimit_compPower' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := rightlimit_compPower.eq

private instance rightlimit_compPower'' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := rightlimit_compPower.eq

private instance funclimit_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance funclimit_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance funclimit_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance leftlimit_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance leftlimit_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℤ.eq

private instance leftlimit_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℤ.eq

private instance rightlimit_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance rightlimit_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℤ.eq

private instance rightlimit_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℤ.eq

private instance funclimit_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp Nat.cast_pos.mpr id

private instance funclimit_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance funclimit_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance leftlimit_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp Nat.cast_pos.mpr id

private instance leftlimit_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℕ.eq

private instance leftlimit_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℕ.eq

private instance rightlimit_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp Nat.cast_pos.mpr id

private instance rightlimit_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℕ.eq

private instance rightlimit_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℕ.eq

private instance funclimit_compExp {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance funclimit_compExp' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := funclimit_compExp.eq

private instance leftlimit_compExp {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance leftlimit_compExp' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := leftlimit_compExp.eq

private instance rightlimit_compExp {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance rightlimit_compExp' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := rightlimit_compExp.eq

private instance funclimit_compExpow {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance funclimit_compExpow' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := funclimit_compExpow.eq

private instance leftlimit_compExpow {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance leftlimit_compExpow' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := leftlimit_compExpow.eq

private instance rightlimit_compExpow {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance rightlimit_compExpow' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := rightlimit_compExpow.eq

private instance funclimit_compLn {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance funclimit_compLn' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := funclimit_compLn.eq

private instance leftlimit_compLn {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance leftlimit_compLn' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := leftlimit_compLn.eq

private instance rightlimit_compLn {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance rightlimit_compLn' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := rightlimit_compLn.eq

private instance funclimit_compLog {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance funclimit_compLog' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := funclimit_compLog.eq

private instance leftlimit_compLog {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance leftlimit_compLog' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := leftlimit_compLog.eq

private instance rightlimit_compLog {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance rightlimit_compLog' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := rightlimit_compLog.eq

private instance funclimit_compSin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance funclimit_compSin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := funclimit_compSin.eq

private instance leftlimit_compSin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance leftlimit_compSin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := leftlimit_compSin.eq

private instance rightlimit_compSin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance rightlimit_compSin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := rightlimit_compSin.eq

private instance funclimit_compCos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance funclimit_compCos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := funclimit_compCos.eq

private instance leftlimit_compCos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance leftlimit_compCos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := leftlimit_compCos.eq

private instance rightlimit_compCos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance rightlimit_compCos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := rightlimit_compCos.eq

private instance funclimit_compTan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance funclimit_compTan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compTan.eq

private instance leftlimit_compTan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance leftlimit_compTan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := leftlimit_compTan.eq

private instance rightlimit_compTan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance rightlimit_compTan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := rightlimit_compTan.eq

private instance funclimit_compCot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance funclimit_compCot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCot.eq

private instance leftlimit_compCot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance leftlimit_compCot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := leftlimit_compCot.eq

private instance rightlimit_compCot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance rightlimit_compCot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := rightlimit_compCot.eq

private instance funclimit_compSec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance funclimit_compSec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compSec.eq

private instance leftlimit_compSec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance leftlimit_compSec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := leftlimit_compSec.eq

private instance rightlimit_compSec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance rightlimit_compSec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := rightlimit_compSec.eq

private instance funclimit_compCsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance funclimit_compCsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCsc.eq

private instance leftlimit_compCsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance leftlimit_compCsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := leftlimit_compCsc.eq

private instance rightlimit_compCsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance rightlimit_compCsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := rightlimit_compCsc.eq

private instance funclimit_compSinh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance funclimit_compSinh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := funclimit_compSinh.eq

private instance leftlimit_compSinh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance leftlimit_compSinh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := leftlimit_compSinh.eq

private instance rightlimit_compSinh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance rightlimit_compSinh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := rightlimit_compSinh.eq

private instance funclimit_compCosh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance funclimit_compCosh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := funclimit_compCosh.eq

private instance leftlimit_compCosh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance leftlimit_compCosh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := leftlimit_compCosh.eq

private instance rightlimit_compCosh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance rightlimit_compCosh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := rightlimit_compCosh.eq

private instance funclimit_compTanh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance funclimit_compTanh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := funclimit_compTanh.eq

private instance leftlimit_compTanh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance leftlimit_compTanh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := leftlimit_compTanh.eq

private instance rightlimit_compTanh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance rightlimit_compTanh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := rightlimit_compTanh.eq

private instance funclimit_compCoth {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance funclimit_compCoth' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCoth.eq

private instance leftlimit_compCoth {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance leftlimit_compCoth' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := leftlimit_compCoth.eq

private instance rightlimit_compCoth {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance rightlimit_compCoth' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := rightlimit_compCoth.eq

private instance funclimit_compSech {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance funclimit_compSech' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := funclimit_compSech.eq

private instance leftlimit_compSech {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance leftlimit_compSech' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := leftlimit_compSech.eq

private instance rightlimit_compSech {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance rightlimit_compSech' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := rightlimit_compSech.eq

private instance funclimit_compCsch {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance funclimit_compCsch' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCsch.eq

private instance leftlimit_compCsch {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance leftlimit_compCsch' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := leftlimit_compCsch.eq

private instance rightlimit_compCsch {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance rightlimit_compCsch' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := rightlimit_compCsch.eq

private instance funclimit_compArcsin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance funclimit_compArcsin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArcsin.eq

private instance leftlimit_compArcsin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance leftlimit_compArcsin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := leftlimit_compArcsin.eq

private instance rightlimit_compArcsin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance rightlimit_compArcsin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := rightlimit_compArcsin.eq

private instance funclimit_compArccos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance funclimit_compArccos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArccos.eq

private instance leftlimit_compArccos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance leftlimit_compArccos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := leftlimit_compArccos.eq

private instance rightlimit_compArccos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance rightlimit_compArccos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := rightlimit_compArccos.eq

private instance funclimit_compArctan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance funclimit_compArctan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := funclimit_compArctan.eq

private instance leftlimit_compArctan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance leftlimit_compArctan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := leftlimit_compArctan.eq

private instance rightlimit_compArctan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance rightlimit_compArctan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := rightlimit_compArctan.eq

private instance funclimit_compArccot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance funclimit_compArccot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := funclimit_compArccot.eq

private instance leftlimit_compArccot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance leftlimit_compArccot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := leftlimit_compArccot.eq

private instance rightlimit_compArccot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance rightlimit_compArccot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := rightlimit_compArccot.eq

private instance funclimit_compArcsec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance funclimit_compArcsec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArcsec.eq

private instance leftlimit_compArcsec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance leftlimit_compArcsec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := leftlimit_compArcsec.eq

private instance rightlimit_compArcsec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance rightlimit_compArcsec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := rightlimit_compArcsec.eq

private instance funclimit_compArccsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance funclimit_compArccsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArccsc.eq

private instance leftlimit_compArccsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply LeftLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance leftlimit_compArccsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := leftlimit_compArccsc.eq

private instance rightlimit_compArccsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply RightLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance rightlimit_compArccsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := rightlimit_compArccsc.eq

lemma autoFuncLimit {f : ℝ → ℝ} {x₀ : ℝ} {L₁ : ℝ} {cond : Prop}
    [AutoLimit f x₀ L₁ cond] (h_cond : cond)
  : lim f x₀ = the L₁
:= AutoLimit.eq h_cond

lemma autoLeftLimit {f : ℝ → ℝ} {x₀ : ℝ} {L₁ : ℝ} {cond : Prop}
    [AutoLeftLimit f x₀ L₁ cond] (h_cond : cond)
  : lim₋ f x₀ = the L₁
:= AutoLeftLimit.eq h_cond

lemma autoRightLimit {f : ℝ → ℝ} {x₀ : ℝ} {L₁ : ℝ} {cond : Prop}
    [AutoRightLimit f x₀ L₁ cond] (h_cond : cond)
  : lim₊ f x₀ = the L₁
:= AutoRightLimit.eq h_cond


/-! # Tactics -/

/-- ## Limit Calculator (Based on Continuity)

    __Usage__ `lim_calc`

    - Only used for limit expression, including
      - `SeqLimitExpr` (not yet)
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`
      - `NegInftyLimitExpr` (not yet)
      - `PosInftyLimitExpr` (not yet)
      - `InftyLimitExpr` (not yet)

    - `lim_calc` calculates limit expressions as much as possible in standard
      forms, and then uses built-in tactic `auto_eq` to solve the remaining goal.

    - `lim_calc` requires some side-conditions to exist in the context, which are
      the sum of the corresponding conditions for these different functions:

      - `f x ≠ 0` for `lim f⁻¹ x` and other two
      - `g x ≠ 0` for `lim (f / g) x` and other two
      - `x > 0` for `lim sqrt x` and `lim₋ sqrt x`
      - `x ≥ 0` for `lim₊ sqrt x`
      - `x > 0` for `lim (pow a) x` and `lim₋ (pow a) x`
      - `x > 0 ∨ a > 0 ∧ x = 0` for `lim₊ (pow a) x`
      - `n > 0 ∨ x ≠ 0` for `lim (npow n) x` and other two
      - `a > 0` for `lim (a ^ ·) x` and other two
      - `x > 0` for `lim ln x` and other two
      - `x > 0 ∧ a > 0 ∧ a ≠ 1` for `lim (log a) x` and other two
      - `cos x ≠ 0` for `lim tan x` and other two
      - `sin x ≠ 0` for `lim cot x` and other two
      - `cos x ≠ 0` for `lim sec x` and other two
      - `sin x ≠ 0` for `lim csc x` and other two
      - `x ≠ 0` for `lim coth x` and other two
      - `x ≠ 0` for `lim csch x` and other two
      - `x > -1 ∧ x < 1` for `lim arcsin x`
      - `x > -1 ∧ x ≤ 1` for `lim₋ arcsin x`
      - `x ≥ -1 ∧ x < 1` for `lim₊ arcsin x`
      - `x > -1 ∧ x < 1` for `lim arccos x`
      - `x > -1 ∧ x ≤ 1` for `lim₋ arccos x`
      - `x ≥ -1 ∧ x < 1` for `lim₊ arccos x`
      - `x < -1 ∨ x > 1` for `lim arcsec x`
      - `x ≤ -1 ∨ x > 1` for `lim₋ arcsec x`
      - `x < -1 ∨ x ≥ 1` for `lim₊ arcsec x`
      - `x < -1 ∨ x > 1` for `lim arccsc x`
      - `x ≤ -1 ∨ x > 1` for `lim₋ arccsc x`
      - `x < -1 ∨ x ≥ 1` for `lim₊ arccsc x`

      For composite functions, the `x` above represents the inner function.

    - The side-conditions should preferably be provided as they are. If not, the
      following tactics will be used to complete the remaining conditions:
      - `trivial`
      - `tauto`
      - `positivity`
      - `nlinarith`
      - `norm_num`

    __Examples__
    ```lean
    variable {x : ℝ}
    example
      : lim (fun t ↦ ln t / t) 1 = the 0
    := by lim_calc
    example
      : lim (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x))
    := by lim_calc
    example (_ : x ≠ 0)
      : lim (fun t ↦ t⁻¹ + t) x = the ((x ^ 2 + 1) / x)
    := by lim_calc
    ```
-/
macro "lim_calc" : tactic => `(tactic| (
  intros
  repeat rw [autoFuncLimit]
  repeat rw [autoLeftLimit]
  repeat rw [autoRightLimit]
  all_goals try _auto_side_condition
  try focus auto_eq
  try focus lim_congr_by field within 1
))

variable {x : ℝ}
example
  : lim (fun t ↦ ln t / t) 1 = the 0
:= by lim_calc
example
  : lim (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x))
:= by lim_calc
example (_ : x ≠ 0)
  : lim (fun t ↦ t⁻¹ + t) x = the ((x ^ 2 + 1) / x)
:= by lim_calc
