/-
    «Calculus_21».Expr.Tactics
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Tactics
set_option linter.style.header false

open Lean.Elab.Tactic


/-! # Preparations -/

private class AutoExpr (expr : Option ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → expr = the val

instance eval_the {A : ℝ}
  : AutoExpr (the A) A True where
  eq := directly rfl

instance eval_add {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A + B) (a + b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_sub {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A - B) (a - b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_mul {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A * B) (a * b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_div (A B : Option ℝ) (a b : ℝ) (c₁ c₂ : Prop)
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A / B) (a / b) (c₁ ∧ c₂ ∧ b ≠ 0) where
  eq := by
    intro ⟨h_a, h_b, h_ne⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    change (if the b = the 0 then none else _) = _
    have h_cond : the b ≠ the 0 := by
      simp only [ne_eq, Option.some.injEq, h_ne, not_false_eq_true]
    rw [if_neg h_cond]

instance eval_pow₁ {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A ^ B) (a ^ b) (c₁ ∧ c₂ ∧ a > 0) where
  eq := by
    intro ⟨h_a, h_b, h_pos⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    change (if a = 0 ∧ b > 0 then the 0
            else if a > 0 then the (a ^ b)
            else _) = the (a ^ b)
    have h_cond1 : ¬(a = 0 ∧ b > 0) := by
      intro _
      linarith
    rw [if_neg h_cond1, if_pos h_pos]

instance eval_pow₂ {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂]
  : AutoExpr (A ^ B) (a ^ b) (c₁ ∧ c₂ ∧ a = 0 ∧ b > 0) where
  eq := by
    intro ⟨h_a, h_b, h_a_eq_0, h_b_pos⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    change (if a = 0 ∧ b > 0 then the 0
            else _) = the (a ^ b)
    have h_cond : a = 0 ∧ b > 0 := ⟨h_a_eq_0, h_b_pos⟩
    rewrite [if_pos h_cond]
    congr
    rewrite [h_a_eq_0]
    symm
    exact Real.zero_rpow (ne_of_gt h_b_pos)

open Classical in
instance eval_pow₃ {A B : Option ℝ} {a : ℝ} {n : ℤ} {c₁ c₂ : Prop}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B (n : ℝ) c₂]
  : AutoExpr (A ^ B) (a ^ (n : ℝ)) (c₁ ∧ c₂ ∧ a < 0) where
  eq := by
    intro ⟨h_a, h_b, h_a_neg⟩
    rewrite [h₁.eq h_a, h₂.eq h_b]
    change (if a = 0 ∧ (n : ℝ) > 0 then the 0
            else if a > 0 then the (a ^ (n : ℝ))
            else if h : a < 0 ∧ (∃ m : ℤ, (n : ℝ) = m) then
              the (a ^ (choose h.2))
            else none) = the (a ^ (n : ℝ))
    have h_cond1 : ¬(a = 0 ∧ (n : ℝ) > 0) := by
      intro _
      linarith
    have h_cond2 : ¬(a > 0) := by
      linarith
    have h_cond3 : a < 0 ∧ (∃ m : ℤ, (n : ℝ) = m) := ⟨h_a_neg, ⟨n, rfl⟩⟩
    rewrite [if_neg h_cond1, if_neg h_cond2, dif_pos h_cond3]
    congr 1
    have h_m : (n : ℝ) = choose h_cond3.2 := choose_spec h_cond3.2
    have h_n_eq_m : n = choose h_cond3.2 := by
      exact_mod_cast h_m
    rewrite [← h_n_eq_m]
    symm
    exact Real.rpow_intCast a n

instance eval_neg {A : Option ℝ} {a : ℝ} {c : Prop}
    [h : AutoExpr A a c]
  : AutoExpr (-A) (-a) c where
  eq := by
    intro h_a
    rewrite [h.eq h_a]
    rfl

instance eval_inv {A : Option ℝ} {a : ℝ} {c : Prop}
    [h : AutoExpr A a c]
  : AutoExpr (A⁻¹) (a⁻¹) (c ∧ a ≠ 0) where
  eq := by
    intro ⟨h_a, h_ne⟩
    rewrite [h.eq h_a]
    change (if the a = the 0 then none else _) = _
    have h_inv : the a ≠ the 0 := by
      simp only [ne_eq, Option.some.injEq, h_ne, not_false_eq_true]
    rewrite [if_neg h_inv]
    rfl

private lemma autoExpr (expr : Option ℝ) {val : ℝ} {cond : Prop}
    [AutoExpr expr val cond] (h_cond : cond)
  : expr = the val := AutoExpr.eq h_cond

@[aesop unsafe 50% tactic (rule_sets := [AutoEquation])]
def apply_congArg : TacticM Unit := do
  evalTactic (← `(tactic| apply congrArg the))

@[aesop unsafe 20% tactic (rule_sets := [AutoEquation])]
def exe_field : TacticM Unit := do
  evalTactic (← `(tactic| field))


/-! # Tactics -/

/-- ## Expression Simplification
    __Usage__ `expr_simp`
-/
macro "expr_simp" : tactic => `(tactic| (
  intros
  repeat
    rewrite [autoExpr]
    any_goals _auto_side_condition
))

/-- ## Automatic Equation Prover
    __Usage__ `auto_eq`
-/
macro "auto_eq" : tactic => `(tactic|
  aesop (rule_sets := [AutoEquation]) (
    config := { warnOnNonterminal := false }
  )
)
