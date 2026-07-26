/-
    «Calculus_21».Limit.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Limit.Defs
set_option linter.style.header false


/-! # Limit Expression -/

noncomputable section

open Classical in
/-- Sequence Limit Expression -/
def SeqLimitExpr (a : ℕ → ℝ) : Option ℝ :=
  if h : SeqConvergesAt ⟨a, 0, none⟩ then the (choose h)
  else none

open Classical in
/-- Function Limit Expression -/
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : FuncConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Left Limit Expression -/
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : LeftConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Right Limit Expression -/
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : RightConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtNegInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtPosInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtInfty ⟨f, Iii⟩ then the (choose h)
  else none

end

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)
macro "lim₋∞" : term => `(NegInftyLimitExpr)
macro "lim₊∞" : term => `(PosInftyLimitExpr)
macro "lim∞" : term => `(InftyLimitExpr)


/-! # Bridges between Limit & Limit Expression -/

open Classical in
/-- Sequence Limit → Sequence Limit Expression -/
theorem SeqLimit_to_SeqLimitExpr {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : SeqLimit ⟨a, init, none⟩ L)
  : limₙ a = the L
:= sorry

open Classical in
/-- Sequence Limit Expression → Sequence Limit -/
theorem SeqLimitExpr_to_SeqLimit {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : limₙ a = the L)
  : SeqLimit ⟨a, init, none⟩ L
:= sorry

open Classical in
/-- Function Limit → Function Limit Expression -/
theorem FuncLimit_to_FuncLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : FuncLimit ⟨f, I⟩ x₀ L)
  : lim f x₀ = the L
:= sorry

open Classical in
/-- Function Limit Expression → Function Limit -/
theorem FuncLimitExpr_to_FuncLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_lim : lim f x₀ = the L)
  : FuncLimit ⟨f, I⟩ x₀ L
:= sorry

open Classical in
/-- Left Limit → Left Limit Expression -/
theorem LeftLimit_to_LeftLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : LeftLimit ⟨f, I⟩ x₀ L)
  : lim₋ f x₀ = the L
:= sorry

open Classical in
/-- Left Limit Expression → Left Limit -/
theorem LeftLimitExpr_to_LeftLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ I)
    (h_lim : lim₋ f x₀ = the L)
  : LeftLimit ⟨f, I⟩ x₀ L
:= sorry

open Classical in
/-- Right Limit → Right Limit Expression -/
theorem RightLimit_to_RightLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : RightLimit ⟨f, I⟩ x₀ L)
  : lim₊ f x₀ = the L
:= sorry

open Classical in
/-- Right Limit Expression → Right Limit -/
theorem RightLimitExpr_to_RightLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ I)
    (h_lim : lim₊ f x₀ = the L)
  : RightLimit ⟨f, I⟩ x₀ L
:= sorry

open Classical in
/-- Limit at Negative Infinity → Expression of Limit at Negative Infinity -/
theorem NegInftyLimit_to_NegInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : NegInftyLimit ⟨f, I⟩ L)
  : lim₋∞ f = the L
:= sorry

open Classical in
/-- Expression of Limit at Negative Infinity → Limit at Negative Infinity -/
theorem NegInftyLimitExpr_to_NegInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I)
    (h_lim : lim₋∞ f = the L)
  : NegInftyLimit ⟨f, I⟩ L
:= sorry

open Classical in
/-- Limit at Positive Infinity → Expression of Limit at Positive Infinity -/
theorem PosInftyLimit_to_PosInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : PosInftyLimit ⟨f, I⟩ L)
  : lim₊∞ f = the L
:= sorry

open Classical in
/-- Expression of Limit at Positive Infinity → Limit at Positive Infinity -/
theorem PosInftyLimitExpr_to_PosInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Ioi M ⊆ I)
    (h_lim : lim₊∞ f = the L)
  : PosInftyLimit ⟨f, I⟩ L
:= sorry

open Classical in
/-- Limit at Infinity → Expression of Limit at Infinity -/
theorem InftyLimit_to_InftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : InftyLimit ⟨f, I⟩ L)
  : lim∞ f = the L
:= sorry

open Classical in
/-- Expression of Limit at Infinity → Limit at Infinity -/
theorem InftyLimitExpr_to_InftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I ∧ Ioi M ⊆ I)
    (h_lim : lim∞ f = the L)
  : InftyLimit ⟨f, I⟩ L
:= sorry


/-! # Properties of Limit Expression -/

open Classical in
/-- Congruence of Sequence Limit (Expression) -/
lemma SeqLimitExpr.Congr {a b : ℕ → ℝ}
    (h_congr : ∃ N : ℕ, ∀ n > N, a n = b n)
  : limₙ a =? limₙ b
:= sorry

/-- Congruence of Function Limit (Expression) -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry

/-- Congruence of Left Limit (Expression) -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= sorry

/-- Congruence of Right Limit (Expression) -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= sorry

/-- Congruence of Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Iio (-M), f x = g x)
  : lim₋∞ f =? lim₋∞ g
:= sorry

/-- Congruence of Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Ioi M, f x = g x)
  : lim₊∞ f =? lim₊∞ g
:= sorry

/-- Congruence of Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, (∀ x ∈ Iio (-M), f x = g x) ∧ (∀ x ∈ Ioi M, f x = g x))
  : lim∞ f =? lim∞ g
:= sorry

/-- Function Limit → Left Limit (Expression) -/
theorem FuncLimitExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f x₀ =? lim f x₀
:= sorry

/-- Function Limit → Right Limit (Expression) -/
theorem FuncLimitExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f x₀ =? lim f x₀
:= sorry

/-- Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr_toNeg {f : ℝ → ℝ}
  : lim₋∞ f =? lim∞ f
:= sorry

/-- Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr_toPos {f : ℝ → ℝ}
  : lim₊∞ f =? lim∞ f
:= sorry
