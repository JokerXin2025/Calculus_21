/-
    «Calculus_21».Limit.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Sequence.Concepts
import «Calculus_21».Function.Concepts
set_option linter.style.header false


/-! # Definitions of Limit -/

/-- Sequence Limit -/
def SeqLimit (A : Sequence) (L : ℝ) : Prop :=
  A.final = none
  ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, A.map n ∈ Nbho L ε

abbrev SeqConvergesAt (A : Sequence) : Prop :=
  ∃ L : ℝ, SeqLimit A L

/-- Function Limit -/
def FuncLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, F.map x ∈ Nbho L ε)

abbrev FuncConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, FuncLimit F x₀ L

/-- (Function's) Left Limit -/
def LeftLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x ∈ Nbho L ε)

abbrev LeftConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftLimit F x₀ L

/-- (Function's) Right Limit -/
def RightLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x ∈ Nbho L ε)

abbrev RightConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightLimit F x₀ L

/-- (Function's) Limit at Negative Infinity -/
def NegInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)

abbrev ConvergesAtNegInfty (F : Function) : Prop :=
  ∃ L : ℝ, NegInftyLimit F L

/-- (Function's) Limit at Positive Infinity -/
def PosInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

abbrev ConvergesAtPosInfty (F : Function) : Prop :=
  ∃ L : ℝ, PosInftyLimit F L

/-- (Function's) Limit at Infinity -/
def InftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain ∧ Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      (∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)
      ∧ (∀ x ∈ Ioi M, F.map x ∈ Nbho L ε))

abbrev ConvergesAtInfty (F : Function) : Prop :=
  ∃ L : ℝ, InftyLimit F L


/-! # Properties of Limit -/

/-- Uniqueness of Sequence Limit -/
theorem SeqLimit_Unique {A : Sequence} {L₁ L₂ : ℝ}
    (h₁ : SeqLimit A L₁) (h₂ : SeqLimit A L₂)
  : L₁ = L₂
:= sorry

/-- Boundedness of Convergent Sequence -/
theorem SeqLimit_Bounded {A : Sequence}
    (h_conv : SeqConvergesAt A)
  : SeqBounded A
:= sorry

/-- Uniqueness of Function Limit -/
theorem FuncLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : FuncLimit F x₀ L₁) (h₂ : FuncLimit F x₀ L₂)
  : L₁ = L₂
:= sorry

/-- Local Boundedness of Convergent Function -/
theorem FuncLimit_Bounded {F : Function} {x₀ : ℝ}
    (h_conv : FuncConvergesAt F x₀)
  : FuncLocalBounded F x₀
:= sorry

/-- Uniqueness of Left Limit -/
theorem LeftLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : LeftLimit F x₀ L₁) (h₂ : LeftLimit F x₀ L₂)
  : L₁ = L₂
:= sorry

/-- Uniqueness of Right Limit -/
theorem RightLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : RightLimit F x₀ L₁) (h₂ : RightLimit F x₀ L₂)
  : L₁ = L₂
:= sorry

/-- Uniqueness of Limit at Negative Infinity -/
theorem NegInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : NegInftyLimit F L₁) (h₂ : NegInftyLimit F L₂)
  : L₁ = L₂
:= sorry

/-- Local Boundedness of Function Convergent at Negative Infinity -/
theorem NegInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtNegInfty F)
  : FuncLocalBounded_NegInfty F
:= sorry

/-- Uniqueness of Limit at Positive Infinity -/
theorem PosInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : PosInftyLimit F L₁) (h₂ : PosInftyLimit F L₂)
  : L₁ = L₂
:= sorry

/-- Local Boundedness of Function Convergent at Positive Infinity -/
theorem PosInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtPosInfty F)
  : FuncLocalBounded_PosInfty F
:= sorry

/-- Uniqueness of Limit at Infinity -/
theorem InftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : InftyLimit F L₁) (h₂ : InftyLimit F L₂)
  : L₁ = L₂
:= sorry

/-- Congruence of Sequence Limit -/
lemma SeqLimit.Congr {A B : Sequence} {L : ℝ}
    (h_lim : SeqLimit A L)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimit B L
:= sorry

/-- Congruence of Function Limit -/
lemma FuncLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain
                        ∧ ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= sorry

/-- Congruence of Left Limit -/
lemma LeftLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : LeftLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain
                        ∧ ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= sorry

/-- Congruence of Right Limit -/
lemma RightLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : RightLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain
                        ∧ ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= sorry

/-- Congruence of Limit at Negative Infinity -/
lemma NegInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : NegInftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain
                        ∧ ∀ x ∈ Iio (-M), F.map x = G.map x)
  : NegInftyLimit G L
:= sorry

/-- Congruence of Limit at Positive Infinity -/
lemma PosInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : PosInftyLimit F L)
    (h_congr : ∃ M > 0, Ioi M ⊆ G.domain
                        ∧ ∀ x ∈ Ioi M, F.map x = G.map x)
  : PosInftyLimit G L
:= sorry

/-- Congruence of Limit at Infinity -/
lemma InftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain ∧ Ioi M ⊆ G.domain
                        ∧ (∀ x ∈ Iio (-M), F.map x = G.map x)
                        ∧ (∀ x ∈ Ioi M, F.map x = G.map x))
  : InftyLimit G L
:= sorry

/-- Function Limit → Left Limit -/
theorem FuncLimit_toLeft {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= sorry

/-- Function Limit → Right Limit -/
theorem FuncLimit_toRight {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= sorry

/-- Limit at Infinity → Limit at Negative Infinity -/
theorem InftyLimit_toNeg {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : NegInftyLimit F L
:= sorry

/-- Limit at Infinity → Limit at Positive Infinity -/
theorem InftyLimit_toPos {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : PosInftyLimit F L
:= sorry
