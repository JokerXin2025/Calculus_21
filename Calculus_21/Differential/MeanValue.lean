/-
    «Calculus_21».Differential.MeanValue
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
import «Calculus_21».Differential.Defs
set_option linter.style.header false


/-! # Mean Value Theorems -/

/-- Fermat's Lemma -/
theorem Fermat_Lemma {F : Function} {x₀ δ : ℝ}
    (h_dom : Nbho x₀ δ ⊆ F.domain)
    (h_deriv : isDerivableAt F x₀)
    (h_extre : ∀ x ∈ Nbho x₀ δ, F.map x ≤ F.map x₀
               ∨ ∀ x ∈ Nbho x₀ δ, F.map x ≥ F.map x₀)
  : Deriv F x₀ 0
:= sorry

/-- Rolle's Mean Value Theorem -/
theorem Rolle_MeanValue {F : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain)
    (h_eq : F.map a = F.map b)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ 0
:= sorry

/-- Lagrange's Mean Value Theorem -/
theorem Lagrange_MeanValue {F : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ ((F.map b - F.map a) / (b - a))
:= sorry

/-- Cauchy's Mean Value Theorem -/
theorem Cauchy_MeanValue {F G : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_G'_ne_0 : ∀ x ∈ (Diff G).domain, (Diff G).map x ≠ 0)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (F.map b - F.map a) / (G.map b - G.map a) = (Diff F).map ξ / (Diff G).map ξ
:= sorry

/-- Cauchy's Mean Value Theorem (Product Form) -/
theorem Cauchy_MeanValue' {F G : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (Diff F).map ξ * (G.map b - G.map a) = (Diff G).map ξ * (F.map b - F.map a)
:= sorry
