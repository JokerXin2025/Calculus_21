/-
    «Calculus_21».Prelude
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import Aesop.Frontend.Command
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option linter.style.header false


/-! # Notations -/

export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici
            mem_Ioo mem_Icc mem_Ioc mem_Ico mem_Iio mem_Iic mem_Ioi mem_Ici
            mem_univ subset_univ mem_setOf_eq)
export Finset (range)
export Real (sqrt exp sin cos tan cot sinh cosh tanh arcsin arccos arctan)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n  -- this is only scoped in Mathlib
macro "the" : term => `(some)
macro "directly" item:term : term => `(fun _ ↦ $item)


/-! # Supplementary Definitions -/

noncomputable def e : ℝ := Real.exp 1
noncomputable def π : ℝ := Real.pi

def const (C : ℝ) : ℝ → ℝ := Function.const ℝ C
noncomputable def pow (a : ℝ) : ℝ → ℝ := (Real.rpow · a)
noncomputable abbrev npow (n : ℤ) : ℝ → ℝ := ZPow.zpow n
noncomputable def ln : ℝ → ℝ := Real.log
noncomputable def log : ℝ → ℝ → ℝ := (fun a x ↦ Real.log x / Real.log a)
noncomputable def sec : ℝ → ℝ := (1 / cos ·)
noncomputable def csc : ℝ → ℝ := (1 / sin ·)
noncomputable def coth : ℝ → ℝ := (1 / tanh ·)
noncomputable def sech : ℝ → ℝ := (1 / cosh ·)
noncomputable def csch : ℝ → ℝ := (1 / sinh ·)
noncomputable def arccot : ℝ → ℝ := (π / 2 - arctan ·)
noncomputable def arcsec : ℝ → ℝ := (fun x ↦ arccos (1 / x))
noncomputable def arccsc : ℝ → ℝ := (fun x ↦ arcsin (1 / x))


/-! # Declarations for Aesop -/

declare_aesop_rule_sets [AutoEquation]
