/-
    «Calculus_21».Tactics
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Preparations -/

private lemma recover_e : e = exp 1 := rfl
private lemma recover_π : π = Real.pi := rfl
private lemma recover_const : const = Function.const ℝ := rfl
private lemma recover_pow {a : ℝ} : pow a = (Real.rpow · a) := rfl
private lemma recover_npow : npow = ZPow.zpow := rfl
private lemma recover_ln : ln = Real.log := rfl
private lemma recover_log {a x : ℝ} : log a x = Real.log x / Real.log a := rfl
private lemma recover_sec : sec = (1 / cos ·) := rfl
private lemma recover_csc : csc = (1 / sin ·) := rfl
private lemma recover_coth : coth = (1 / tanh ·) := rfl
private lemma recover_sech : sech = (1 / cosh ·) := rfl
private lemma recover_csch : csch = (1 / sinh ·) := rfl
private lemma recover_arccot : arccot = (π / 2 - arctan ·) := rfl
private lemma recover_arcsec : arcsec = (fun x ↦ arccos (1 / x)) := rfl
private lemma recover_arccsc : arccsc = (fun x ↦ arcsin (1 / x)) := rfl


/-! # Tactics -/

macro "_auto_side_condition" : tactic => `(tactic| (
  repeat any_goals apply And.intro
  all_goals try simp_all only [
    recover_e,
    recover_π,
    recover_const,
    recover_pow,
    recover_npow,
    recover_ln,
    recover_log,
    recover_sec,
    recover_csc,
    recover_coth,
    recover_sech,
    recover_csch,
    recover_arccot,
    recover_arcsec,
    recover_arccsc,
  ]
  all_goals try first
  | trivial; done
  | tauto; done
  | positivity; done
  | nlinarith; done
  | norm_num; done
))
