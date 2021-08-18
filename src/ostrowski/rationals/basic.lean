
import data.nat.prime
import data.rat.basic
import data.real.basic
import analysis.special_functions.pow
import data.real.cau_seq
import number_theory.padics.padic_norm

import valuations.basic

import for_mathlib.hom
import for_mathlib.rat

open is_absolute_value
noncomputable theory

def trivial_abs : ℚ → ℝ := λ a,
    if a = 0 then 0
    else 1

instance : is_absolute_value trivial_abs :=
{ abv_nonneg := λ x, by { rw [trivial_abs], dsimp, split_ifs, exact le_refl 0, exact zero_le_one, },
  abv_eq_zero := λ x, by { rw [trivial_abs], dsimp, split, contrapose!, intro, rw if_neg ᾰ, norm_num, intro, rw if_pos ᾰ, },
  abv_add := λ x y, by { rw [trivial_abs], dsimp, split_ifs, any_goals { linarith,}, exfalso, rw [h_1,h_2] at h, simpa using h, },
  abv_mul := λ x y, by { rw [trivial_abs], dsimp, split_ifs, any_goals {norm_num}, finish, finish, finish, finish, } }

def padic_norm_ℝ (p: ℕ) := λ r: ℚ, (padic_norm p r: ℝ)

instance abv_lift (abv: ℚ → ℚ) [habv: is_absolute_value abv]:
  is_absolute_value (λ r: ℚ, (abv r: ℝ)) :=
{ abv_nonneg := by { norm_cast, exact abv_nonneg abv, },
  abv_eq_zero := by { norm_cast, intro x, exact abv_eq_zero abv, },
  abv_add := by { norm_cast, exact abv_add abv, },
  abv_mul := by { norm_cast, exact abv_mul abv, } }

instance padic_is_abv {p: ℕ} [hp: fact (nat.prime p)] : is_absolute_value (padic_norm_ℝ p) :=
  @abv_lift (padic_norm p) (@padic_norm.is_absolute_value p _)

lemma trivial_abs_is_one_iff_nonzero_arg (a: ℚ) : (a ≠ 0) ↔ (trivial_abs a = 1) :=
begin
    split,
    intro h₁,
    unfold trivial_abs,
    by_cases (a = 0),
    exfalso,
    exact h₁ h,
    rw if_neg h,
    contrapose!,
    intro h,
    unfold trivial_abs,
    rw if_pos h,
    finish
end

lemma abs_val_equiv_of_equiv_on_primes (abv abv': ℚ → ℝ)
  [habv: is_absolute_value abv] [habv': is_absolute_value abv']
  (α: ℝ) (α_pos: 0 < α)
  (h: ∀ p: ℕ, prime p → (abv p) ^ α = abv' p): (λ r: ℚ, (abv r) ^ α) = abv' :=
begin
  have: ∀ n: ℕ, (abv n) ^ α = abv' n,
  {
    have inductive_step: ∀ q a: ℕ, nat.prime q → (abv a) ^ α = abv' a
      → (abv (q * a: ℕ)) ^ α = abv' ((q * a): ℕ),
    {
      intros q a q_prime a_norms_eq,
      calc (abv (q * a: ℕ)) ^ α
        = abv (q*a: ℕ) ^ α
          : rfl
        ... = ((abv q) * (abv a)) ^ α
          : by { push_cast, rw abv_mul abv, }
        ... = (abv q) ^ α * (abv a) ^ α
          : by rw real.mul_rpow (abv_nonneg abv q) (abv_nonneg abv a)
        ... = (abv' q) * (abv' a)
          : by rw [h q (nat.prime_iff.1 q_prime), a_norms_eq]
        ... = abv' ((q * a): ℕ)
            : by { rw ← abv_mul abv', norm_cast, }
    },
    apply induction_on_primes,
    {
      norm_cast,
      rw [abv_zero abv, abv_zero abv'],
      rw real.zero_rpow,
      exact (ne_of_lt α_pos).symm,
    },
    {
      norm_cast,
      rw [abv_one abv, abv_one abv'],
      rw real.one_rpow,
    },
    exact inductive_step,
  },
  
  set equiv_hom := hom_of_equiv (hom_of_abv abv) α α_pos
    (by { rw ← show abv = hom_of_abv abv, from rfl, exact abv_nonneg abv, }) with equiv_hom_def,
  set abv'_hom := abv_hom abv' with abv'_hom_def,
  have abv_eq_hom_fn: abv' = abv'_hom := rfl,
  have equiv_abs_eq_hom_fn: (λ r: ℚ, abv r ^ α) = equiv_hom := rfl,
  have same_on_neg_one: equiv_hom (-1) = abv'_hom (-1),
  {
    rw [← abv_eq_hom_fn, ← equiv_abs_eq_hom_fn],
    simp,
    rw [abv_neg abv, abv_neg abv'],
    rw [abv_one abv, abv_one abv'],
    rw real.one_rpow,
  },
  apply ext_hom_pnat equiv_hom abv'_hom same_on_neg_one,

  exact this, 
end
