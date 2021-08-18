/-
  Absolute values on Principal Ideal Domains.
-/

import data.real.cau_seq

import for_mathlib.exp_log

import abvs_equiv

import valuations.basic
import valuations.bounded
import valuations.multiplicative_hom

open is_absolute_value
open_locale classical

def associated_ideal {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1): ideal α :=
{
  carrier := { a: α | abv a < 1 },
  zero_mem' := by simp [abv_zero abv, zero_lt_one],
  add_mem' := by {
    intros a b ha hb,
    have nonarchimedian := (nonarchimedian_iff_integers_bounded abv).1
      ⟨ 1, zero_lt_one, λ n, bounded n ⟩,
    calc abv (a + b) ≤ max (abv a) (abv b) : nonarchimedian a b
      ... < max 1 1 : max_lt_max ha hb
      ... = 1 : by simp,
  },
  smul_mem' := by {
    intros c x hx,
    rw [algebra.id.smul_eq_mul, set.mem_set_of_eq],
    rw abv_mul abv,
    rw ← mul_one (1: ℝ),
    exact mul_lt_mul' (bounded c) hx (abv_nonneg abv x) zero_lt_one,
  },
}

theorem associated_ideal_prime {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1): (associated_ideal abv bounded).is_prime :=
begin
  split,
  {
    rw ideal.ne_top_iff_one,
    by_contra,
    have: abv 1 < 1 := h,
    rw abv_one abv at this,
    linarith only [this],
  },
  {
    intros x y,
    contrapose!,
    intro h,
    have: abv x ≥ 1 ∧ abv y ≥ 1,
    { split; by_contra h'; push_neg at h', exact h.1 h', exact h.2 h', },
    suffices: abv (x * y) ≥ 1,
    { intro h, linarith only [this, show abv (x * y) < 1, from h], },
    rw abv_mul abv,
    rw ← mul_one (1: ℝ),
    rw ge_iff_le,
    exact mul_le_mul this.1 this.2 zero_le_one (abv_nonneg abv x),
  },
end

theorem absolute_value_on_primes {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1)
    (nontrivial: ∃ a: α, a ≠ 0 ∧ abv a ≠ 1):
      ∃ c, 0 < c ∧ c < 1 ∧
      ∃ p: α, prime p ∧ ∀ q: α, prime q → abv q = if associated q p then c else 1 :=
begin
  set I := associated_ideal abv bounded,
  
  have ideal_prime: I.is_prime,
  from associated_ideal_prime abv bounded,

  obtain ⟨ p, p_prime, abvp_lt_one, p_prop ⟩: ∃ p: α, prime p ∧ abv p < 1 ∧
    ∀ a: α, abv a < 1 → p ∣ a,
  {
    have := _inst_2.principal,
    haveI principal: I.is_principal := this I,
    use submodule.is_principal.generator I,

    have ne_bot: I ≠ ⊥,
    {
      intro h,
      rw submodule.eq_bot_iff at h,
      rcases nontrivial with ⟨ a, ha ⟩,
      have abva_lt_one: abv a < 1,
      from lt_of_le_of_ne (bounded a) ha.2,
      specialize h a abva_lt_one,
      exact ha.1 h,
    },

    refine ⟨ submodule.is_principal.prime_generator_of_prime I ne_bot,
      submodule.is_principal.generator_mem I, _ ⟩,
    intros a ha,
    have a_in_ideal: a ∈ I := ha,
    rw submodule.is_principal.mem_iff_eq_smul_generator I at a_in_ideal,
    cases a_in_ideal with c hc,
    use c,
    rw mul_comm,
    exact hc,
  },

  use [abv p, ((abv_pos abv).2 p_prime.1), abvp_lt_one,
    p, p_prime],
  intros q q_prime,
  exact if hpq: associated q p
    then by {
      simp [hpq],
      cases hpq with c hc,
      rw [← hc, abv_mul abv],
      simp [show abv c = 1, from absolute_value_units_bounded abv bounded c],
    }
    else by {
      simp [hpq],
      by_contra h,
      exact hpq (associated.symm $ primes_associated_of_dvd p_prime q_prime $
        p_prop q $ lt_of_le_of_ne (bounded q) h),
    },
end

theorem abv_bounded_padic {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1)
    (nontrivial: ∃ a: α, a ≠ 0 ∧ abv a ≠ 1):
      ∃ (p: α) [p_prime: fact (prime p)], abvs_equiv abv (@sample_padic_abv _ _ _ _ p p_prime) :=
begin
  obtain ⟨ c, c_pos, c_lt_one, p, p_prime, prime_vals ⟩ :=
    absolute_value_on_primes abv bounded nontrivial,
  use [p, p_prime],

  set a := - real.log 2 / real.log c with a_def,
  have a_pos: 0 < a,
  {
    refine div_pos_of_neg_of_neg (neg_of_neg_pos _) (real.log_neg c_pos c_lt_one),
    rw neg_neg,
    exact real.log_pos one_lt_two,
  },
  use [a, a_pos],
  set φ₁ := hom_of_equiv (hom_of_abv abv) a a_pos
    (λ a, (show abv = (hom_of_abv abv), from rfl) ▸ abv_nonneg abv a) with φ₁_def,
  haveI : fact (prime p) := fact_iff.2 p_prime,
  set φ₂ := hom_of_abv (sample_padic_abv p) with φ₂_def,
  have φ₁_f: (λ x, abv x ^ a) = φ₁ := rfl,
  have φ₂_f: sample_padic_abv p = φ₂ := rfl,
  rw [φ₁_f, φ₂_f],
  suffices: φ₁ = φ₂, by { rw this, },
  apply ext_hom_primes,
  by simp [← φ₁_f, ← φ₂_f,
    absolute_value_units_bounded abv bounded,
    absolute_value_units_bounded (sample_padic_abv p)
      (sample_padic_abv_bounded p)],
  {
    rw [← φ₁_f, ← φ₂_f],
    intros q hq,
    have q_prime := principal_ideal_ring.irreducible_iff_prime.1 hq,
    dsimp,
    rw prime_vals q q_prime,
    rw sample_padic_abv_on_primes p q q_prime,
    rw a_def,
    exact if hpq: associated q p
      then by {
        simp only [hpq, if_true],
        apply log_inj_pos (real.rpow_pos_of_pos c_pos _) one_half_pos,
        rw real.log_rpow c_pos,
        calc -real.log 2 / real.log c * real.log c
          = -real.log 2 * (real.log c / real.log c) : by ring
          ... = - real.log 2 : by { rw [div_self (real.log_ne_zero_of_ne_one c c_pos $
            ne_of_lt c_lt_one), mul_one], }
          ... = real.log (1/2) : by rw [← real.log_inv, inv_eq_one_div],
      }
      else by simp [hpq],
  },
end
