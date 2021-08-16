import data.real.cau_seq
import algebra.big_operators.basic
import algebra.big_operators.ring

import valuations.basic
import for_mathlib.specific_limits

open is_absolute_value
open_locale classical big_operators

lemma absolute_value_units_bounded {α} [ring α] [nontrivial α]
  (abv: α → ℝ) [is_absolute_value abv]
  (bounded: ∀ a: α, abv a ≤ 1): ∀ u: units α, abv u = 1 :=
begin
  intro u,
  by_contra h,
  have abvc_lt_one: abv u.val < 1 := lt_of_le_of_ne (bounded u) h,
  have prod_eq: abv u.val * abv u.inv = 1 * 1,
  by rw [← abv_mul abv, u.val_inv, abv_one abv, one_mul],
  have prod_lt: abv u.val * abv u.inv < 1 * 1,
  {
    have: u.inv ≠ 0,
    {
      intro h,
      have := u.val_inv,
      rw [h, mul_zero] at this,
      exact zero_ne_one this,
    },
    exact mul_lt_mul abvc_lt_one (bounded u.inv)
      ((abv_pos abv).2 this) zero_le_one,
  },
  exact (ne_of_lt prod_lt) prod_eq,
end

theorem nonarchimedian_iff_integers_bounded
  {α} [comm_ring α] [nontrivial α] (abv: α → ℝ) [is_absolute_value abv]:
  (∃ C: ℝ, 0 < C ∧ ∀ n: ℕ, abv n ≤ C) ↔ (∀ a b: α, abv (a + b) ≤ max (abv a) (abv b)) :=
begin
  split,
  {
    rintros ⟨ C, h ⟩ a b,
    have max_nonneg: 0 ≤ max (abv a) (abv b),
    from le_trans (abv_nonneg abv a) (le_max_left _ _),

    have: ∀ n: ℕ, abv (a + b) ^ n ≤ C * (n + 1) * (max (abv a) (abv b) ^ n),
    {
      intro n,

      have p₁: ∀ m ≤ n, abv (a^m * b^(n - m) * nat.choose n m)
        ≤ C * (max (abv a) (abv b) ^ n),
      {
        intros m hm,
        simp only [abv_mul abv, abv_pow abv],
        
        have p₁: abv a ^ m ≤ (max (abv a) (abv b)) ^ m,
        from pow_le_pow_of_le_left (abv_nonneg abv a) (le_max_left _ _) _,
        have p₂: abv b ^ (n - m) ≤ (max (abv a) (abv b)) ^ (n - m),
        from pow_le_pow_of_le_left (abv_nonneg abv b) (le_max_right _ _) _,
        have p₃: abv (nat.choose n m) ≤ C,
        from h.2 _,

        calc abv a ^ m * abv b ^ (n - m) * abv (nat.choose n m)
          ≤ max (abv a) (abv b) ^ m * max (abv a) (abv b) ^ (n - m) * C
            : by {
              refine mul_le_mul
                (mul_le_mul p₁ p₂ (pow_nonneg (abv_nonneg abv _) _) _)
                p₃ (abv_nonneg abv _)
                (mul_nonneg _ _); exact pow_nonneg max_nonneg _,
            }
          ... = (max (abv a) (abv b) ^ n) * C
            : by { rw ← pow_add, congr, exact nat.add_sub_cancel' hm, }
          ... = C * (max (abv a) (abv b) ^ n)
            : by ring,
      },

      calc abv (a + b) ^ n = abv ((a + b) ^ n) : eq.symm (abv_pow abv _ _)
        ... = abv (∑ (m: ℕ) in finset.range (n + 1), a^m * b^(n - m) * nat.choose n m)
          : by { rw add_pow a b n, }
        ... ≤ ∑ (m: ℕ) in finset.range (n + 1), abv (a^m * b^(n - m) * nat.choose n m)
          : abv_sum_le_sum_abv _ _
        ... ≤ ∑ (m: ℕ) in finset.range (n + 1), C * (max (abv a) (abv b) ^ n)
          : by {
            refine finset.sum_le_sum (λ m hm, p₁ m _),
            rw finset.mem_range at hm,
            linarith only [hm],
          }
        ... = C * ∑ (m: ℕ) in finset.range (n + 1), (max (abv a) (abv b) ^ n)
          : eq.symm finset.mul_sum
        ... = C * (n + 1) * (max (abv a) (abv b) ^ n)
          : by { simp, rw mul_assoc, },
    },

    suffices h₁: ∀ n: ℕ, (abv (a + b) ^ (n: ℝ)) ^ (1/n: ℝ)
      ≤ (C * (n + 1) * (max (abv a) (abv b) ^ (n: ℝ))) ^ (1/n: ℝ),
    {
      have: ∀ n: ℕ, 0 < n → abv (a + b) ≤
        (C * (n + 1)) ^ (1/n: ℝ) * (max (abv a) (abv b)),
      {
        intros n hn,
        specialize h₁ n,
        rw ← real.rpow_mul (abv_nonneg abv (a + b)) _ _ at h₁,
        rw real.mul_rpow
          (mul_nonneg (le_of_lt h.1)
            (show 0 ≤ (n:ℝ) + 1, by { norm_cast, linarith, }))
          (real.rpow_nonneg_of_nonneg max_nonneg n) at h₁,
        rw ← real.rpow_mul max_nonneg _ _ at h₁,
        rw mul_one_div_cancel (show (n: ℝ) ≠ 0,
          by { norm_cast, exact ne.symm (ne_of_lt hn), } ) at h₁,
        repeat { rw real.rpow_one at h₁, },
        exact h₁,
      },
      have lim₀: filter.tendsto (λ n: ℕ, (C * (n + 1)) ^ (1/n: ℝ)) filter.at_top (nhds 1) := tendsto_comparison_at_top_nhds_1_of_pos h.1,
      have lim₁: filter.tendsto (λ n: ℕ, abv (a + b)) filter.at_top (nhds (abv (a + b))),
      { exact tendsto_const_nhds, },
      have lim₂: filter.tendsto
        (λ n: ℕ, (C * (n + 1)) ^ (1/n: ℝ) * (max (abv a) (abv b)))
        filter.at_top (nhds (max (abv a) (abv b))),
      {
        convert tendsto.mul_const (max (abv a) (abv b)) lim₀,
        rw one_mul,
      },
      
      apply le_of_tendsto_of_tendsto lim₁ lim₂,
      simp only [filter.eventually_le, filter.eventually_at_top],
      exact ⟨ 1, λ n, this n ⟩,
    },

    intro n,
    specialize this n,
    simp only [real.rpow_nat_cast],

    have low_bound: 0 ≤ C * (n + 1: ℝ) * max (abv a) (abv b) ^ n,
    from mul_nonneg (mul_nonneg (le_of_lt h.1)
      (by { norm_cast, simp, })) (pow_nonneg max_nonneg n),
    
    apply_fun (λ x: ℝ, (max 0 x) ^ (1/n: ℝ)) at this,
    simp only [abv_nonneg abv (a + b), low_bound, max_eq_right, pow_nonneg] at this,
    exact this,
    intros x y hxy,
    dsimp,
    apply real.rpow_le_rpow
      (le_max_left _ _) (max_le_max (le_refl 0) (hxy))
      (one_div_nonneg.2 $ nat.cast_nonneg n),
  },
  {
    intro h,
    use [1, zero_lt_one],
    intro n,
    induction n with n hn,
    simp [abv_zero abv, zero_le_one],
    rw ← nat.add_one,
    push_cast,
    calc abv (n + 1) ≤ max (abv n) (abv 1) : h n 1
      ... ≤ max 1 1 : max_le_max hn (by { rw abv_one abv, })
      ... = 1 : by simp,
  },
end
