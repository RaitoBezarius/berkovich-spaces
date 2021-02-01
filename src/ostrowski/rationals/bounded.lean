
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import data.real.cau_seq

import ostrowski.rationals.basic
import abvs_equiv

open list is_absolute_value

lemma prime_norm_lt_one_of_bounded_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1)):
      ∃ p: ℕ, prime p ∧ abv p < 1 :=
begin
  by_contra,
  push_neg at h,

  suffices h': ∀ n: ℕ, n ≠ 0 → abv n = 1,
  {
    apply hnontriv,
    set abv_hom := hom_of_abv abv with abv_hom_def,
    set triv_hom := hom_of_abv trivial_abs with triv_hom_def,
    have abv_hom_f: abv = abv_hom := by refl,
    have triv_hom_f: trivial_abs = triv_hom := by refl,
    rw [abv_hom_f, triv_hom_f],
    apply mul_mor_eq_of_eq_on_pnat,
    {
      rw [← abv_hom_f, ← triv_hom_f],
      rw [abv_neg abv, abv_neg trivial_abs],
      rw [abv_one abv, abv_one trivial_abs],
    },
    {
      intro n,
      rw [← abv_hom_f, ← triv_hom_f],
      unfold trivial_abs,
      by_cases h'': n = 0,
      {
        rw h'',
        simp,
        rw abv_zero abv,
      },
      {
        rw h' n h'',
        simp [h''],
      }
    },
  },
  
  apply @induction_on_primes (λ n, n ≠ 0 → abv n = 1),
  { tauto },
  { intro h, exact abv_one abv, },
  {
    intros p a p_prime ha hprod,
    push_cast,
    rw abv_mul abv,
    have abvp_eq_one: abv p = 1,
    { by linarith [h p p_prime, all_nat_le_one p], },
    rw abvp_eq_one,
    have a_ne_zero: a ≠ 0,
    { by_contra h, push_neg at h, apply hprod, simp [h], },
    rw ha a_ne_zero,
    simp,
  },
end

lemma padic_norm_q (p: ℕ) (q: ℕ) (p_prime: prime p) (q_prime: prime q):
  (p = q → padic_norm p q = 1/p) ∧ (p ≠ q → padic_norm p q = 1) :=
begin
  split,
  {
    intro h, -- In the case where `p = q`
    have p: padic_val_rat p q = 1,
    {
      rw ← h,
      unfold padic_val_rat,
      simp [p_prime.1, prime.ne_one p_prime],
    },
    unfold padic_norm,
    rw p,
    simp [q_prime.1],
  },
  {
    intro h, -- In the case where `p ≠ q`
    have p: padic_val_rat p q = 0,
    {
      unfold padic_val_rat,
      simp [q_prime.1, prime.ne_one p_prime],
      suffices h: p^0 ∣ q ∧ ¬ p^1 ∣ q,
      {
        norm_cast,
        rw roption.get_eq_iff_eq_some,
        rw multiplicity.eq_some_iff.2 h,
        refl,
      },
      split,
      {
        simp,
      },
      {
        by_contra p_div_q,
        apply h,
        rw ← associated_iff_eq,
        simp at p_div_q,
        have q_div_p := dvd_symm_of_irreducible
          (irreducible_of_prime p_prime)
          (irreducible_of_prime q_prime)
          p_div_q,
        exact associated_of_dvd_dvd p_div_q q_div_p,
      },
    },
    unfold padic_norm,
    rw p,
    simp [q_prime.1],
  },
end

lemma abs_val_bounded_q (abv : ℚ → ℝ) [habv : is_absolute_value abv]
  (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1))
  (p: ℕ) (p_prime: prime p) (abvp_lt_one: abv p < 1):
  ∃ α: ℝ, 0 < α ∧ ∀ q: ℕ, prime q →
    (p = q → abv q = (1/p) ^ α) ∧ (p ≠ q → abv q = 1 ^ α) :=
begin
  -- We set `α` such that it Just Works™
  set α := - real.log (abv p) / real.log p with α_def,
  
  have α_pos: 0 < α,
  {
    obtain ⟨ p_pos_ℝ, p_nonzero_ℚ ⟩: 0 < (p: ℝ) ∧ (p: ℚ) ≠ 0,
    {
      norm_cast,
      exact ((λ p_pos, and.intro p_pos (ne.symm $ ne_of_lt p_pos)) $
        nat.prime.pos $ nat.prime_iff_prime.2 p_prime),
    },

    refine div_pos (neg_pos_of_neg $
        (real.log_neg_iff ((abv_pos abv).2 p_nonzero_ℚ)).2 $ gt_iff_lt.2 abvp_lt_one) _,
    rw_mod_cast real.log_pos_iff p_pos_ℝ,
    exact (nat.prime.one_lt $ nat.prime_iff_prime.2 p_prime),
  },
  use [α, α_pos],

  intros q q_prime,

  split,
  intro h,
  {
    -- When `p = q`, we just need to show that `abv p = p ^ (- α)`.
    have p_pos: 0 < (p: ℝ),
    { norm_cast, exact nat.lt_of_le_and_ne (zero_le p) (ne.symm (p_prime.1)), },
    -- The result is clear by definition of `α`.
    -- The calculus that leads to it is yet long to formalize...
    rw ← h,
    suffices h: real.log (abv p) = real.log ((1/p) ^ α),
    {
      refine (λ p₁ p₂, le_antisymm
        ((real.log_le_log p₁ p₂).1 $ le_of_eq h)
        ((real.log_le_log p₂ p₁).1 $ le_of_eq $ eq.symm h)) _ _,
      {
        apply gt_iff_lt.2 ∘ (abv_pos abv).2,
        norm_cast,
        exact p_prime.1,
      },
      from (real.rpow_pos_of_pos $ one_div_pos.2 p_pos) α,
    },
    have one_lt_p: 1 < p,
    from (nat.prime.one_lt ∘ nat.prime_iff_prime.2) p_prime,
    calc real.log (abv p) = real.log (abv p) * 1
        : by ring
      ... = real.log (abv p) * (real.log p / real.log p)
        : by { rw div_self, symmetry, apply ne_of_lt ∘ real.log_pos,
          norm_cast, exact one_lt_p, }
      ... = real.log (abv p) / real.log p * real.log p
        : by ring
      ... = real.log (p^(real.log (abv p) / real.log p))
        : by { rw ← real.log_rpow, exact p_pos, }
      ... = real.log (p^(- (- real.log (abv p) / real.log p)))
        : by ring
      ... = real.log (p^(-α))     : by rw α_def
      ... = real.log (p^(-1 * α)) : by ring
      ... = real.log ((p ^ (-1: ℝ)) ^ α)
        : by { congr' 1, exact real.rpow_mul (le_of_lt p_pos) (-1) α, }
      ... = real.log (((p ^ (1: ℝ))⁻¹) ^ α)
        : by { congr' 2, exact real.rpow_neg (le_of_lt p_pos) 1, }
      ... = real.log ((p⁻¹) ^ α)
        : by { congr' 3, exact real.rpow_one p, }
      ... = real.log ((1/p) ^ α)  : by simp,
  },
  {
    intro h,
    rw real.one_rpow α,

    -- We reason by contradiction. Our hypothesis becomes `abv q < 1`.
    by_contradiction h',
    have abvq_lt_one: abv q < 1,
    from lt_iff_le_and_ne.2 ⟨ (all_nat_le_one q), h' ⟩,
    -- We find `N` such that `(abv p) ^ N, (abv q) ^ N < 1/2`.
    obtain ⟨ n, abvpn_lt_half, abvqn_lt_half ⟩: ∃ n: ℕ, ((abv p)^n < 1/2) ∧ ((abv q)^n < 1/2),
    {
      have geom_tendsto_zero: ∀ r: ℝ, (0 ≤ r) → (r < 1) →
        ∃ N: ℕ, ∀ n ≥ N, r^n < 1/2,
      {
        -- Again, some formal play.
        -- Went actually pretty nicely !
        intros r h₁ h₂,
        have p := metric.tendsto_at_top.1 (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂),
        specialize p (1/2) (by linarith),
        rcases p with ⟨ N, hN ⟩,
        use N,
        intros n hn,
        specialize hN n hn,
        calc r^n = r^n - 0                 : by simp
          ... ≤ max (r^n - 0) (-(r^n - 0)) : le_max_left _ _
          ... < 1/2 : hN,
      },
      obtain ⟨ N₁, pN₁ ⟩: ∃ N: ℕ, ∀ n ≥ N, (abv p)^n < 1/2,
      { exact geom_tendsto_zero (abv p) (abv_nonneg abv p) abvp_lt_one },
      obtain ⟨ N₂, pN₂ ⟩: ∃ N: ℕ, ∀ n ≥ N, (abv q)^n < 1/2,
      { exact geom_tendsto_zero (abv q) (abv_nonneg abv q) abvq_lt_one },
      use max N₁ N₂,
      exact ⟨
        pN₁ (max N₁ N₂) (by linarith only [le_max_left N₁ N₂]),
        pN₂ (max N₁ N₂) (by linarith only [le_max_right N₁ N₂])
      ⟩,
    },
    -- We use Bézout to find `u`, `v` such that `1 = u * p^n + v * q^n`.
    obtain ⟨ u, v, bezout ⟩: ∃ u: ℤ, ∃ v: ℤ, 1 = u * p^n + v * q^n,
    {
      have p₁: ((p^n).gcd (q^n): ℤ) = (1: ℤ),
      {
        suffices coprimes: p.coprime q,
        by exact_mod_cast (nat.coprime.pow_left n $ nat.coprime.pow_right n coprimes),
        rw nat.coprime_primes (nat.prime_iff_prime.2 p_prime) (nat.prime_iff_prime.2 q_prime),
        exact h,
      },
      use [(p^n).gcd_a (q^n), (p^n).gcd_b (q^n)],
      rw [← p₁, mul_comm _ (p^n: ℤ), mul_comm _ (q^n: ℤ)],
      exact_mod_cast nat.gcd_eq_gcd_ab (p^n) (q^n),
    },
    have abv_rel_le_one: ∀ k: ℤ, abv k ≤ 1,
    {
      intro k,
      by_cases h: 0 < k,
      {
        rw [← abs_of_pos h, int.abs_eq_nat_abs],
        exact all_nat_le_one _,
      },
      {
        rw_mod_cast [← abv_neg abv, ← abs_of_nonpos $ not_lt.1 h, int.abs_eq_nat_abs],
        exact all_nat_le_one _,
      }
    },
    have abv_bezout_lt_one: abv (u * p^n + v * q^n) < 1,
    {
      -- Is there a way to simplify this ?
      -- (Of course these two properties could be gathered in one function...)
      have p₁: abv u * abv p ^ n ≤ 1 * abv p ^ n,
      { exact (mul_le_mul_right
        (pow_pos ((abv_pos abv).2 (by { norm_cast, exact p_prime.1, })) n)).2
        (abv_rel_le_one u), },
      have p₂: abv v * abv q ^ n ≤ 1 * abv q ^ n,
      { exact (mul_le_mul_right
        (pow_pos ((abv_pos abv).2 (by { norm_cast, exact q_prime.1, })) n)).2
        (abv_rel_le_one v), },
      calc abv (u * p^n + v * q^n)
        ≤ abv (u * p^n) + abv (v * q^n) : abv_add abv _ _
        ... = abv u * abv (p^n) + abv v * abv (q^n) : by { congr; rw abv_mul abv _ _, }
        ... = abv u * abv p ^ n + abv v * abv q ^ n : by { congr; rw abv_pow abv _ _, }
        ... ≤ 1 * abv p ^ n + 1 * abv q ^ n         : add_le_add p₁ p₂
        ... = abv p ^ n + abv q ^ n                 : by ring
        ... < 1/2 + 1/2                             : add_lt_add abvpn_lt_half abvqn_lt_half
        ... = 1                                     : by ring,
    },
    have absurd: (1: ℝ) < 1,
    {
      calc 1 = abv (1: ℤ)             : eq.symm (abv_one abv)
        ... = abv (u * p^n + v * q^n) : by { rw bezout, norm_cast, }
        ... < 1                       : abv_bezout_lt_one,
    },
    linarith only [absurd],
  },
end

lemma rat_abs_val_one_bounded_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1)):
      ∃ (p) [hp: nat.prime p],
      @abvs_equiv _ _ abv (padic_norm_ℝ p) habv (@padic_is_abv p hp) :=
begin
  obtain ⟨ p, p_prime, abvp_lt_one ⟩: ∃ p: ℕ, prime p ∧ abv p < 1,
  from prime_norm_lt_one_of_bounded_padic abv hnontriv all_nat_le_one,

  obtain ⟨ α, zero_lt_α, abv_val ⟩ := abs_val_bounded_q abv all_nat_le_one p p_prime abvp_lt_one,

  -- We show that `abv` is equivalent to the p-adic norm on all primes.
  have same_on_primes: ∀ q: ℕ, prime q → (padic_norm p q: ℝ) ^ α = abv q,
  {
    intros q q_prime,

    /-
    We have already calculated the values of the p-adic norm and of `abv` on
    all prime numbers (lemmas `abs_val_bounded_q` and `padic_norm_q`).
    -/
    have padic_norm := padic_norm_q p q p_prime q_prime,
    specialize abv_val q q_prime,

    by_cases h: p = q,
    {
      rw padic_norm.1 h,
      rw abv_val.1 h,
      simp,
    },
    {
      rw padic_norm.2 h,
      rw abv_val.2 h,
      simp,
    },
  },

  -- Now we reason by induction, by using prime numbers as the base case.
  
  have p_nat_prime := nat.prime_iff_prime.2 p_prime,
  have := @abs_val_equiv_of_equiv_on_primes (padic_norm_ℝ p) abv
    (@padic_is_abv p p_nat_prime) _
    α (ne.symm $ ne_of_lt zero_lt_α) same_on_primes,
  
  use [p, p_nat_prime],
  apply abvs_equiv_symmetric,
  use [α, zero_lt_α],

  exact this,
end
