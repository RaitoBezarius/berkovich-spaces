
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
  -- First we find some `n ∈ ℕ*` such that `abv n < 1`.
  obtain ⟨ n, zero_lt_n, abvn_lt_one ⟩: ∃ n: ℕ, 0 < n ∧ abv n < 1,
  {
    -- `abv` is nontrivial so there is some `r ≠ 0` such that `abv r ≠ 1`.
    obtain ⟨ r, r_ne_zero, abvr_notone ⟩: ∃ r: ℚ, r ≠ 0 ∧ abv r ≠ 1,
    {
      -- Just some formal play, not much to say.
      by_contra h,
      push_neg at h,
      apply hnontriv,
      ext r,
      by_cases h': r = 0,
      {
        rw (abv_eq_zero abv).2 h',
        rw (abv_eq_zero trivial_abs).2 h',
      },
      {
        rw h r h',
        rw [trivial_abs],
        dsimp,
        split_ifs,
        refl,
      },
    },
    -- Let's write `r = a/b`. We get `(abv a)/(abv b) ≠ 1`, then `abv a ≠ abv b`.
    rcases r with ⟨ a, b, b_pos, a_b_coprimes ⟩,
    have not_eq: abv a ≠ abv b,
    {
      -- Just doing the calculus by hand.
      -- Is there a simpler way to do this ?
      rw rat_mk_eq_div at abvr_notone,
      rw is_absolute_value.abv_div abv at abvr_notone,
      intro h,
      rw h at abvr_notone,
      apply abvr_notone,
      ring,
      rw inv_mul_cancel,
      intro h,
      rw (abv_eq_zero abv) at h,
      norm_cast at h,
      linarith,
    },
    -- Then either `abv a` or `abv b` is strictly less than one,
    -- so we have some `n: ℕ` such that `abv n < 1`.
    obtain ⟨ zero_ne_a, zero_ne_b ⟩: 0 ≠ a ∧ 0 ≠ b,
    {
      by_contra h,
      rw ← or_iff_not_and_not at h,
      cases h,
      {
        -- `a = 0` but `r = a/b ≠ 0`.
        apply r_ne_zero,
        rw rat_mk_eq_div,
        rw ← h,
        norm_cast,
        exact rat.zero_mk b,
      },
      {
        -- `b = 0` but `b` is the denominator of `r`; `b_pos` says `0 < b`.
        linarith,
      },
    },

    by_cases abv b = 1,
    {
      -- If `abv b = 1`, we need to discuss wether `a ≥ 0` or not.
      rw h at not_eq,
      cases a,
      {
        -- `a ≥ 0`
        use a,
        rw ← int.coe_nat_eq a at not_eq,
        norm_cast at not_eq,
        have p: abv a ≤ 1,
        from all_nat_le_one a,
        rw lt_iff_le_and_ne,
        rw ← int.coe_nat_eq at zero_ne_a,
        norm_cast,
        norm_cast at zero_ne_a,
        exact ⟨ ⟨ zero_le a, zero_ne_a ⟩, lt_of_le_of_ne p not_eq ⟩,
      },
      {
        -- `a < 0`
        use a + 1,
        push_cast at not_eq,
        rw (abv_neg abv) at not_eq,
        have p: abv (a + 1) ≤ 1,
        from all_nat_le_one (a + 1),
        -- rw lt_iff_le_and_ne,
        push_cast,
        exact ⟨ nat.zero_lt_succ a, lt_of_le_of_ne p not_eq ⟩,
      },
    },
    {
      -- `abv b ≠ 1`, so we show `abv b < 1`, as `b: ℕ`, we get what we wanted.
      use b,
      have p: abv b ≤ 1,
      from all_nat_le_one b,
      exact ⟨ b_pos, lt_of_le_of_ne p h ⟩,
    },
  },

  /-
  We just got : `⟨ n, n_ne_zero, abvn_lt_one ⟩: ∃ n: ℕ, n ≠ 0 ∧ abv n < 1`
  Now we search for some prime `p` such that `abv p < 1`.
  We prove the existence by contradiction : let us suppose that `forall p, abv p < 1`.
  -/
  by_contradiction h,
  push_neg at h,

  -- First we prove that the absolute value commutes with arbitrary products
  have abv_prod_eq_prod_abv: ∀ l: list nat, abv (prod l: ℕ) = prod (list.map (λ k: ℕ, abv k) l),
  {
    intro l,
    induction l with r l h,
    {
      -- The result is clear for the empty list.
      simp,
      exact abv_one abv,
    },
    {
      -- We use the compatibility of absolute values with the product.
      simp,
      rw ← h,
      rw abv_mul abv,
    },
    -- This went surprisingly well !
  },

  -- then that in our case any prouct of primes is equal to `1`.
  -- (We use `= 1` because it avoids performing calculations by hand.)
  have prod_abv_primes_ge_one:
    ∀ l: list nat, (∀ k ∈ l, prime k) → prod (list.map (λ k: ℕ, abv k) l) = 1,
  {
    intro l,
    induction l with r l h',
    simp,
    {
      intro h_primes,
      simp,
      have p₁: abv r = 1 := le_antisymm
        (all_nat_le_one r)                      -- By hypothesis `|…| ≤ 1`.
        (h r (h_primes r (by { left, refl, }))) -- Everyone in `l` is prime therefore `|…| ≥ 1`;
      ,
      -- The product of the rest is equal to `1`.
      have p₂ := h' (λ r h, by { apply h_primes r, right, exact h, }),
      rw p₁,
      rw p₂,
      simp,
    },
  },

  /- the absolute value of the product of the prime factors of `n` is therefore
    greater than or equal to `1`. -/
  have prod_eq_one: abv (prod (nat.factors n): ℕ) = 1,
  {
    rw abv_prod_eq_prod_abv,
    apply prod_abv_primes_ge_one,
    intros p hp,
    rw ← nat.prime_iff_prime,
    exact @nat.mem_factors n p hp,
  },

  rw nat.prod_factors zero_lt_n at prod_eq_one,
  linarith only [abvn_lt_one, prod_eq_one],
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
  have zero_lt_α: 0 < α,
  {
    apply div_pos,
    have one_lt_abvp: abv p < 1,
    {
      rw ← gt_iff_lt,
      exact abvp_lt_one,
    },
    apply neg_pos_of_neg,
    have p_ne_zero_ℚ: (p: ℚ) ≠ 0,
    { norm_cast, linarith only [nat.prime.pos $ nat.prime_iff_prime.2 p_prime], },
    exact (real.log_neg_iff ((abv_pos abv).2 p_ne_zero_ℚ)).2
      one_lt_abvp,
    have p_pos_ℝ: 0 < (p: ℝ),
    { norm_cast, exact (nat.prime.pos $ nat.prime_iff_prime.2 p_prime), },
    exact (real.log_pos_iff p_pos_ℝ).2
        (by { norm_cast, exact (nat.prime.one_lt $ nat.prime_iff_prime.2 p_prime), }),
  },
  use [α, zero_lt_α],

  intros q q_prime,

  split,
  intro h,
  {
    -- When `p = q`, we just need to show that `abv p = p ^ (- α)`.
    have zero_lt_p: 0 < (p: ℝ),
    { norm_cast, exact nat.lt_of_le_and_ne (zero_le p) (ne.symm (p_prime.1)), },
    -- The result is clear by definition of `α`.
    -- The calculus that leads to it is yet long to formalize...
    rw ← h,
    suffices h: real.log (abv p) = real.log ((1/p) ^ α),
    {
      have p₁: abv p > 0,
      {
        apply gt_iff_lt.2,
        apply (abv_pos abv).2,
        norm_cast,
        exact p_prime.1,
      },
      have p₂: (1/p: ℝ)^α > 0,
      {
        apply real.rpow_pos_of_pos,
        rw one_div_pos,
        -- norm_cast,
        exact zero_lt_p,
      },
      apply le_antisymm,
      rw ← real.log_le_log p₁ p₂,
      exact le_of_eq h,
      rw ← real.log_le_log p₂ p₁,
      exact le_of_eq (eq.symm h),
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
        : by { rw ← real.log_rpow, exact zero_lt_p, }
      ... = real.log (p^(- (- real.log (abv p) / real.log p)))
        : by ring
      ... = real.log (p^(-α))     : by rw α_def
      ... = real.log (p^(-1 * α)) : by ring
      ... = real.log ((p ^ (-1: ℝ)) ^ α)
        : by { congr' 1, exact real.rpow_mul (le_of_lt zero_lt_p) (-1) α, }
      ... = real.log (((p ^ (1: ℝ))⁻¹) ^ α)
        : by { congr' 2, exact real.rpow_neg (le_of_lt zero_lt_p) 1, }
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
        unfold dist at p,
        unfold abs at p,
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
        norm_cast,
        suffices coprimes: p.coprime q,
        { exact (nat.coprime.pow_left n ∘ nat.coprime.pow_right n) coprimes },
        rw nat.coprime_primes
          (nat.prime_iff_prime.2 p_prime)
          (nat.prime_iff_prime.2 q_prime),
        exact h,
      },
      use [(p^n).gcd_a (q^n), (p^n).gcd_b (q^n)],
      rw ← p₁,
      rw mul_comm _ (p^n: ℤ),
      rw mul_comm _ (q^n: ℤ),
      norm_cast,
      exact nat.gcd_eq_gcd_ab (p^n) (q^n),
    },
    have abv_rel_le_one: ∀ k: ℤ, abv k ≤ 1,
    {
      intro k,
      by_cases h: 0 < k,
      {
        rw ← abs_of_pos h,
        rw int.abs_eq_nat_abs,
        exact all_nat_le_one _,
      },
      {
        simp at h,
        rw ← abv_neg abv,
        norm_cast,
        rw ← abs_of_nonpos h,
        rw int.abs_eq_nat_abs,
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

  -- set α := - real.log (abv p) / real.log p with α_def,

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
  
  set padic := λ q, (padic_norm p q: ℝ) with padic_def,
  have padic_is_absolute_value: is_absolute_value padic,
  from sorry, -- @padic_norm.is_absolute_value p (nat.prime_iff_prime.2 p_prime),

  have p_nat_prime := nat.prime_iff_prime.2 p_prime,
  have := @abs_val_equiv_of_equiv_on_primes (padic_norm_ℝ p) abv
    (@padic_is_abv p p_nat_prime) _
    α (ne.symm $ ne_of_lt zero_lt_α) same_on_primes,
  
  use [p, p_nat_prime],
  apply abvs_equiv_symmetric,
  use [α, zero_lt_α],

  exact this,
end
