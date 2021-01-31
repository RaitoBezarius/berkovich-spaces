import data.real.basic
import data.real.cau_seq
import analysis.special_functions.pow

import for_mathlib.nat_digits
import for_mathlib.geom_sum

lemma exists_nonneg_const_nat_abs_le_const_mul_pow_alpha
  (abv: ℚ → ℝ) [habv: is_absolute_value abv]
  (n₀: ℕ) (α: ℝ) 
  (h_exponent_pos: 0 < α)
  (h_n0_ge_2: n₀ ≥ 2)
  (h_abv_n0: abv n₀ = (n₀: ℝ) ^ α)
  (h_abv_n0_gt_one: abv n₀ > 1)
  (h_smallest: ∀ (a: ℕ), a < n₀ → abv a ≤ 1):
  ∃ (C: ℝ) (C_pos: C > 0), ∀ (n: ℕ), abv n ≤ C * n^α :=
begin
  set C := (n₀: ℝ)^α / ((n₀: ℝ)^α - 1),
  use C,
  have h_n0_pow_alpha_pos: 0 < (n₀: ℝ)^α,
  {
    apply real.rpow_pos_of_pos,
    refine lt_of_lt_of_le zero_lt_two _,
    norm_cast,
    exact h_n0_ge_2,
  },
  split,
  {
    apply div_pos,
    exact h_n0_pow_alpha_pos,
    simp,
    refine real.one_lt_rpow _ h_exponent_pos,
    refine lt_of_lt_of_le one_lt_two _,
    norm_cast,
    exact h_n0_ge_2
  },
  {
    intro n,
    set base_repr := n₀.digits n with h_base_repr,
    have h_coeff_abv_pos: ∀ (a: ℕ), a ∈ base_repr → abv a ≤ 1,
    {
      intros a h_a_in_base_repr, 
      apply h_smallest,
      rw h_base_repr at h_a_in_base_repr,
      exact nat.digits_lt_base (h_n0_ge_2) h_a_in_base_repr,
    },
    have h_coeff_fun_abv_pos: ∀ (i: ℕ) (hi: i < base_repr.length),
      (λ (i a: ℕ), (abv a) * ((n₀: ℝ) ^ α) ^ i) i (list.nth_le base_repr i hi) ≤ (λ (i a: ℕ), ((n₀: ℝ) ^ α) ^ i) i (list.nth_le base_repr i hi),
    {
      intros i hi,
      simp,
      convert mul_le_mul (h_coeff_abv_pos _ (list.nth_le_mem base_repr i hi)) (le_refl _) _ zero_le_one,
      rw one_mul,
      apply le_of_lt,
      exact pow_pos h_n0_pow_alpha_pos _,
    },
    have h_abs_of_n0_pow_alpha_inv_lt_one: abs (((n₀: ℝ) ^ α)⁻¹) < 1,
    {
      sorry,
    },  
    exact calc (abv n: ℝ) = abv (nat.of_digits n₀ base_repr) : by rw_mod_cast [h_base_repr, nat.of_digits_digits n₀ n]
    ... = abv (list.sum (base_repr.map_with_index (λ i a, a * (n₀: ℚ) ^ i))) : fun_of_digits_eq_fun_of_sum_map_with_index abv n₀ base_repr
    ... ≤ list.sum (base_repr.map_with_index (λ i a, abv ((a: ℚ) * (n₀ : ℚ) ^ i))) : by { rw ← list.map_map_with_index, exact list.abv_sum_le_sum_abv abv _ }
    ... = list.sum (base_repr.map_with_index (λ i a, (abv a) * (abv n₀) ^ i)) : by simp [abv_mul abv, abv_pow abv]
    ... = list.sum (base_repr.map_with_index (λ (i a: ℕ), (abv a) * ((n₀: ℝ) ^ α) ^ i)) : by rw_mod_cast h_abv_n0
    ... ≤ list.sum (base_repr.map_with_index (λ (i a: ℕ), ((n₀: ℝ) ^ α) ^ i)) : sorry -- by { rw_mod_cast list.le_map_with_index _ _ base_repr h_coeff_fun_abv_pos }
    ... = list.sum (list.map (λ i, ((n₀: ℝ) ^ α) ^ i) (list.range base_repr.length)) : by rw list.map_with_index_eq_range_map (λ i a, ((n₀ : ℝ) ^ α) ^ i) (λ i, ((n₀ : ℝ) ^ α) ^ i) base_repr (by simp)
    ... = geom_series ((n₀: ℝ) ^ α) (base_repr.length) : geom_sum_of_sum_of_range_map ((n₀: ℝ) ^ α) base_repr.length
    ... = (n₀ ^ α) ^ (base_repr.length) * geom_series (((n₀: ℝ) ^ α)⁻¹) (base_repr.length) : geom_sum_eq_factor_inv_geom_sum _ _
    ... ≤ (n₀ ^ α) ^ (base_repr.length) * ∑' n: ℕ, (((n₀: ℝ) ^ α)⁻¹) ^ n : sorry -- (mul_le_mul_left h_n0_pow_alpha_pos).2 (real.finite_geom_sum_le_infinite_geom_sum _ _ (by assumption))
    ... = (n₀ ^ α) ^ (base_repr.length) * C : sorry
    ... ≤ C * n^α : sorry,
  },
end

lemma nat_abs_val_le_nat_pow_alpha (abv: ℚ → ℝ)
  [habv: is_absolute_value abv] (n₀: ℕ) (n: ℕ) (α: ℝ)
  (abv_n0_eq_cst: abv n₀ = n₀^α):
  (abv n: ℝ) ≤ n^α :=
begin
    have n_nonneg: 0 < (n: ℝ) := sorry,
    obtain ⟨ C, ⟨ C_pos, abv_pos ⟩ ⟩ := 
      exists_nonneg_const_nat_abs_le_const_mul_pow_alpha abv n α,
    have h_nthroot: ∀ᶠ (N: ℕ) in filter.at_top, abv n ≤ C^((1:ℝ)/N) * n^α,
    {
      simp,
      use 1,
      intros N N_pos,
      have C_pow_pos: 0 < C^((N: ℝ)⁻¹), from real.rpow_pos_of_pos C_pos _,
      have n_pow_alpha_pos: 0 < (n: ℝ)^α, from real.rpow_pos_of_pos n_nonneg _,
      have N_nonneg: 0 < (N: ℝ), by norm_cast; exact lt_of_lt_of_le zero_lt_one N_pos,
      apply (real.rpow_le_rpow_iff _ _ N_nonneg).1,
      -- |n|^N ≤ (C^(1/N)*n^α)^N
      {
        convert abv_pos (n ^ N),
        -- |n|^N = |n^N|
        {
          simp,
          symmetry,
          exact abv_pow abv n N,
        },
        -- (C^(1/N)n^α)^N = C(n^N)^α
        {
          rw real.mul_rpow,
          congr' 1,
          -- (C^(1/N))^N = C
          {
            -- FIXME(Ryan): investigate why cannot use real.rpow_nat_inv_pow_nat properly?
            rw [← real.rpow_mul, inv_mul_cancel, real.rpow_one],
            linarith,
            exact le_of_lt C_pos,
          },
          -- (n^α)^N = (n^N)^α
          {
            rw ← real.rpow_mul,
            rw mul_comm α (↑N),
            rw real.rpow_mul,
            simp,
            all_goals {
              norm_cast,
              exact nat.zero_le n,
            },
          },
          exact le_of_lt C_pow_pos,
          exact le_of_lt n_pow_alpha_pos,
        },
      },
      apply habv.abv_nonneg,
      {
        -- C > 0 → C^(1/N) > 0 as N > 0
        -- n > 0 → n^α > 0 as α > 0
        -- therefore C^(1/N) * n^α > 0
        apply (zero_le_mul_left (gt_iff_lt.1 C_pow_pos)).2,
        exact le_of_lt (gt_iff_lt.1 n_pow_alpha_pos),
      }
    },
    have h_convergence: filter.tendsto (λ (N : ℕ), C ^ ((1: ℝ) / N) * ↑n ^ α) filter.at_top (nhds (↑n ^ α)),
    {
      convert tendsto.mul_const ((n: ℝ)^α) (tendsto_root_at_top_nhds_1_of_pos C_pos),
      rw one_mul,
    },
    -- eventually version is required here but I need to learn about it first :>.
    exact ge_of_tendsto h_convergence h_nthroot,
end

lemma exists_nonneg_const_pow_alpha_le_abs_nat
  (abv: ℚ → ℝ) [habv: is_absolute_value abv]
  (n₀: ℕ) (α: ℝ) 
  (h_exponent_pos: 0 < α)
  (h_n0_ge_2: n₀ ≥ 2)
  (h_abv_n0: abv n₀ = (n₀: ℝ) ^ α)
  (h_abv_n0_gt_one: abv n₀ > 1)
  (h_smallest: ∀ (a: ℕ), a < n₀ → abv a ≤ 1):
  ∃ (C: ℝ) (C_pos: C > 0), ∀ (n: ℕ), C * n^α ≤ abv n := sorry

lemma nat_pow_alpha_le_nat_abs_val (abv: ℚ → ℝ)
  [habv: is_absolute_value abv] (n₀: ℕ) (n: ℕ) (α: ℝ):
  (n: ℝ)^α ≤ (abv n: ℝ) :=
begin
  sorry,
end