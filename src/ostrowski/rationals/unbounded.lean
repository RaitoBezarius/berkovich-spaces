import data.real.basic
import data.real.cau_seq
import analysis.special_functions.pow

import for_mathlib.nat_digits
import for_mathlib.geom_sum
import for_mathlib.valuations
import for_mathlib.specific_limits

lemma sum_le_sum_abv_aux1 {b: ℝ} {l: list ℕ} {abv: ℚ → ℝ}
[is_absolute_value abv]
(hb_nonneg: 0 ≤ b)
(h_abs : ∀ (a: ℕ), a ∈ l → abv a ≤ 1):
list.sum (l.map_with_index (λ (i a: ℕ), abv a * b ^ i))
  ≤ list.sum (l.map_with_index (λ (i a: ℕ), b ^ i)) :=
begin
  have : (λ (i a : ℕ), (abv a) * b ^ i) = (λ (i a : ℕ), b ^ i * (abv a)),
    { ext, rw mul_comm },
  rw this, clear this,
  simp [list.map_with_index_eq_enum_map, list.enum_eq_zip_range, list.map_uncurry_zip_eq_zip_with],
  rw [← list.zip_with_map],
  have : list.take l.length = list.take (list.map (pow (b : ℝ)) (list.range l.length)).length,
    { congr' 1, simp },
  rw [this, list.take_length], clear this,
  refine list.sum_ext_le (by simp) _,
  intros i hi,
  let k : ℕ := l.nth_le i (by simpa using hi),
  specialize h_abs k (list.nth_le_mem _ _ _),
  simp,
  suffices: (b: ℝ) ^ i * abv k ≤ b ^ i * 1,
    { simpa using this },
  refine mul_le_mul (le_refl _)
    h_abs
    (is_absolute_value.abv_nonneg abv k)
    (pow_nonneg hb_nonneg i),
end

lemma exists_nonneg_const_nat_abs_le_const_mul_pow_alpha
  {abv: ℚ → ℝ} [habv: is_absolute_value abv]
  {n₀: ℕ} {α: ℝ} 
  (h_exponent_pos: 0 < α)
  (h_n0_ge_2: n₀ ≥ 2)
  (h_abv_n0: abv n₀ = (n₀: ℝ) ^ α)
  (h_abv_n0_gt_one: abv n₀ > 1)
  (h_smallest: ∀ (a: ℕ), a < n₀ → abv a ≤ 1):
  ∃ (C: ℝ) (C_pos: C > 0), ∀ (n: ℕ), abv n ≤ C * n^α :=
begin
  set C := (1 - ((n₀: ℝ) ^ α)⁻¹)⁻¹ with hc,
  use C,
  have h_n0_pow_alpha_pos: 0 < (n₀: ℝ)^α,
  {
    apply real.rpow_pos_of_pos,
    refine lt_of_lt_of_le zero_lt_two _,
    norm_cast,
    exact h_n0_ge_2,
  },
  have h_n0_pow_alpha_inv_lt_one: ((n₀: ℝ) ^ α)⁻¹ < 1,
  {
      apply inv_lt_one,
      rw h_abv_n0 at h_abv_n0_gt_one,
      exact h_abv_n0_gt_one,
  },
  have C_pos: C > 0,
  {
    apply inv_pos.1,
    rw [hc, inv_inv', sub_pos],
    exact h_n0_pow_alpha_inv_lt_one,
  },
  split,
  { exact C_pos },
  {
    intro n,
    by_cases hn: n = 0,
    rw_mod_cast [hn, is_absolute_value.abv_zero abv, real.zero_rpow, mul_zero],
    exact ne_of_gt h_exponent_pos,
    set base_repr := n₀.digits n with h_base_repr,
    have h_coeff_abv_pos: ∀ (a: ℕ), a ∈ base_repr → abv a ≤ 1,
    {
      intros a h_a_in_base_repr, 
      apply h_smallest,
      rw h_base_repr at h_a_in_base_repr,
      exact nat.digits_lt_base (h_n0_ge_2) h_a_in_base_repr,
    },
    have h_n0_pow_alpha_inv_nonneg: 0 ≤ ((n₀: ℝ) ^ α)⁻¹,
    from inv_nonneg.2 (le_of_lt h_n0_pow_alpha_pos),
    have h_n0_pow_alpha_pow_len_pos: 0 < ((n₀: ℝ) ^ α) ^ (base_repr.length - 1),
    from pow_pos (h_n0_pow_alpha_pos) _,
    have h_n0_pow_neq_0: (n₀: ℝ) ^ α ≠ 0, from ne_of_gt h_n0_pow_alpha_pos,
    have h_n0_pow_neq_1: (n₀: ℝ) ^ α ≠ 1, { rw ← h_abv_n0, exact ne_of_gt h_abv_n0_gt_one },
    have h_n0_pow_alpha_pow_len_le_n_pow_alpha: ((n₀: ℝ) ^ α) ^ (base_repr.length - 1) ≤ (n: ℝ) ^ α,
    {
      have h_n0_nonneg: 0 ≤ n₀, from le_trans zero_le_two h_n0_ge_2,
      suffices: ((n₀: ℝ) ^ α) ^ (base_repr.length - 1) = ((n₀: ℝ) ^ (base_repr.length - 1)) ^ α,
      {
        rw this,
        apply real.rpow_le_rpow,
        apply pow_nonneg,
        norm_cast,
        exact h_n0_nonneg,
        rw h_base_repr,
        norm_cast,
        apply (mul_le_mul_right (lt_of_lt_of_le zero_lt_two h_n0_ge_2)).1,
        rw [← pow_succ', nat.sub_add_cancel],
        conv_rhs {
          rw mul_comm,
        },
        apply nat.base_pow_length_digits_le _ n h_n0_ge_2 hn,
        exact one_le_of_nonzero_digits_length _ _ hn,
        exact le_of_lt h_exponent_pos,
      },
      rw [← real.rpow_nat_cast _ (base_repr.length - 1), ← real.rpow_mul, mul_comm,
          real.rpow_mul, real.rpow_nat_cast _ (base_repr.length - 1)],
      all_goals { norm_cast, exact h_n0_nonneg },
    },
    have h_aux1: base_repr.length - 1 + 1 = base_repr.length,
    from nat.sub_add_cancel (one_le_of_nonzero_digits_length n n₀ hn),
    exact calc (abv n: ℝ) = abv (nat.of_digits n₀ base_repr) : by rw_mod_cast [h_base_repr, nat.of_digits_digits n₀ n]
    ... = abv (list.sum (base_repr.map_with_index (λ i a, a * (n₀: ℚ) ^ i))) : fun_of_digits_eq_fun_of_sum_map_with_index abv n₀ base_repr
    ... ≤ list.sum (base_repr.map_with_index (λ i a, abv ((a: ℚ) * (n₀ : ℚ) ^ i))) : by { rw ← list.map_map_with_index, exact list.abv_sum_le_sum_abv abv _ }
    ... = list.sum (base_repr.map_with_index (λ i a, (abv a) * (abv n₀) ^ i)) : by simp [is_absolute_value.abv_mul abv, is_absolute_value.abv_pow abv]
    ... = list.sum (base_repr.map_with_index (λ (i a: ℕ), (abv a) * ((n₀: ℝ) ^ α) ^ i)) : by rw_mod_cast h_abv_n0
    ... ≤ list.sum (base_repr.map_with_index (λ (i a: ℕ), ((n₀: ℝ) ^ α) ^ i)) : sum_le_sum_abv_aux1 (le_of_lt h_n0_pow_alpha_pos) h_coeff_abv_pos
    ... = list.sum (list.map (pow ((n₀: ℝ) ^ α)) (list.range base_repr.length)) : by rw list.map_with_index_eq_range_map (λ i a, ((n₀ : ℝ) ^ α) ^ i) (λ i, ((n₀ : ℝ) ^ α) ^ i) base_repr (by simp)
    ... = geom_series ((n₀: ℝ) ^ α) (base_repr.length) : geom_sum_of_sum_of_range_map ((n₀: ℝ) ^ α) base_repr.length
    ... = (n₀ ^ α) ^ (base_repr.length - 1) * geom_series (((n₀: ℝ) ^ α)⁻¹) (base_repr.length) : by { rw ← h_aux1, exact geom_sum_eq_factor_inv_geom_sum (base_repr.length - 1) h_n0_pow_neq_0 h_n0_pow_neq_1}
    ... ≤ (n₀ ^ α) ^ (base_repr.length - 1) * ∑' n: ℕ, (((n₀: ℝ) ^ α)⁻¹) ^ n : (mul_le_mul_left h_n0_pow_alpha_pow_len_pos).2 $ real.finite_geom_sum_le_infinite_geom_sum_of_lt_1 (base_repr.length) h_n0_pow_alpha_inv_nonneg (by assumption)
    ... = (n₀ ^ α) ^ (base_repr.length - 1) * C : by erw tsum_geometric_of_lt_1 (inv_nonneg.2 (le_of_lt h_n0_pow_alpha_pos)) h_n0_pow_alpha_inv_lt_one
    ... ≤ n^α * C : (mul_le_mul_right C_pos).2 h_n0_pow_alpha_pow_len_le_n_pow_alpha
    ... = C * n^α : mul_comm _ _,
  },
end

lemma nat_abs_val_le_nat_pow_alpha {abv: ℚ → ℝ}
  [habv: is_absolute_value abv] {n₀: ℕ} {n: ℕ} {α: ℝ}
  (h_exponent_pos: 0 < α)
  (h_n0_ge_2: n₀ ≥ 2)
  (h_abv_n0: abv n₀ = (n₀: ℝ) ^ α)
  (h_abv_n0_gt_one: abv n₀ > 1)
  (h_smallest: ∀ (a: ℕ), a < n₀ → abv a ≤ 1):
  (abv n: ℝ) ≤ n^α :=
begin
    obtain ⟨ C, ⟨ C_pos, abv_pos ⟩ ⟩ := 
      exists_nonneg_const_nat_abs_le_const_mul_pow_alpha 
      h_exponent_pos h_n0_ge_2 h_abv_n0 h_abv_n0_gt_one h_smallest,
    have h_nthroot: ∀ᶠ (N: ℕ) in filter.at_top, abv n ≤ C^((1:ℝ)/N) * n^α,
    {
      simp,
      use 1,
      intros N N_pos,
      by_cases hn: n = 0,
      rw_mod_cast [hn, 
        is_absolute_value.abv_zero abv,
        real.zero_rpow (ne_of_gt h_exponent_pos), mul_zero],
      have C_pow_pos: 0 < C^((N: ℝ)⁻¹), from real.rpow_pos_of_pos C_pos _,
      have n_pow_alpha_pos: 0 < (n: ℝ)^α, from real.rpow_pos_of_pos (by exact_mod_cast nat.pos_of_ne_zero hn) _,
      have N_pos: 0 < (N: ℝ), by norm_cast; exact lt_of_lt_of_le zero_lt_one N_pos,
      apply (real.rpow_le_rpow_iff _ _ N_pos).1,
      -- |n|^N ≤ (C^(1/N)*n^α)^N
      {
        convert abv_pos (n ^ N),
        -- |n|^N = |n^N|
        {
          simp,
          symmetry,
          exact is_absolute_value.abv_pow abv n N,
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
            simp only [real.rpow_nat_cast, nat.cast_pow],
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
  ∃ (C: ℝ) (C_pos: C > 0), ∀ (n: ℕ), C * n^α ≤ abv n :=
begin
  set C := (1 - (1 - (n₀: ℝ)⁻¹) ^ α),
  have C_pos: C > 0,
  {
    sorry,
  },
  use C,
  split,
  {
    exact C_pos,
  },
  {
    intro n,
    by_cases (n = 0),
    rw_mod_cast [h, real.zero_rpow, is_absolute_value.abv_zero abv, mul_zero],
    exact ne_of_gt h_exponent_pos,
    set base_repr := n₀.digits n with base_repr_def,
    set s := base_repr.length with s_def,
    have aux0: n < n₀ ^ s,
    {
      rw [s_def, base_repr_def],
      exact nat.lt_base_pow_length_digits h_n0_ge_2,
    },
    have aux1: abv (n₀ ^ s - n) ≤ (n₀ ^ s - n) ^ α,
    {
      -- apply lemma 1.1
      sorry,
    },
    have aux2: ((n₀: ℝ) ^ s - (n₀: ℝ) ^ α) ^ α = (n₀: ℝ) ^ (α * (s)) * (1 - (n₀: ℝ)⁻¹) ^ α,
    {
      sorry,
    },
    have aux3: (n: ℝ) ^ α ≤ (n₀: ℝ) ^ (α * s),
    {
      rw [mul_comm, real.rpow_mul],
      apply real.rpow_le_rpow,
      rotate 1,
      rw_mod_cast real.rpow_nat_cast _ _,
      exact le_of_lt aux0,
      exact le_of_lt h_exponent_pos,
      all_goals {
        norm_cast,
        exact zero_le _,
      }
    },
    calc abv n = abv (n₀ ^ s - (n₀ ^ s - n)) : by abel
    ... ≥ abv (n₀ ^ s) - abv (n₀ ^ s - n) : is_absolute_value.sub_abv_le_abv_sub abv _ _
    ... = (abv n₀) ^ s - abv (n₀ ^ s - n) : by rw is_absolute_value.abv_pow abv _ _
    ... ≥ (abv n₀) ^ s - (n₀ ^ s - n) ^ α : sorry
    ... = (n₀ ^ α) ^ s - (n₀ ^ s - n) ^ α : by rw h_abv_n0
    ... = n₀ ^ (α * s) - (n₀ ^ s - n) ^ α : by { rw_mod_cast [real.rpow_mul _ _ _, real.rpow_nat_cast _ _], exact zero_le _ }
    ... ≥ n₀ ^ (α * s) - (n₀ ^ s - n₀ ^ α) ^ α : sorry
    ... = C * n₀ ^ (α * s) : sorry
    ... ≥ C * n ^ α : (mul_le_mul_left C_pos).2 aux3,
  }
end

lemma nat_pow_alpha_le_nat_abs_val (abv: ℚ → ℝ)
  [habv: is_absolute_value abv] (n₀: ℕ) (n: ℕ) (α: ℝ):
  (n: ℝ)^α ≤ (abv n: ℝ) :=
begin
  sorry,
end