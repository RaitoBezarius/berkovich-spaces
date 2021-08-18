import analysis.special_functions.pow
import data.set.function
import analysis.calculus.lhopital
import analysis.calculus.mean_value
import analysis.asymptotics.asymptotics

open filter
open_locale filter topological_space

lemma tendsto_root_at_top_nhds_1_of_pos {C: ℝ} (c_pos: C > 0):
  filter.tendsto (λ (n: ℕ), C^((1: ℝ) / n)) filter.at_top (nhds 1) :=
begin
  have h_exp_form: (λ (n: ℕ), C^((1: ℝ)/n)) = (λ (n: ℕ), real.exp((real.log C) / n)),
  {
    ext,
    simp,
    rw div_eq_mul_inv,
    rw real.exp_mul,
    rw real.exp_log c_pos,
  },
  {
    rw h_exp_form,
    apply filter.tendsto.comp,
    apply real.tendsto_exp_nhds_0_nhds_1,
    apply tendsto_const_div_at_top_nhds_0_nat,
  }
end

lemma tendsto_log1_plus_x_under_x_at_top_nhds_1:
  tendsto (λ (x: ℝ), real.log (1 + x) / x) at_top (𝓝 0) :=
begin
  have h: tendsto (λ (x : ℝ), 1 + x) at_top at_top,
  from tendsto_at_top_mono (by simp [zero_le_one]) (tendsto_id),
  apply asymptotics.is_o.tendsto_0,
end

lemma tendsto_comparison_at_top_nhds_1_of_pos {C: ℝ} (C_pos: C > 0):
  filter.tendsto (λ (n: ℕ), (C*(n + 1))^((1: ℝ) / n)) filter.at_top (nhds 1) :=
begin
  have h_exp_form: (λ (n: ℕ), (C*(n + 1))^((1: ℝ) / n)) = (λ (n: ℕ), real.exp((real.log (C*(n + 1)) / n))),
  {
    ext,
    simp,
    rw [div_eq_mul_inv, real.exp_mul, real.exp_log _],
    exact (zero_lt_mul_right (by exact_mod_cast nat.zero_lt_succ _)).2 C_pos,
  },
  {
    rw h_exp_form,
    apply filter.tendsto.comp,
    apply real.tendsto_exp_nhds_0_nhds_1,
    have : (λ (x: ℕ), real.log (C * (x + 1)) / x) = (λ (x: ℕ), ((real.log C / x) + real.log (1 + x) / x)),
    {
      ext,
      rw_mod_cast [real.log_mul (ne_of_gt C_pos) _, add_comm x 1, add_div _ _],
      exact_mod_cast nat.succ_ne_zero _,
    },
    rw [this],
    convert filter.tendsto.add
    (tendsto_const_div_at_top_nhds_0_nat (real.log C))
    (tendsto_log1_plus_x_under_x_at_top_nhds_1.comp tendsto_coe_nat_at_top_at_top),
    simp,
  }
end
