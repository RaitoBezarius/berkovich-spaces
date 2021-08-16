import analysis.special_functions.pow
import data.set.function

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

-- [C(n + 1)]^(1/n) = exp(log(C[n + 1]) / n) = exp([log C / n] + log (n + 1) / log n)

lemma deriv.lhopital_inf_at_top {l: filter ℝ} {f g: ℝ → ℝ}
  (hdf: ∀ᶠ (x: ℝ) in filter.at_top, differentiable_at ℝ f x)
  (hg': ∀ᶠ (x: ℝ) in filter.at_top, deriv g x ≠ 0)
  (hftop: filter.tendsto f filter.at_top filter.at_top)
  (hgtop: filter.tendsto g filter.at_top filter.at_top)
  (hdiv: filter.tendsto (λ (x: ℝ), deriv f x / deriv g x) filter.at_top l):
  filter.tendsto (λ (x: ℝ), f x / g x) filter.at_top l := sorry

lemma eventually_eq.of_le_ite_at_top {α β: Type*} [preorder α] {f g: α → β} {a: α} {c: β} [decidable_rel ((≤) : α → α → Prop)]:
  filter.eventually_eq filter.at_top (λ (x: α), if (x ≤ a) then c else (f x)) g := sorry
lemma eventually.eq_of_eq_ite_at_top {α β: Type*} [preorder α] {f g: α → β} {a: α} {c: β} [decidable_eq α]:
  filter.eventually_eq filter.at_top (λ (x: α), if (x = a) then c else (f x)) g := sorry

lemma deriv.log_1_plus_x: deriv (λ (x: ℝ), real.log (1 + x)) = λ (x: ℝ), if x = -1 then 0 else (1 / (1 + x)) := sorry

lemma deriv.log_1_plus_x_eventually_at_top: 
  filter.eventually_eq filter.at_top 
  (deriv (λ (x: ℝ), real.log (1 + x))) (λ (x: ℝ), 1 / (1 + x)) :=
by rw [deriv.log_1_plus_x]; exact eventually.eq_of_eq_ite_at_top

lemma tendsto_log1_plus_x_under_x_at_top_nhds_1:
  filter.tendsto (λ (x: ℝ), real.log (1 + x) / x) filter.at_top (nhds 0) :=
begin
  have h: filter.tendsto (λ (x : ℝ), 1 + x) filter.at_top filter.at_top,
  from filter.tendsto_at_top_mono (by simp [zero_le_one]) (filter.tendsto_id),
  refine deriv.lhopital_inf_at_top _ _ _ filter.tendsto_id _,
  simp only [filter.eventually_at_top, ge_iff_le],
  use 0, intros b hb,
  apply differentiable_at.comp,
  simp only [real.differentiable_at_log_iff, ne.def],
  linarith [hb],
  simp,
  simp,
  exact filter.tendsto.comp real.tendsto_log_at_top h,
  simp only [deriv_id'', div_one],
  refine (filter.tendsto_congr' deriv.log_1_plus_x_eventually_at_top).2 _,
  exact filter.tendsto.div_at_top tendsto_const_nhds h,
end

lemma tendsto_comparison_at_top_nhds_1_of_pos {C: ℝ} (C_pos: C > 0):
  filter.tendsto (λ (n: ℕ), (C*(n + 1))^((1: ℝ) / n)) filter.at_top (nhds 1) :=
begin
  have h_exp_form: (λ (n: ℕ), (C*(n + 1))^((1: ℝ) / n)) = (λ (n: ℕ), real.exp((real.log (C*(n + 1)) / n))),
  {
    ext,
    simp,
    rw [div_eq_mul_inv, real.exp_mul, real.exp_log _],
    sorry,
  },
  {
    rw h_exp_form,
    apply filter.tendsto.comp,
    apply real.tendsto_exp_nhds_0_nhds_1,
    sorry
  }
end
