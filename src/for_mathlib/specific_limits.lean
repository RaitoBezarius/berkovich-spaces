import analysis.special_functions.pow
import data.set.function
import analysis.calculus.lhopital
import analysis.calculus.mean_value
import analysis.asymptotics.asymptotics
import analysis.asymptotics.asymptotic_equivalent

open filter asymptotics
open_locale filter topological_space asymptotics

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


lemma eventually_nonzero_of_tendsto_at_top {f: ℝ → ℝ} {l: filter ℝ}
  (htop: tendsto f l at_top): ∀ᶠ x in l, f x ≠ 0 :=
  begin
    have: ∀ᶠ (y: ℝ) in at_top, y ≠ 0,
    {
      simp [eventually_at_top],
      exact ⟨ 1, λ b hb, by linarith only [hb] ⟩,
    },
    convert tendsto.eventually htop this,
  end

lemma eventually_false_of_not {α} {p q: α → Prop} {l: filter α}
  (hnp: ∀ᶠ x in l, ¬ p x): (∀ᶠ x in l, p x → q x) :=
  eventually.mono hnp (λ x hnpx hpx, absurd hpx hnpx)

lemma asymptotics.is_o.of_tendsto_at_top {f: ℝ → ℝ} {l: filter ℝ}
  (htop: tendsto f l at_top): is_o (1: ℝ → ℝ) f l :=
  begin
    refine (asymptotics.is_o_iff_tendsto' _).2 _,
    exact eventually_false_of_not (eventually_nonzero_of_tendsto_at_top htop),
    convert tendsto.inv_tendsto_at_top htop,
    ext, simp,
  end

lemma asymptotics.is_equivalent.left_comp_log {f g: ℝ → ℝ} {l: filter ℝ}
  (h: f ~[l] g) (htop: tendsto f l at_top): real.log ∘ f ~[l] real.log ∘ g :=
  begin
    have fact1 : is_o (real.log ∘ f - real.log ∘ g) (1: ℝ → ℝ) l,
    {
      have hnonvanish: ∀ᶠ x in l, g x ≠ 0 := (eventually_nonzero_of_tendsto_at_top (is_equivalent.tendsto_at_top h htop)),
      refine (asymptotics.is_o_iff_tendsto _).2 _,
      simp only [forall_false_left, forall_const, pi.one_apply, one_ne_zero],
      simp only [function.comp_app, pi.one_apply, div_one, pi.sub_apply],
      refine tendsto.congr'
        (_: real.log ∘ (f / g) =ᶠ[l] (λ (x: ℝ), real.log (f x) - real.log (g x))) _,
      convert eventually.mono _ (λ (x: ℝ) (hx: f x ≠ 0 ∧ g x ≠ 0), @real.log_div (f x) (g x) hx.1 hx.2),
      exact (eventually_nonzero_of_tendsto_at_top htop).and hnonvanish,
      convert (real.continuous_at_log _).tendsto.comp 
        ((is_equivalent_iff_tendsto_one hnonvanish).1 h),
      all_goals { simp, },
    },
    have fact2 : is_o 1 (real.log ∘ g) l := 
      asymptotics.is_o.of_tendsto_at_top
        (real.tendsto_log_at_top.comp
        ((asymptotics.is_equivalent.tendsto_at_top_iff h).1 htop)),
    exact is_o.trans fact1 fact2,
  end

lemma tendsto_log1_plus_x_under_x_at_top_nhds_1:
  tendsto (λ (x: ℝ), real.log (1 + x) / x) at_top (𝓝 0) :=
begin
  have h: tendsto (λ (x : ℝ), 1 + x) at_top at_top,
  from tendsto_at_top_mono (by simp [zero_le_one]) (tendsto_id),
  suffices : asymptotics.is_o real.log id at_top,
  {
    apply asymptotics.is_o.tendsto_0,
    sorry,
  },
  
  have : asymptotics.is_o id real.exp at_top := sorry,
  convert asymptotics.is_o.comp_tendsto this real.tendsto_log_at_top using 1,
  ext, simp,
  sorry,
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
