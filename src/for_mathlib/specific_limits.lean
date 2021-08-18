import analysis.special_functions.pow
import data.set.function
import analysis.calculus.lhopital
import analysis.calculus.mean_value

open filter
open_locale filter topological_space

lemma tendsto_aux1 {l: ℝ} {f g: ℝ → ℝ}
  (hg: filter.tendsto g filter.at_top (nhds 0))
  (hc: filter.tendsto (f / (1 - g)) filter.at_top (nhds l)):
  filter.tendsto f filter.at_top (nhds l) :=
  begin
    have lim₁ : tendsto (1 - g) at_top (𝓝 1),
    { rw ← sub_zero (1 : ℝ),
      exact tendsto_const_nhds.sub hg },
    have : (λ (x : ℝ), (1 - g) x * (f / (1 - g)) x) =ᶠ[at_top] f,
    { have : {(0 : ℝ)}ᶜ ∈ 𝓝 (1 : ℝ) := compl_singleton_mem_nhds zero_ne_one.symm,
      have : ∀ᶠ (x : ℝ) in at_top, (1 - g) x ∈ ({(0 : ℝ)} : set ℝ)ᶜ := lim₁ this,
      apply this.mono,
      intros x hx,
      replace hx : 1 - g x ≠ 0, by simpa using hx,
      exact mul_div_cancel' _ hx  },
    simpa using (tendsto_congr' this).mp (lim₁.mul hc)
  end

lemma tendsto_aux2 {u: filter ℝ} {l: ℝ} {f g: ℝ → ℝ}
  (hfg: filter.tendsto (f - g) u (nhds 0))
  (hg: filter.tendsto g u (nhds l)):
  filter.tendsto f u (nhds l) := by convert hfg.add hg; simp

lemma tendsto_aux3 {u: filter ℝ} {l: ℝ} {f g: ℝ → ℝ}
  (hfg: filter.tendsto (f - g) u (nhds l))
  (hg: filter.tendsto g u (nhds 0)):
  filter.tendsto f u (nhds l) := by convert hfg.add hg; simp

lemma tendsto_aux4 {u: filter ℝ} {f: ℝ → ℝ} {c: ℝ}
  (hf: tendsto f u at_top):
  tendsto (λ (x: ℝ), c / f x) u (nhds 0) := sorry

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

/-  rw filter.eventually_iff_exists_mem at *,

  rcases hdf with ⟨ s₁, hs₁, hdf ⟩,
  rcases hg' with ⟨ s₂, hs₂, hg' ⟩,

  let starget := s₁∩s₂, 
  have hstarget_mem: starget ∈ filter.at_top := filter.inter_mem_sets hs₁ hs₂,
  rw filter.mem_at_top_sets at hstarget_mem,
  rcases hstarget_mem with ⟨ δ, hδ ⟩,
  have hδ' : set.Ioi δ ⊆ starget := λ x hx, hδ x (le_of_lt hx),
  have fact2 : ∀ (a b: ℝ), δ ≤ a → a < b → ∃ (c: ℝ) (H: c ∈ set.Ioo a b), (deriv f c) / (deriv g c) = (f b - f a) / (g b - g a),
  {
    have hdg' : differentiable_on ℝ g s₂ := λ y hy, 
      differentiable_at.differentiable_within_at 
      (not_not.1 (mt deriv_zero_of_not_differentiable_at (hg' _ hy))),
    intros a b haδ hab,
    convert 
      exists_ratio_deriv_eq_ratio_slope f hab 
      (λ y hy, continuous_at.continuous_within_at 
      (differentiable_at.continuous_at (hdf _ (hδ _ (le_trans haδ hy.1)).1)))
      (λ y hy, differentiable_at.differentiable_within_at 
        (hdf _ (hδ _ (le_trans haδ (le_of_lt hy.1))).1))
      g 
      (differentiable_on.mono hdg' (λ z (hz: z ∈ set.Icc a b), (hδ _ (le_trans haδ hz.1)).2)).continuous_on 
      (differentiable_on.mono hdg' (λ y hy, (hδ _ (le_trans haδ (le_of_lt hy.1))).2)),
    ext,
    simp only [and_imp, exists_prop, and.congr_right_iff],
    intros hx_mem,
    -- g' nonzero, therefore g monotone, therefore g a < g b, therefore g b - g a ≠ 0
    have fact₀ : g b - g a ≠ 0, from sorry,
    have fact₁ : deriv g x ≠ 0, from hg' _ (hδ _ (le_trans haδ (le_of_lt hx_mem.1))).2,
    field_simp [fact₀, fact₁, mul_comm _ (g b - g a), mul_comm _ (f b - f a)],
  },
  have fact2_plus: ∀ (s: set ℝ) (hs: s ∈ (nhds l)), ∃ (c: ℝ) (H: c ≥ δ), ∀ (a b: ℝ), c ≤ a → a < b → (f b - f a) / (g b - g a) ∈ s,
  {
    choose! k P Q using fact2,
    rw filter.tendsto_at_top' at hdiv,
    intros u hu,
    obtain ⟨ δ', hdiv' ⟩ := hdiv u hu,
    use (max δ δ'),
    split,
    exact le_max_left _ _,
    intros a b haδ hab,
    have: δ ≤ a, from le_trans (le_max_left _ _) haδ,
    rw [← Q a b this hab],
    exact 
      hdiv' 
      _ 
      (le_trans 
        (le_max_right _ _) 
        (le_trans 
          haδ 
          (le_of_lt 
            (P a b this hab).1
          )
        )
      ),
  },
  have fact3: ∀ (s: set ℝ) (hs: s ∈ (nhds l)), ∃ (c: ℝ) (H: c ≥ δ), ∀ x ∈ set.Ioi c, (f x - f c) / (g x - g c) ∈ s,
  {
    intros s hs,
    obtain ⟨ c, ⟨ hcδ, hc ⟩ ⟩ := fact2_plus s hs,
    use c,
    split,
    exact hcδ,
    intros x hx,
    exact hc c x (le_refl _) (set.mem_Ioi.1 hx),
  },
  have fact4 : filter.tendsto 
  (λ (x: ℝ), ((f x) / (g x) - (f δ) / (g x)) / (1 - (g δ) / (g x))) filter.at_top (nhds l),
  {
    sorry,
  },
  convert tendsto_aux3 (tendsto_aux1 _ fact4) _,
  all_goals { exact tendsto_aux4 hgtop },
-/

lemma deriv.comp_inv {f : ℝ → ℝ} {x: ℝ}
  (hx: x ≠ 0) (hdf: differentiable_at ℝ f (1 / x)): deriv (λ (y: ℝ), f y⁻¹) x = - (deriv f (1 / x)) / x^2 :=
  begin
    simp [← one_div],
    rw [deriv.comp _ hdf],
    field_simp,
    sorry,
    -- simp [one_div, differentiable_at_inv hx],
  end

lemma deriv.lhopital_at_top_nhds_right_on_Ioo {l a b: ℝ} {f g: ℝ → ℝ}
  (hdf: ∀ x ∈ set.Ioo a b, differentiable_at ℝ f x)
  (hg': ∀ x ∈ set.Ioo a b, deriv g x ≠ 0)
  (hcf: continuous_on f (set.Icc a b))
  (hcg: continuous_on g (set.Icc a b))
  (hftop: filter.tendsto f (𝓝[set.Ioi a] a) at_top)
  (hgtop: filter.tendsto g (𝓝[set.Ioi a] a) at_top)
  (hdiv: filter.tendsto (λ (x: ℝ), deriv f x / deriv g x) (𝓝[set.Ioi a] a) (𝓝 l)):
  filter.tendsto (λ (x: ℝ), f x / g x) (𝓝[set.Ioi a] l) (𝓝 l) :=
  begin
    have cmvt : ∀ (a' b': ℝ), a ≤ a' → b' ≤ b → a' < b' → ∃ (c: ℝ) (H: c ∈ set.Ioo a' b'), (deriv f c) / (deriv g c) = (f b' - f a') / (g b' - g a'),
    {
      intros a' b' haa' hb'b hab',
      have hdg' : differentiable_on ℝ g (set.Ioo a' b') := λ y hy, 
      differentiable_at.differentiable_within_at 
      (not_not.1 (mt deriv_zero_of_not_differentiable_at (hg' _ ⟨ lt_of_le_of_lt haa' hy.1, lt_of_lt_of_le hy.2 hb'b ⟩))),
      convert 
        exists_ratio_deriv_eq_ratio_slope f hab' 
        (hcf.mono (λ z (hz: z ∈ set.Icc a' b'), ⟨ le_trans haa' hz.1, le_trans hz.2 hb'b ⟩))
        (λ y hy, differentiable_at.differentiable_within_at 
          (hdf _ ⟨ lt_of_le_of_lt haa' hy.1, lt_of_lt_of_le hy.2 hb'b ⟩))
        g 
        (hcg.mono (λ z (hz: z ∈ set.Icc a' b'), ⟨ le_trans haa' hz.1, le_trans hz.2 hb'b ⟩))
        hdg',
      ext,
      simp only [and_imp, exists_prop, and.congr_right_iff],
      intros hx_mem,
      -- g' nonzero, therefore g monotone, therefore g a < g b, therefore g b - g a ≠ 0
      have fact₀ : g b' - g a' ≠ 0, from sorry,
      have fact₁ : deriv g x ≠ 0, from hg' _ ⟨ lt_of_le_of_lt haa' hx_mem.1, lt_of_lt_of_le hx_mem.2 hb'b ⟩,
      field_simp [fact₀, fact₁, mul_comm _ (g b' - g a')],
    },
    sorry,
  end

lemma deriv.lhopital_inf_at_top {l: ℝ} {f g: ℝ → ℝ}
  (hdf: ∀ᶠ (x: ℝ) in filter.at_top, differentiable_at ℝ f x)
  (hg': ∀ᶠ (x: ℝ) in filter.at_top, deriv g x ≠ 0)
  (hftop: filter.tendsto f filter.at_top filter.at_top)
  (hgtop: filter.tendsto g filter.at_top filter.at_top)
  (hdiv: filter.tendsto (λ (x: ℝ), deriv f x / deriv g x) filter.at_top (nhds l)):
  filter.tendsto (λ (x: ℝ), f x / g x) filter.at_top (nhds l) :=
begin
  have hdf' : ∀ᶠ (x: ℝ) in (𝓝[set.Ioi 0] 0), differentiable_at ℝ (λ (x: ℝ), f (1 / x)) x, from sorry,
  have hg'' : ∀ᶠ (x: ℝ) in (𝓝[set.Ioi 0] 0), deriv (λ (y: ℝ), g (1 / y)) x ≠ 0, from sorry,
  have hfzero : tendsto (λ (x: ℝ), f (1 / x)) (𝓝[set.Ioi 0] 0) at_top,
  by simp [hftop.comp tendsto_inv_zero_at_top],
  have hgzero : tendsto (λ (x: ℝ), g (1 / x)) (𝓝[set.Ioi 0] 0) at_top,
  by simp [hgtop.comp tendsto_inv_zero_at_top],
  convert (deriv.lhopital_at_top_nhds_right_on_Ioo hdf' hg''
  hfzero hgzero _).comp tendsto_inv_at_top_zero',
  ext, field_simp, ring,
  convert (tendsto_congr' _).1 (hdiv.comp tendsto_inv_zero_at_top),
  rw [eventually_eq_nhds_within_iff, eventually_iff_exists_mem],
  use (set.Ioi (-1)),
  split,
  exact Ioi_mem_nhds (by norm_num),
  intros y _ hy,
  have h : y ≠ 0, from ne_of_gt (set.mem_Ioi.1 hy),
  field_simp,
  conv {
    to_rhs,
    simp [one_div],
  },
  rw [deriv.comp_inv h, deriv.comp_inv h],
  rw [div_div_div_cancel_right, neg_div_neg_eq],
  simp [h],
  sorry,
  sorry,
end

lemma eventually_eq.of_le_ite_at_top {α β: Type*} [preorder α] {f g: α → β} {a: α} {c: β} [decidable_rel ((≤) : α → α → Prop)]:
  filter.eventually_eq filter.at_top (λ (x: α), if (x ≤ a) then c else (f x)) g := sorry

lemma eventually.eq_of_eq_ite_at_top {α β: Type*} [preorder α] [no_top_order α] {f g: α → β} {a: α} {c: β} [decidable_eq α]:
  (λ (x: α), if (x = a) then c else (f x)) = g → filter.eventually_eq filter.at_top f g :=
begin
  intro hext,
  suffices: set.eq_on f g (set.Ioi a),
  from filter.eventually_eq_of_mem (filter.Ioi_mem_at_top a) this,
  rw ← hext,
  intros x hmem,
  simp [if_neg (ne_of_gt hmem)],
end

lemma deriv.log_1_plus_x: deriv (λ (x: ℝ), real.log (1 + x)) = λ (x: ℝ), if x = -1 then 0 else (1 / (1 + x)) :=
begin
  ext,
  by_cases (x = -1),
  {
    rw [if_pos h],
    have := (mt real.differentiable_at_log_iff.1) (not_not.2 ((add_eq_zero_iff_eq_neg.2) h)),
    rw [add_comm _ _] at this,
    apply deriv_zero_of_not_differentiable_at,
    -- have notdiff := (mt (differentiable_at.comp x)),
    -- rw [not_imp] at notdiff,
    sorry,
  },
  {
    rw [if_neg h],
    convert deriv.log _ _,
    repeat { simp [add_comm 1 x, (mt add_eq_zero_iff_eq_neg.1) h] },
  },
end

lemma deriv.log_1_plus_x_eventually_at_top: 
  filter.eventually_eq filter.at_top 
  (deriv (λ (x: ℝ), real.log (1 + x))) (λ (x: ℝ), 1 / (1 + x)) :=
(eventually.eq_of_eq_ite_at_top (deriv.log_1_plus_x.symm)).symm

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
