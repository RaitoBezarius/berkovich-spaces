import data.polynomial.basic
import data.polynomial.degree.definitions

lemma polynomial.nat_degree_eq_nat_degree {R} [semiring R] {p q: polynomial R}
  (hpq: p.degree = q.degree): p.nat_degree = q.nat_degree :=
begin
  apply le_antisymm,
  exact polynomial.nat_degree_le_nat_degree (le_of_eq hpq),
  exact polynomial.nat_degree_le_nat_degree (le_of_eq hpq.symm),
end

theorem with_bot.lt_iff_exists_coe {α} [partial_order α]: ∀ {a b: with_bot α}, a < b ↔ (∃ p : α, b = p ∧ a < ↑p)
| a (some b) := by simp [with_bot.some_eq_coe, with_bot.coe_eq_coe]
| a none := by simp [with_bot.none_eq_bot]; exact (λ x hx, hx ▸ (@not_lt_bot _ _ a))

lemma polynomial.zero_le_nat_degree {R} [semiring R] {p: polynomial R}
  (hne: p ≠ 0): 0 ≤ p.nat_degree :=
begin
  have := (mt polynomial.degree_eq_bot.1) hne,
  obtain ⟨ n, ⟨ hdeg, hbot ⟩ ⟩ := with_bot.lt_iff_exists_coe.1 (bot_lt_iff_ne_bot.2 this),
  rw polynomial.nat_degree_eq_of_degree_eq_some hdeg,
  have := polynomial.zero_le_degree_iff.2 hne,
  rw hdeg at this,
  exact_mod_cast this,
end

lemma polynomial.nat_degree_add_C {R} [semiring R] {a: R} {p: polynomial R}: 
  (p.nat_degree = 0 → p + polynomial.C a ≠ 0)  → (p + polynomial.C a).nat_degree = p.nat_degree :=
begin
  intro h_cancel,
  apply (polynomial.degree_eq_iff_nat_degree_eq _).1,
  rotate 1,
  {
    by_cases (p.nat_degree = 0),
    exact h_cancel h,
    have h_deg := (nat.eq_zero_or_pos _).resolve_left h,
    suffices : 0 ≤ (p + polynomial.C a).degree, from polynomial.ne_zero_of_coe_le_degree this,
    rw polynomial.degree_add_eq_left_of_degree_lt,
    exact le_of_lt (polynomial.nat_degree_pos_iff_degree_pos.1 h_deg),
    calc (polynomial.C a).degree ≤ 0 : polynomial.degree_C_le
    ... < p.degree : polynomial.nat_degree_pos_iff_degree_pos.1 h_deg,
  },
  by_cases (0 < p.nat_degree),
  {
    rw polynomial.degree_add_C (polynomial.nat_degree_pos_iff_degree_pos.1 h),
    exact polynomial.degree_eq_nat_degree (polynomial.ne_zero_of_nat_degree_gt h),
  },
  {
    replace h := nonpos_iff_eq_zero.1 (not_lt.1 h),
    rw polynomial.eq_C_of_nat_degree_eq_zero h,
    by_cases ha_zero : a = 0,
    {
      rw ha_zero at *,
      simp only [add_zero, ring_hom.map_zero, polynomial.nat_degree_C, with_top.coe_zero],
      simp only [add_zero, ring_hom.map_zero, ne.def] at h_cancel,
      rw ← polynomial.eq_C_of_nat_degree_eq_zero h,
      rw_mod_cast [polynomial.degree_eq_nat_degree (h_cancel h), h],
    },
    {
      replace h_cancel := h_cancel h,
      by_cases hp_zero: p.coeff 0 = 0,
      {
        simp [hp_zero, le_antisymm 
        (polynomial.degree_C_le)
        (polynomial.zero_le_degree_iff.2 ((not_iff_not_of_iff polynomial.C_eq_zero).2 ha_zero))],
      },
      {
        rw [polynomial.degree_add_eq_of_leading_coeff_add_ne_zero],
        rw_mod_cast [← polynomial.eq_C_of_nat_degree_eq_zero h, polynomial.degree_eq_nat_degree, 
        h, polynomial.degree_C ha_zero],
        exact max_self _,
        {
          rw [polynomial.eq_C_of_nat_degree_eq_zero h],
          simp [hp_zero],
        },
        {
          rw [polynomial.eq_C_of_nat_degree_eq_zero h, ← polynomial.C_add, ne.def, polynomial.C_eq_zero] at h_cancel,
          simp [h_cancel],
        },
      }
    }
  },
end