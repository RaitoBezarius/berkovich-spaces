import data.nat.enat
import data.real.basic
import data.real.cau_seq
import data.nat.choose.basic
import algebra.group_power.basic
import ring_theory.ideal.basic
import ring_theory.principal_ideal_domain
import ring_theory.unique_factorization_domain
import analysis.special_functions.pow
import topology.basic

import for_mathlib.associated
import for_mathlib.multiplicity
import for_mathlib.principal_ideal_domain

open is_absolute_value
open_locale classical big_operators
noncomputable theory

set_option old_structure_cmd true

def padic_val {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (p: α) (p_prime: prime p) (a: α): ℕ :=
  if a ≠ 0
      then multiset.count (normalize p) (unique_factorization_monoid.factors a)
      else 0

lemma padic_val_mul {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (p: α) (p_prime: prime p) (a b: α) (ha: a ≠ 0) (hb: b ≠ 0):
  padic_val p p_prime (a * b) = padic_val p p_prime a + padic_val p p_prime b :=
begin
  unfold padic_val,
  simp [ha, hb],
end

lemma padic_val_add {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (p: α) (p_prime: prime p) {a b: α} (add_ne_zero: a + b ≠ 0):
    padic_val p p_prime (a + b) ≥ min (padic_val p p_prime a) (padic_val p p_prime b) :=
begin
  unfold padic_val,
  exact if ha: a = 0
    then by { simp [ha], }
    else if hb: b = 0
    then by { simp [hb], }
    else by {
      have h: multiplicity p (a + b) ≥ min (multiplicity p a) (multiplicity p b),
      from multiplicity.min_le_multiplicity_add,
      have p₀ := λ a: α, λ p: a ≠ 0,
        unique_factorization_monoid.multiplicity_eq_count_factors
          (irreducible_of_prime p_prime) p,
      rw p₀ _ add_ne_zero at h,
      rw p₀ _ ha at h,
      rw p₀ _ hb at h,
      finish,
    },
end

lemma padic_val_primes {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (p: α) (p_prime: prime p): ∀ q: α, prime q →
    padic_val p p_prime q = if associated q p then 1 else 0 :=
begin
  intros q q_prime,
  unfold padic_val,
  simp only [q_prime.left, if_true, if_false, ne.def, not_false_iff],
  rw ← enat.coe_inj,
  rw eq.symm (unique_factorization_monoid.multiplicity_eq_count_factors
    (irreducible_of_prime p_prime) q_prime.1),
  exact if hpq: associated q p
    then by simp [hpq, multiplicity.eq_of_associated hpq,
      multiplicity.multiplicity_self p_prime.not_unit p_prime.ne_zero]
    else by simp [hpq, multiplicity.multiplicity_eq_zero_of_not_dvd
      (λ h, hpq (primes_associated_of_dvd p_prime q_prime h).symm)]
end

lemma padic_val_units {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (p: α) (p_prime: prime p): ∀ u: units α, padic_val p p_prime u = 0 :=
begin
  intro u,
  unfold padic_val,
  simp only [u.ne_zero, if_true, ne.def, not_false_iff],
  rw ← enat.coe_inj,
  rw eq.symm (unique_factorization_monoid.multiplicity_eq_count_factors
    (irreducible_of_prime p_prime) u.ne_zero),
  exact multiplicity.unit_right p_prime.not_unit u,
end

def padic_abv {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (base: ℝ) (base_pos: 0 < base) (base_lt_one: base < 1)
    (p: α) (p_prime: prime p): α → ℝ :=
  λ a: α, if a = 0 then 0 else base ^ padic_val p p_prime a

instance padic_abv_is_absolute_value {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (base: ℝ) (base_pos: 0 < base) (base_lt_one: base < 1)
  (p: α) (p_prime: prime p) :
    is_absolute_value (padic_abv base base_pos base_lt_one p p_prime) :=
{
  abv_nonneg := by {
    intro a, unfold padic_abv, split_ifs, refl,
    apply pow_nonneg, exact le_of_lt base_pos,
  },
  abv_eq_zero := by {
    intro a, unfold padic_abv, split_ifs, tauto,
    finish [pow_ne_zero (padic_val p p_prime a) (ne.symm $ ne_of_lt base_pos)],
  },
  abv_add := by {
    intros x y,
    unfold padic_abv,
    have pow_x_pos := pow_pos base_pos (padic_val p p_prime x),
    have pow_y_pos := pow_pos base_pos (padic_val p p_prime y),
    exact if hx: x = 0 then
        by { simp [hx], }
      else if hy: y = 0 then
        by { simp [hy], }
      else if hxy: x + y = 0 then
        by {
          simp [hx, hy, hxy],
          linarith only [pow_x_pos, pow_y_pos],
        }
      else by {
        suffices p₁: real.rpow base (padic_val p p_prime (x + y)) ≤
          max
            (real.rpow base (padic_val p p_prime x))
            (real.rpow base (padic_val p p_prime y)),
        {
          have p₂ := max_le_add_of_nonneg (le_of_lt pow_x_pos) (le_of_lt pow_y_pos),
          repeat { rw [real.rpow_eq_pow, real.rpow_nat_cast] at p₁, },
          simp [hx, hy, hxy, le_trans p₁ p₂],
        },

        set c := base⁻¹ with c_def,
        obtain ⟨ one_lt_c, base_rw, c_nonneg ⟩: 1 < c ∧ base = c⁻¹ ∧ 0 ≤ c,
        {
          rw c_def,
          rw inv_inv',
          exact ⟨ one_lt_inv base_pos base_lt_one, rfl,
            inv_nonneg.2 $ le_of_lt base_pos ⟩,
        },
        have pow_c_mono: monotone (pow c),
        from λ a b h, real.rpow_le_rpow_of_exponent_le (le_of_lt one_lt_c) h,
        
        have p₀ := (int.neg_le_neg $ int.coe_nat_le.2 $ padic_val_add p p_prime hxy),
        
        repeat { rw base_rw, },
        repeat { rw real.rpow_eq_pow, },
        repeat { rw real.inv_rpow c_nonneg, },
        repeat { rw ← real.rpow_neg c_nonneg, },
        rw ← monotone.map_max pow_c_mono,
        rw ← ge_iff_le at p₀,
        rw max_neg_neg,
        rw ← monotone.map_min,
        {
          apply pow_c_mono,
          exact_mod_cast p₀,
        },
        exact nat.mono_cast,
      },
  },
  abv_mul := by {
    intros x y,
    unfold padic_abv,
    exact if hx: x = 0 then
      by simp [hx]
    else if hy: y = 0 then
      by simp [hy]
    else by { simp [hx, hy, padic_val_mul p p_prime x y, pow_add _ _ _], },
  },
}

lemma padic_abv_primes {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (base: ℝ) (base_pos: 0 < base) (base_lt_one: base < 1)
    (p: α) (p_prime: prime p):
      ∀ q: α, prime q →
      padic_abv base base_pos base_lt_one p p_prime q =
        if associated q p then base else 1 :=
begin
  intros q q_prime,
  unfold padic_abv,
  rw padic_val_primes p p_prime q q_prime,
  simp [q_prime.1],
end

lemma padic_abv_bounded {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (base: ℝ) (base_pos: 0 < base) (base_lt_one: base < 1)
    (p: α) (p_prime: prime p):
      ∀ a: α, padic_abv base base_pos base_lt_one p p_prime a ≤ 1 :=
begin
  set abv := (padic_abv base base_pos base_lt_one p p_prime) with abv_def,
  
  intro a,
  refine wf_dvd_monoid.induction_on_irreducible a ((abv_zero abv).symm ▸ zero_le_one) _ _,
  {
    rintros _ ⟨ u, rfl ⟩,
    rw abv_def,
    unfold padic_abv,
    simp [padic_val_units p p_prime u],
  },
  {
    intros a q ha hq abva_le_one,
    rw abv_mul abv,
    convert mul_le_mul _ abva_le_one (abv_nonneg abv a) (zero_le_one),
    rw one_mul,
    rw principal_ideal_ring.irreducible_iff_prime at hq,
    rw [abv_def, padic_abv_primes base base_pos base_lt_one p p_prime q hq],
    by_cases hpq: associated q p; simp [hpq, if_true, le_of_lt base_lt_one],
  },
end

def sample_padic_abv {α} [integral_domain α] [is_principal_ideal_ring α]
  [normalization_monoid α]
  (p: α) (p_prime: prime p): α → ℝ :=
    padic_abv (1/2) one_half_pos one_half_lt_one p p_prime

instance sample_padic_abv_is_absolute_value {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (p: α) (p_prime: prime p): is_absolute_value (sample_padic_abv p p_prime) :=
  padic_abv_is_absolute_value (1/2) one_half_pos one_half_lt_one p p_prime

lemma sample_padic_abv_on_primes {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α] (p: α) (p_prime: prime p):
      ∀ q: α, prime q →
      sample_padic_abv p p_prime q = if associated q p then 1/2 else 1 :=
padic_abv_primes (1/2) one_half_pos one_half_lt_one p p_prime

lemma sample_padic_abv_bounded {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α] (p: α) (p_prime: prime p):
      ∀ a: α, sample_padic_abv p p_prime a ≤ 1 :=
padic_abv_bounded (1/2) one_half_pos one_half_lt_one p p_prime

def hom_of_abv {α} [linear_ordered_field α] {β} [ring β] [nontrivial β]
  (abv: β → α) [is_absolute_value abv]:
  monoid_with_zero_hom β α :=
{
  to_fun := abv,
  map_zero' := abv_zero abv,
  map_one' := abv_one abv,
  map_mul' := abv_mul abv,
}

def hom_of_equiv {α} [comm_ring α]
  (φ: monoid_with_zero_hom α ℝ) (a: ℝ) (a_pos: 0 < a)
  (nonneg: ∀ a: α, 0 ≤ φ a):
  monoid_with_zero_hom α ℝ :=
{
  to_fun := (λ r, (φ r) ^ a),
  map_zero' := by {
    rw [← monoid_with_zero_hom.to_fun_eq_coe, φ.map_zero'],
    exact real.zero_rpow (ne.symm $ ne_of_lt a_pos),
  },
  map_one' := by {
    rw [← monoid_with_zero_hom.to_fun_eq_coe, φ.map_one'],
    exact real.one_rpow a,
  },
  map_mul' := by {
    intros x y,
    rw [← monoid_with_zero_hom.to_fun_eq_coe, φ.map_mul'],
    have p: ∀ a: α, 0 ≤ φ.to_fun a := nonneg,
    rw real.mul_rpow (p x) (p y),
  },
}
