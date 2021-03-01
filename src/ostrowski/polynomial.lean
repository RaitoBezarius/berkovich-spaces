import data.real.basic
import data.polynomial.basic
import data.polynomial.induction
import data.real.cau_seq

import abvs_equiv
import valuations.basic
import valuations.abv_pid
import valuations.bounded

import for_mathlib.degree

open is_absolute_value
open_locale classical
noncomputable theory

def degree_norm {R} [field R] (c: ℝ) (one_lt_c: 1 < c): polynomial R → ℝ :=
  λ p, if p = 0 then 0 else c ^ p.nat_degree

instance degree_norm.is_absolute_value {R} [field R] (c: ℝ) (one_lt_c: 1 < c):
  is_absolute_value (@degree_norm R _ c one_lt_c) :=
begin
  have c_pos := (lt_trans zero_lt_one one_lt_c),
  exact { abv_nonneg := λ p, if h: p = 0
      then by simp [degree_norm, h, int.zero_nonneg.le]
      else by simp [degree_norm, h, pow_nonneg (le_of_lt c_pos) p.nat_degree],
    abv_eq_zero := λ p, if h: p = 0
      then by simp [degree_norm, h]
      else by { simp [degree_norm, h], exact (ne.symm $ ne_of_lt $ pow_pos c_pos _), },
    abv_add := λ p q, if hp: p = 0
      then by { simp [degree_norm, hp], }
      else if hq: q = 0
      then by { simp [degree_norm, hq], }
      else if hpq: p + q = 0
      then by {
        simp [degree_norm, hpq, hp, hq],
        exact (λ p₁: (Π (n: ℕ), 0 ≤ c ^ n),
            add_nonneg (p₁ p.nat_degree) (p₁ q.nat_degree))
          (pow_nonneg $ le_of_lt c_pos),
      }
      else by {
        simp [degree_norm, hpq, hp, hq],
        cases le_max_iff.1 (polynomial.degree_add_le p q) with h₀ h₀;
        have h := polynomial.nat_degree_le_nat_degree h₀;
        apply le_trans (pow_le_pow (le_of_lt one_lt_c) h);
        linarith [pow_nonneg (le_of_lt c_pos) p.nat_degree,
          pow_nonneg (le_of_lt c_pos) q.nat_degree],
      },
    abv_mul := λ p q, if hp: p = 0
      then by { simp [degree_norm, hp], }
      else if hq: q = 0
      then by { simp [degree_norm, hq], }
      else by {
        simp [degree_norm, hp, hq],
        have hpq: p * q ≠ 0,
        {
          by_contra hpq,
          push_neg at hpq,
          cases eq_zero_or_eq_zero_of_mul_eq_zero hpq,
          exact hp h, exact hq h,
        },
        have := (@polynomial.degree_mul _ _ p q),
        rw polynomial.degree_eq_nat_degree hp at this,
        rw polynomial.degree_eq_nat_degree hq at this,
        rw polynomial.degree_eq_nat_degree hpq at this,
        norm_cast at this,
        rw this,
        rw pow_add,
      }, },
end

def sample_degree_norm {R} [field R]: polynomial R → ℝ := degree_norm 2 one_lt_two

instance sample_degree_norm.is_absolute_value {R} [hR: field R]:
  is_absolute_value (@sample_degree_norm R hR) :=
    degree_norm.is_absolute_value 2 one_lt_two

lemma polynomial_abv_nonarchimedian {R} [field R] [normalization_monoid R]
  (abv: polynomial R → ℝ) [is_absolute_value abv]
  (trivial_on_base: ∀ x: R, x ≠ 0 → abv (polynomial.C x) = 1):
    ∀ a b: polynomial R, abv (a + b) ≤ max (abv a) (abv b) :=
begin
  have bounded_on_base: ∀ a: R, abv (polynomial.C a) ≤ 1,
    from λ p, if hp: p = 0
      then by simp [hp, abv_zero abv, zero_le_one]
      else (le_of_eq $ trivial_on_base p hp),
  rw ← nonarchimedian_iff_integers_bounded,
  use [1, zero_lt_one],
  intro n,
  rw show (n: polynomial R) = (polynomial.C (n: R)), by simp,
  exact bounded_on_base n,
end

theorem polynomial_abv_is_degree {R} [field R] [normalization_monoid R]
  (abv: polynomial R → ℝ) [is_absolute_value abv]
  (one_lt_abvx: 1 < abv polynomial.X)
  (trivial_on_base: ∀ x: R, x ≠ 0 → abv (polynomial.C x) = 1):
    abvs_equiv abv sample_degree_norm :=
begin
  have nonarchimedian := polynomial_abv_nonarchimedian abv trivial_on_base,
  
  have abv_sum_of_abv_ne: ∀ p q: polynomial R, abv p < abv q → abv (p + q) = abv q,
  {
    intros a b hab,
    apply le_antisymm,
    calc abv (a + b) ≤ max (abv a) (abv b) : by sorry
      ... = abv b : max_eq_right (le_of_lt hab),
    have: abv b ≤ abv (a + b),
    calc abv b = abv (-a + (a + b)) : by ring
      ... ≤ max (abv (-a)) (abv (a + b)) : by sorry
      ... = max (abv a) (abv (a + b)) : by rw abv_neg abv
      ... = abv (a + b) : by sorry,
    exact this,
  },

  suffices: abvs_equiv abv (degree_norm (abv polynomial.X) one_lt_abvx),
  {
    apply abvs_equiv_transitive
      abv (degree_norm (abv polynomial.X) one_lt_abvx) sample_degree_norm this,
    set α := real.log 2 / real.log (abv polynomial.X) with α_def,
    have α_pos: 0 < α,
    from div_pos (real.log_pos one_lt_two) (real.log_pos one_lt_abvx),
    use [α, α_pos],
    unfold sample_degree_norm,
    unfold degree_norm,
    ext p,
    by_cases hp: p = 0,
    simp [hp, abv_zero abv, real.zero_rpow (ne_of_lt α_pos).symm],
    suffices: ((abv polynomial.X) ^ (p.nat_degree: ℝ)) ^ α = 2 ^ (p.nat_degree: ℝ),
    {
      simp [hp],
      rw ← real.rpow_nat_cast _ p.nat_degree,
      rw ← real.rpow_nat_cast _ p.nat_degree,
      exact this,
    },
    rw ← real.rpow_mul (le_of_lt $ lt_trans zero_lt_one one_lt_abvx),
    apply log_inj_pos
      (real.rpow_pos_of_pos (lt_trans zero_lt_one one_lt_abvx) _)
      (real.rpow_pos_of_pos zero_lt_two _),
    rw real.log_rpow (lt_trans zero_lt_one one_lt_abvx),
    rw real.log_rpow zero_lt_two,
    rw α_def,
    calc (p.nat_degree: ℝ) * (real.log 2 / real.log (abv polynomial.X))
      * real.log (abv polynomial.X)
      = (p.nat_degree: ℝ) * real.log 2 *
        (real.log (abv polynomial.X) / real.log (abv polynomial.X)) : by ring
      ... = (p.nat_degree: ℝ) * real.log 2 : by rw [div_self
        (real.log_ne_zero_of_ne_one _ (lt_trans zero_lt_one one_lt_abvx)
        (ne_of_lt one_lt_abvx).symm), mul_one],
  },

  use [1, zero_lt_one],
  simp [degree_norm],
  ext p,
  by_cases hp: p = 0,
  simp [hp, abv_zero abv],
  have: abv p = (abv polynomial.X) ^ p.nat_degree,
  {
    -- use polynomial.as_sum_range ?
    sorry
  },
  simp [this, hp],
end

theorem polynomial_abv_is_padic {R} [field R] [normalization_monoid R]
  (abv: polynomial R → ℝ) [is_absolute_value abv]
  (nontrivial: abv ≠ (λ x, if x = 0 then 0 else 1))
  (abvx_le_one: abv polynomial.X ≤ 1)
  (trivial_on_base: ∀ x: R, x ≠ 0 → abv (polynomial.C x) = 1):
    ∃ (p: polynomial R) (p_prime: prime p), abvs_equiv abv (sample_padic_abv p p_prime) :=
begin
  apply abv_bounded_padic abv,
  {
    have nonarchimedian := polynomial_abv_nonarchimedian abv trivial_on_base,
    have bounded_on_base: ∀ a: R, abv (polynomial.C a) ≤ 1,
      from λ p, if hp: p = 0
        then by simp [hp, abv_zero abv, zero_le_one]
        else (le_of_eq $ trivial_on_base p hp),
    intro p,
    apply polynomial.induction_on p,
    from bounded_on_base,
    from λ p q hp hq,
      by { calc abv (p + q) ≤ max (abv p) (abv q) : nonarchimedian p q
        ... ≤ 1 : max_le_iff.2 ⟨ hp, hq ⟩, },
    from λ n a h, by {
      rw pow_succ,
      rw mul_comm (polynomial.X) _,
      rw ← mul_assoc,
      rw abv_mul abv,
      convert mul_le_mul h abvx_le_one (abv_nonneg abv polynomial.X) zero_le_one,
      rw mul_one,
    },
  },
  {
    by_contra h,
    push_neg at h,
    apply nontrivial,
    ext,
    exact if hx: x = 0
      then by { simp [hx, abv_zero abv], }
      else by { simp [hx, h x hx], },
  },
end
