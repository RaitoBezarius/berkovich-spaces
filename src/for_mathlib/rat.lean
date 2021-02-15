import data.rat.basic
import data.real.basic
import algebra.group_with_zero.basic
import algebra.group.hom

import for_mathlib.hom

-- From Alex J. Best (?)
lemma rat_mk_eq_div (x_num : ℤ) (x_denom : ℕ) (x_pos : 0 < x_denom) (x_cop : nat.coprime (int.nat_abs x_num) x_denom)
: ({num := x_num, denom := x_denom, pos := x_pos, cop := x_cop}:ℚ) = (↑ x_num)/(↑ x_denom) := begin
  norm_cast,
  rw rat.mk,
  rw rat.mk_nat,
  rw dif_neg,
  rw rat.mk_pnat,
  {
    simp [x_cop.gcd_eq_one],
  },
  exact ne_of_gt x_pos,
end

-- Integer values of a morphism `φ` and its value on `-1` completely determines `φ`
theorem ext_hom_pnat (φ₁ φ₂: monoid_with_zero_hom ℚ ℝ)
  (same_on_neg_one: φ₁ (-1) = φ₂ (-1)) (same_on_nat: ∀ n: ℕ, φ₁ n = φ₂ n): (φ₁: ℚ → ℝ) = φ₂ :=
begin
  ext,
  suffices : ∀ z : ℤ, φ₁ z = φ₂ z,
  begin
    induction x,
    rw rat_mk_eq_div,
    repeat { rw div_eq_mul_inv, },
    have x_denom_ne_zero: (x_denom: ℚ) ≠ 0,
    {
      symmetry,
      norm_cast,
      exact (ne_of_lt x_pos),
    },
    rw monoid_with_zero_hom.map_mul φ₁,
    rw monoid_with_zero_hom.map_inv φ₁ x_denom x_denom_ne_zero,
    rw monoid_with_zero_hom.map_mul φ₂,
    rw monoid_with_zero_hom.map_inv φ₂ x_denom x_denom_ne_zero,
    rw this x_num,
    have := this (↑ x_denom),
    norm_cast at this,
    rw this,
  end,
  intro x,
  suffices : ∀ z : ℕ, φ₁ z = φ₂ z,
  begin
    induction x,
    simp [this],
    push_cast,
    conv {
      congr,
      rw neg_eq_neg_one_mul,
      skip,
      rw neg_eq_neg_one_mul,
      skip,
    },
    rw monoid_with_zero_hom.map_mul φ₁,
    rw monoid_with_zero_hom.map_mul φ₂,
    rw same_on_neg_one,
    simp,
    norm_cast,
    exact this _,
  end,
  intro x,
  cases x,
  simp,
  have := same_on_nat (nat.succ x_1),
  simp [-add_comm] at this,
  simp [-add_comm],
  rw this,
end
