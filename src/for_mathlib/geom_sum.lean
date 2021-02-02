import .list
import algebra.geom_sum
import analysis.specific_limits

lemma geom_sum_of_sum_of_range_map {α} [semiring α] (x: α) (n: ℕ):
  list.sum (list.map (pow x) (list.range n)) = geom_series x n :=
begin
  induction n with d hd,
  { simp only [list.sum_nil, geom_series_zero, list.range_zero, list.map] },
  { simp [geom_series, finset.range, list.range_succ, add_comm, hd] },
end

lemma geom_sum_of_sum_of_map_with_index {α} [semiring α] (x: α) (l: list α):
  list.sum (l.map_with_index (λ i a, x ^ i)) = geom_series x (l.length) :=
by simp [← geom_sum_of_sum_of_range_map x (l.length), list.map_with_index_eq_range_map (λ i a, x ^ i) (λ i, x ^ i)]

lemma real.finite_geom_sum_le_infinite_geom_sum_of_abs_lt_1
  (x: ℝ) (n: ℕ) (x_nonneg: 0 ≤ x) (h: abs x < 1):
  geom_series x n ≤ ∑' k: ℕ, x ^ k :=
begin
  apply sum_le_tsum,
  simp,
  intros m hm,
  exact pow_nonneg x_nonneg m,
  exact summable_geometric_of_abs_lt_1 h,
end

lemma real.finite_geom_sum_le_infinite_geom_sum_of_lt_1
  {x: ℝ} (n: ℕ) (x_nonneg: 0 ≤ x) (h: x < 1):
  geom_series x n ≤ ∑' k: ℕ, x ^ k :=
begin
  sorry,
end

-- can be generalized to 'semifield', but we do not have them.
lemma geom_sum_eq_factor_inv_geom_sum
  {α} [field α]
  {x: α} (n: ℕ) (hx_ne_0: x ≠ 0) (hx_ne_1: x ≠ 1):
  geom_series x (n + 1) = (x ^ n) * geom_series (x⁻¹) (n + 1) :=
begin
  rw [geom_sum hx_ne_1, geom_sum_inv hx_ne_1 hx_ne_0],
  rw [← mul_assoc, div_eq_mul_inv],
  exact calc (x ^ (n + 1) - 1) * (x - 1)⁻¹ = (x - 1)⁻¹ * (x ^ (n + 1) - 1) : mul_comm _ _
  ... = (x - 1)⁻¹ * (x ^ n * x - 1) : by rw pow_succ' x n
  ... = (x - 1)⁻¹ * (x ^ n * x - x ^ (-n: ℤ) * x ^ n) : by erw [fpow_neg_mul_fpow_self n hx_ne_0]
  ... = (x - 1)⁻¹ * (x ^ n * x - x ^ n * x ^ (-n: ℤ)) : by ring
  ... = (x - 1)⁻¹ * x ^ n * (x - x⁻¹ ^ n) : by rw [← mul_sub_left_distrib _ _ _, ← mul_assoc, ← inv_fpow', fpow_coe_nat]
  ... = (x - 1)⁻¹ * x ^ n * (x - x⁻¹ ^ n * 1) : by rw mul_one (x⁻¹ ^ n)
  ... = (x - 1)⁻¹ * x ^ n * (x - x⁻¹ ^ n * (x⁻¹ * x)) : by rw inv_mul_cancel hx_ne_0
  ... = (x - 1)⁻¹ * x ^ n * (x - x⁻¹ ^ (n + 1) * x)  : by rw [← mul_assoc, pow_succ' x⁻¹ n]
  ... = x ^ n * (x - 1)⁻¹ * (x - x⁻¹ ^ (n + 1) * x) : by ac_refl,
end