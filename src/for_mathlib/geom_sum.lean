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

-- can be generalized.
lemma geom_sum_eq_factor_inv_geom_sum
  (x: ℝ) (n: ℕ):
  geom_series x n = (x ^ (n - 1)) * geom_series (x⁻¹) n :=
begin
  rw ← geom_sum_of_sum_of_range_map,
  rw ← geom_sum_of_sum_of_range_map,
  sorry,
end