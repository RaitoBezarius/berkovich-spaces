import .list
import algebra.geom_sum
import analysis.specific_limits

lemma geom_sum_of_sum_of_range_map {α} [semiring α] (x: α) (n: ℕ):
  list.sum (list.map (λ i, x ^ i) (list.range n)) = geom_series x n := sorry

lemma geom_sum_of_sum_of_map_with_index {α} [semiring α] (x: α) (l: list α):
  list.sum (l.map_with_index (λ i a, x ^ i)) = geom_series x (l.length) :=
by simp [← geom_sum_of_sum_of_range_map x (l.length), list.map_with_index_eq_range_map (λ i a, x ^ i) (λ i, x ^ i)]

lemma real.finite_geom_sum_le_infinite_geom_sum 
  (x: ℝ) (n: ℕ) (h: abs x < 1):
  geom_series x n ≤ ∑' k: ℕ, x ^ k := sorry

-- can be generalized.
lemma geom_sum_eq_factor_inv_geom_sum
  (x: ℝ) (n: ℕ):
  geom_series x n = (x ^ n) * geom_series (x⁻¹) n :=
begin
  rw ← geom_sum_of_sum_of_range_map,
  rw ← geom_sum_of_sum_of_range_map,
  sorry,
end