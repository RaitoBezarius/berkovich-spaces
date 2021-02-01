import data.nat.digits
import .list

lemma of_digits_eq_sum_map_with_index_aux (b : ℕ) (l : list ℕ) :
  (list.zip_with ((λ (i a : ℕ), a * b ^ i) ∘ nat.succ) (list.range l.length) l).sum =
  b * (list.zip_with (λ i a, a * b ^ i) (list.range l.length) l).sum :=
begin
  suffices : list.zip_with (((λ (i a : ℕ), a * b ^ i) ∘ nat.succ)) (list.range l.length) l =
      list.zip_with (λ i a, b * (a * b ^ i)) (list.range l.length) l,
    { simp [this] },
  congr,
  ext,
  simp [pow_succ],
  ring
end

lemma of_digits_eq_sum_map_with_index (b: ℕ) (L: list ℕ):
  nat.of_digits b L = list.sum (L.map_with_index (λ (i: ℕ) (a: ℕ), a * b ^ i)) :=
begin
  rw [list.map_with_index_eq_enum_map_uncurry, list.enum_eq_zip_range,
    list.map_uncurry_zip_eq_zip_with, nat.of_digits_eq_foldr b],
  induction L with hd tl hl,
    { simp },
    { 
      norm_cast at hl,
      simp [list.range_succ_eq_map, list.zip_with_map_left, of_digits_eq_sum_map_with_index_aux, hl],
    }
end

lemma fun_of_digits_eq_fun_of_sum_map_with_index
  {α β} [has_lift_t ℕ α] 
  [semiring α] 
  (f: α → β) (b: ℕ) (l: list ℕ):
  f ((nat.of_digits b l): α) = f (list.sum (l.map_with_index (λ i a, a * (b: α) ^ i))) :=
begin
  congr,
  rw_mod_cast of_digits_eq_sum_map_with_index,
  have := list.sum_hom _ (nat.cast_add_monoid_hom α),
  simp at this,
  rw [← this, list.map_map_with_index],
end

lemma one_le_of_nonzero_digits_length
  (n b: ℕ) (hn: n ≠ 0):
  1 ≤ (b.digits n).length :=
begin
  induction n with d hd,
  exact absurd rfl hn,
  cases b,
  { simp },
  { 
    cases b,
    { simp },
    { dsimp [nat.digits],
      rw nat.digits_aux,
      simp only [list.length, zero_le, le_add_iff_nonneg_left],
    }
  },
end