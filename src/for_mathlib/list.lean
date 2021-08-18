import data.list.range
import data.list.indexes

namespace list

lemma sum_ext_le {α : Type*} [ordered_add_comm_monoid α] {l l' : list α}
  (hl : l.length = l'.length)
  (h : ∀ {i} (hle), l.nth_le i hle ≤ l'.nth_le i (hl ▸ hle)) :
  l.sum ≤ l'.sum :=
begin
  induction l with hd tl IH generalizing l',
  { have : l' = nil := by simpa [length_eq_zero] using hl.symm,
    simp [this] },
  { cases l' with hd' tl',
    { simpa using hl },
    { simp at hl,
      simp_rw sum_cons,
      refine add_le_add _ _,
      { exact h (nat.zero_lt_succ _) },
      { apply IH hl,
        intros i hi,
        exact h (nat.succ_lt_succ hi) } } }
end

@[simp] lemma zip_with_const_left {α β γ : Type*} (f : α → γ) (l : list α) (l' : list β) :
  zip_with (λ a b, f a) l l' = take l'.length (map f l) :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l',
    { simp },
    { simp [hl] } }
end

@[simp] lemma zip_with_const_right {α β γ : Type*} (f : β → γ) (l : list α) (l' : list β) :
  zip_with (λ a, f) l l' = take l.length (map f l') :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l',
    { simp },
    { simp [hl] } }
end

@[simp] lemma sum_zip_with_distrib_right {α β γ} [semiring γ] (f : α → β → γ) (n : γ) (l : list α) (l' : list β) :
  (zip_with (λ x y, f x y * n) l l').sum = (l.zip_with f l').sum * n :=
begin
  induction l with hd tl hl generalizing f n l',
  { simp },
  { cases l' with hd' tl',
    { simp, },
    { simp [hl, add_mul] } }
end

lemma map_map_with_index_core {α β γ} (f : ℕ → α → β) (g : β → γ) : ∀ (l : list α) n,
  (l.map_with_index_core f n).map g = l.map_with_index_core (λ i a, g (f i a)) n :=
by intros; induction l generalizing n; simp [*, map_with_index_core]

@[simp] lemma map_map_with_index {α β γ} (f : ℕ → α → β) (g : β → γ) (l : list α) :
  (l.map_with_index f).map g = l.map_with_index (λ i a, g (f i a)) :=
map_map_with_index_core _ _ _ _

lemma map_with_index_eq_range_map {α β} (f: ℕ → α → β) (g: ℕ → β) (l: list α):
  (∀ (i: ℕ) (a: α), f i a = g i) → l.map_with_index f = (range l.length).map g :=
begin
  intro hf,
  induction l with hd tl hl generalizing f g,
  { simp [map_with_index, map_with_index_core, range, range_core, map] },
  {
    simp [map_with_index, map_with_index_core, range_eq_range'],
    split,
    exact hf _ _,
    rw [map_with_index_core_eq, range'_eq_map_range],
    rw hl _ (g ∘ has_add.add 1),
    simp,
    intros i a,
    simp,
    rw add_comm,
    exact hf (1 + i) a,
  },
end

lemma const_mul_sum_of_map_with_index {α β} [semiring β] (f: ℕ → α → β) (l: list α) (c: β):
  c * sum (l.map_with_index f) = sum (l.map_with_index (λ i a, c * f i a)) :=
begin
  induction l with hd tl hl generalizing f,
  { simp [map_with_index, map_with_index_core] },
  { 
    simp [map_with_index, map_with_index_core, left_distrib],
    congr,
    rw [map_with_index_core_eq, map_with_index_core_eq, hl],
  },
end

end list