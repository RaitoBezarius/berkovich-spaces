import data.list.range

lemma list.map_with_index_core_eq {α β : Type*} (l : list α) (f : ℕ → α → β) (n : ℕ) :
  l.map_with_index_core f n = l.map_with_index (λ i a, f (i + n) a) :=
begin
  induction l with hd tl hl generalizing f n,
  { simp [list.map_with_index, list.map_with_index_core] },
  { rw [list.map_with_index],
    simp [list.map_with_index_core, hl, add_left_comm, add_assoc, add_comm] }
end

@[simp] lemma list.map_uncurry_zip_eq_zip_with {α β γ : Type*}
  (f : α → β → γ) (l : list α) (l' : list β) :
  list.map (function.uncurry f) (l.zip l') = list.zip_with f l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

lemma list.zip_with_map_left {α β γ δ : Type*}
  (f : α → β → γ) (g : δ → α) (l : list δ) (l' : list β) :
  list.zip_with f (l.map g) l' = list.zip_with (f ∘ g) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

lemma list.zip_with_map_right {α β γ δ : Type*}
  (f : α → β → γ) (l : list α) (g : δ → β) (l' : list δ) :
  list.zip_with f l (l'.map g) = list.zip_with (λ x, f x ∘ g) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end 

lemma list.map_with_index_eq_enum_map_uncurry {α β : Type*} (l : list α) (f : ℕ → α → β) :
  l.map_with_index f = l.enum.map (function.uncurry f) :=
begin
  induction l with hd tl hl generalizing f,
  { simp [list.map_with_index, list.map_with_index_core, list.enum_eq_zip_range] },
  { rw [list.map_with_index, list.map_with_index_core, list.map_with_index_core_eq, hl],
    simp [list.enum_eq_zip_range, list.range_succ_eq_map, list.zip_with_map_left] }
end

@[simp] lemma list.sum_zip_with_distrib_left {α β γ} [semiring γ] (f : α → β → γ) (n : γ) (l : list α) (l' : list β) :
  (list.zip_with (λ x y, n * f x y) l l').sum = n * (l.zip_with f l').sum :=
begin
  induction l with hd tl hl generalizing f n l',
  { simp },
  { cases l' with hd' tl',
    { simp, },
    { simp [hl, mul_add] } }
end

@[simp] lemma list.sum_zip_with_distrib_right {α β γ} [semiring γ] (f : α → β → γ) (n : γ) (l : list α) (l' : list β) :
  (list.zip_with (λ x y, f x y * n) l l').sum = (l.zip_with f l').sum * n :=
begin
  induction l with hd tl hl generalizing f n l',
  { simp },
  { cases l' with hd' tl',
    { simp, },
    { simp [hl, add_mul] } }
end

lemma list.map_map_with_index_core {α β γ} (f : ℕ → α → β) (g : β → γ) : ∀ (l : list α) n,
  (l.map_with_index_core f n).map g = l.map_with_index_core (λ i a, g (f i a)) n :=
by intros; induction l generalizing n; simp [*, list.map_with_index_core]

@[simp] lemma list.map_map_with_index {α β γ} (f : ℕ → α → β) (g : β → γ) (l : list α) :
  (l.map_with_index f).map g = l.map_with_index (λ i a, g (f i a)) :=
list.map_map_with_index_core _ _ _ _

lemma list.le_map_with_index {α β} {f g: ℕ → α → β} [canonically_linear_ordered_add_monoid β] {l: list α}:
  (∀ (i: ℕ) (i_le: i < l.length), f i (list.nth_le l i i_le) ≤ g i (list.nth_le l i i_le)) → (l.map_with_index f).sum ≤ (l.map_with_index g).sum :=
begin
  intro h_f_le,
  induction l with hd tl hl generalizing f g,
  { simp [list.map_with_index, list.map_with_index_core] },
  { simp [list.map_with_index, list.map_with_index_core],
    rw [list.map_with_index_core_eq, list.map_with_index_core_eq],
    apply add_le_add,
    convert h_f_le 0 _,
    simp,
    convert hl _,
    intros i hi,
    convert h_f_le (i + 1) _,
    simp [hi],
   },
end

lemma list.map_with_index_eq_range_map {α β} (f: ℕ → α → β) (g: ℕ → β) (l: list α):
  (∀ (i: ℕ) (a: α), f i a = g i) → l.map_with_index f = (list.range l.length).map g :=
begin
  intro hf,
  induction l with hd tl hl generalizing f g,
  { simp [list.map_with_index, list.map_with_index_core, list.range, list.range_core, list.map] },
  {
    simp [list.map_with_index, list.map_with_index_core, list.range_eq_range'],
    split,
    exact hf _ _,
    rw [list.map_with_index_core_eq, list.range'_eq_map_range],
    rw hl _ (g ∘ has_add.add 1),
    simp,
    intros i a,
    simp,
    rw add_comm,
    exact hf (1 + i) a,
  },
end

lemma list.const_mul_sum_of_map_with_index {α β} [semiring β] (f: ℕ → α → β) (l: list α) (c: β):
  c * list.sum (l.map_with_index f) = list.sum (l.map_with_index (λ i a, c * f i a)) :=
begin
  induction l with hd tl hl generalizing f,
  { simp [list.map_with_index, list.map_with_index_core] },
  { 
    simp [list.map_with_index, list.map_with_index_core, left_distrib],
    congr,
    rw [list.map_with_index_core_eq, list.map_with_index_core_eq, hl],
  },
end