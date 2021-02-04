import data.nat.basic

namespace nat

section find
parameter {p: ℕ → Prop}
parameter [decidable_pred p]

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : nat.find h < n ↔ ∃ m < n, p m :=
⟨λ h2, ⟨nat.find h, h2, nat.find_spec h⟩, λ ⟨m, hmn, hm⟩, (nat.find_min' h hm).trans_lt hmn⟩

@[simp] lemma le_find_iff (h : ∃ (n : ℕ), p n) (n : ℕ) : n ≤ nat.find h ↔ ∀ m < n, ¬ p m :=
by simp_rw [← not_lt, not_iff_comm, not_forall, not_not, find_lt_iff]

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < nat.find h ↔ ∀ m ≤ n, ¬ p m :=
by simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

end find
end nat