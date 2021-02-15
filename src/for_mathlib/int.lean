import ring_theory.int.basic

lemma int.associated_nat_abs (k: ℤ): associated k k.nat_abs :=
begin
  apply associated.symm,
  unfold associated,
  cases int.nat_abs_eq k with h h,
  use 1, simp, exact h.symm,
  use -1, simp, exact h.symm,
end

lemma int.prime_iff_nat_abs_prime {k: ℤ}: prime k ↔ nat.prime k.nat_abs :=
begin
  rw nat.prime_iff_prime_int,
  rw prime_iff_of_associated (int.associated_nat_abs k),
end

lemma int.associated_iff (a: ℤ) (b: ℤ): associated a b ↔ (a = b ∨ a = -b) :=
begin
  split,
  {
    intro h,
    rcases h with ⟨ u, h ⟩,
    have p₁ := fintype.complete u,
    cases p₁,
    left, rw ← mul_one a, rw p₁ at h, exact h,
    cases p₁,
    right, rw p₁ at h, simp at h, linarith only [h],
    exfalso, exact list.not_mem_nil u p₁,
  },
  {
    intro h,
    cases h,
    rw h,
    use -1, simp, linarith [h],
  },
end

lemma units_int.values (u: units ℤ): u = 1 ∨ u = -1 :=
begin
  have p₁ := fintype.complete u,
  cases p₁,
  left, exact p₁,
  cases p₁,
  right, exact p₁,
  exfalso, exact list.not_mem_nil u p₁,
end
