import ring_theory.int.basic

lemma units_int.values (u: units ℤ): u = 1 ∨ u = -1 :=
begin
  have p₁ := fintype.complete u,
  cases p₁,
  left, exact p₁,
  cases p₁,
  right, exact p₁,
  exfalso, exact list.not_mem_nil u p₁,
end
