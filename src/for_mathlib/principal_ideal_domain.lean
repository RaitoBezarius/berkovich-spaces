
import ring_theory.ideal.basic
import ring_theory.principal_ideal_domain

theorem submodule.is_principal.prime_generator_of_prime {α} [comm_ring α] (I: ideal α)
  [submodule.is_principal I] [is_prime: ideal.is_prime I] (ne_bot: I ≠ ⊥):
  prime (submodule.is_principal.generator I) :=
⟨
  by {
    intro h,
    rw ← submodule.is_principal.eq_bot_iff_generator_eq_zero I at h,
    exact ne_bot h,
  },
  by {
    intro h,
    have p₁: I = ⊤,
    from ideal.eq_top_of_is_unit_mem I (submodule.is_principal.generator_mem I) h,
    exact ideal.is_prime.ne_top is_prime p₁,
  },
  by {
    simp only [← submodule.is_principal.mem_iff_generator_dvd I],
    exact is_prime.2,
  }
⟩
