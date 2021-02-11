import data.real.cau_seq
import ring_theory.unique_factorization_domain

open is_absolute_value
open_locale classical

theorem ext_hom_primes {α} [comm_monoid_with_zero α] [wf_dvd_monoid α]
  {β} [monoid_with_zero β]
  (φ₁ φ₂: monoid_with_zero_hom α β)
  (h_units: ∀ u: units α, φ₁ u = φ₂ u)
  (h_irreducibles: ∀ a: α, irreducible a → φ₁ a = φ₂ a):
    φ₁ = φ₂ :=
begin
  ext x,
  exact wf_dvd_monoid.induction_on_irreducible x
    (by rw [φ₁.map_zero, φ₂.map_zero])
    (by { rintros _ ⟨ u, rfl ⟩, exact h_units u, })
    (by {
      intros a i ha hi hφa,
      simp only [monoid_with_zero_hom.map_mul, monoid_with_zero_hom.to_fun_eq_coe],
      rw h_irreducibles i hi,
      rw hφa,
    }),
end
