import algebra.associated

lemma primes_associated_of_dvd {α} [comm_cancel_monoid_with_zero α] {p q: α}
  (p_prime: prime p) (q_prime: prime q) (dvd: p ∣ q): associated p q :=
begin
  cases dvd with c hc,
  cases ((q_prime.irreducible).is_unit_or_is_unit hc)
    .resolve_left p_prime.not_unit with u hu,
  exact ⟨ u, by rw [hu, hc] ⟩,
end
