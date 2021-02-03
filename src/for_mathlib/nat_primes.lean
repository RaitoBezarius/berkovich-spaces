import data.nat.basic
import data.nat.prime
import ring_theory.int.basic
import ring_theory.unique_factorization_domain

lemma induction_on_primes [P: nat → Prop] (h₁: P 0) (h₂: P 1)
  (h: ∀ p a: ℕ, nat.prime p → P a → P (p * a)): ∀ n: ℕ, P n :=
begin
  intro n,
  apply unique_factorization_monoid.induction_on_prime,
  exact h₁,
  {
    intros n h,
    rw nat.is_unit_iff.1 h,
    exact h₂,
  },
  {
    intros a p _ hp ha,
    exact h p a (nat.prime_iff_prime.2 hp) ha,
  },
end
