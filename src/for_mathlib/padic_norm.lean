import data.nat.basic
import data.nat.prime
import data.padics.padic_norm

theorem padic_norm_primes {p q: ℕ} [p_prime: fact (nat.prime p)] [q_prime: fact (nat.prime q)]
  (neq: p ≠ q): padic_norm p q = 1 :=
begin
  have p: padic_val_rat p q = 0,
  exact_mod_cast @padic_val_nat_primes p q p_prime q_prime neq,
  simp [padic_norm, p, q_prime.1, nat.prime.ne_zero q_prime],
end
