import data.polynomial.basic
import data.polynomial.degree.definitions

lemma polynomial.nat_degree_eq_nat_degree {R} [semiring R] {p q: polynomial R}
  (hpq: p.degree = q.degree): p.nat_degree = q.nat_degree :=
begin
  apply le_antisymm,
  exact polynomial.nat_degree_le_nat_degree (le_of_eq hpq),
  exact polynomial.nat_degree_le_nat_degree (le_of_eq hpq.symm),
end
