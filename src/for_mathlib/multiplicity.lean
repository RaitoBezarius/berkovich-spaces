import algebra.associated
import ring_theory.multiplicity

lemma multiplicity.eq_of_associated {α} [comm_monoid_with_zero α]
  [decidable_rel ((∣): α → α → Prop)]
  {a b c: α} (h: associated b c): multiplicity a b = multiplicity a c :=
begin
  have aux: ∀ a b c: α, associated b c → multiplicity a b ≤ multiplicity a c,
  { intros a b c h,
    rw multiplicity.multiplicity_le_multiplicity_iff,
    exact λ n, (dvd_iff_dvd_of_rel_right h).1, },
  exact le_antisymm (aux a b c h) (aux a c b h.symm),
end

lemma multiplicity.unit_right {α} [comm_monoid_with_zero α]
  [decidable_rel ((∣): α → α → Prop)]
  {a: α} (ha: ¬is_unit a)
  (u: units α): multiplicity a u = 0 :=
begin
  rw multiplicity.eq_of_associated unit_associated_one,
  exact multiplicity.one_right ha,
end
