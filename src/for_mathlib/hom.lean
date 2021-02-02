import algebra.group_with_zero.basic
import algebra.group.hom

-- Deserves its place in matlib, as `monoid_with_zero_hom.map_inv`
theorem monoid_with_zero_hom.map_inv {G₁ G₂: Type} [group_with_zero G₁] [group_with_zero G₂]
  (φ: monoid_with_zero_hom G₁ G₂) (a: G₁) (a_ne_zero: a ≠ 0): φ a⁻¹ = (φ a)⁻¹ :=
begin
  apply eq_inv_of_mul_left_eq_one,
  rw ← monoid_with_zero_hom.map_mul,
  rw inv_mul_cancel a_ne_zero,
  rw monoid_with_zero_hom.map_one,
end