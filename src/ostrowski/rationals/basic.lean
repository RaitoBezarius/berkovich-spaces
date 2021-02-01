
import data.nat.prime
import data.rat.basic
import data.real.basic
import analysis.special_functions.pow
import data.real.cau_seq
import data.padics

open is_absolute_value
noncomputable theory

def trivial_abs : ℚ → ℝ := λ a,
    if a = 0 then 0
    else 1

instance : is_absolute_value trivial_abs :=
{ abv_nonneg := λ x, begin rw [trivial_abs], dsimp, split_ifs, exact le_refl 0, exact zero_le_one, end,
  abv_eq_zero := λ x, begin rw [trivial_abs], dsimp, split, contrapose!, intro, rw if_neg ᾰ, norm_num, intro, rw if_pos ᾰ, end,
  abv_add := λ x y, begin rw [trivial_abs], dsimp, split_ifs, any_goals { linarith,}, exfalso, rw [h_1,h_2] at h, simpa using h, end,
  abv_mul := λ x y, begin rw [trivial_abs], dsimp, split_ifs, any_goals {norm_num}, finish, finish, finish, finish, end }

def padic_norm_ℝ (p: ℕ) := λ r: ℚ, (padic_norm p r: ℝ)

instance abv_lift (abv: ℚ → ℚ) [habv: is_absolute_value abv]:
  is_absolute_value (λ r: ℚ, (abv r: ℝ)) :=
{ abv_nonneg := by { norm_cast, exact abv_nonneg abv, },
  abv_eq_zero := by { norm_cast, intro x, exact abv_eq_zero abv, },
  abv_add := by { norm_cast, exact abv_add abv, },
  abv_mul := by { norm_cast, exact abv_mul abv, } }

instance padic_is_abv {p: ℕ} [hp: nat.prime p] : is_absolute_value (padic_norm_ℝ p) :=
  @abv_lift (padic_norm p) (@padic_norm.is_absolute_value p hp)

lemma trivial_abs_is_one_iff_nonzero_arg (a: ℚ) : (a ≠ 0) ↔ (trivial_abs a = 1) :=
begin
    split,
    intro h₁,
    unfold trivial_abs,
    by_cases (a = 0),
    exfalso,
    exact h₁ h,
    rw if_neg h,
    contrapose!,
    intro h,
    unfold trivial_abs,
    rw if_pos h,
    finish
end

lemma rat_mk_eq_div (x_num : ℤ) (x_denom : ℕ) (x_pos : 0 < x_denom) (x_cop : nat.coprime (int.nat_abs x_num) x_denom)
: ({num := x_num, denom := x_denom, pos := x_pos, cop := x_cop}:ℚ) = (↑ x_num)/(↑ x_denom) := begin
norm_cast,
rw rat.mk,
rw rat.mk_nat,
rw dif_neg,
rw rat.mk_pnat,
{
  simp [x_cop.gcd_eq_one],
},
exact ne_of_gt x_pos,
end

def hom_of_abv {α} [linear_ordered_field α] {β} [ring β] [nontrivial β]
  (abv: β → α) [is_absolute_value abv]:
  monoid_with_zero_hom β α := {
    to_fun := abv,
    map_zero' := abv_zero abv,
    map_one' := abv_one abv,
    map_mul' := abv_mul abv,
 }

def hom_of_equiv (abv: ℚ → ℝ) [habv: is_absolute_value abv] (α: ℝ) (α_ne_zero: α ≠ 0):
  monoid_with_zero_hom ℚ ℝ := {
    to_fun := (λ r: ℚ, (abv r) ^ α),
    map_zero' := by {
      rw abv_zero abv,
      exact real.zero_rpow α_ne_zero,
    },
    map_one' := by {
      rw abv_one abv,
      exact real.one_rpow α,
    },
    map_mul' := by {
      intros x y,
      rw abv_mul abv,
      rw real.mul_rpow (abv_nonneg abv x) (abv_nonneg abv y),
    },
  }

-- Deserves its place in matlib, as `monoid_with_zero_hom.map_inv`
theorem Γ₀_map_inv {G₁ G₂: Type} [group_with_zero G₁] [group_with_zero G₂]
  (φ: monoid_with_zero_hom G₁ G₂) (a: G₁) (a_ne_zero: a ≠ 0): φ a⁻¹ = (φ a)⁻¹ :=
begin
  apply eq_inv_of_mul_left_eq_one,
  rw ← monoid_with_zero_hom.map_mul,
  rw inv_mul_cancel a_ne_zero,
  rw monoid_with_zero_hom.map_one,
end

lemma induction_on_primes [P: nat → Prop] (h₁: P 0) (h₂: P 1)
  (h: ∀ p a: ℕ, prime p → P a → P (p * a)): ∀ n: ℕ, P n :=
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
    exact h p a hp ha,
  },
end

-- Integer values of a morphism `φ` and its value on `-1` completely determines `φ`
theorem mul_mor_eq_of_eq_on_pnat (φ₁ φ₂: monoid_with_zero_hom ℚ ℝ)
  (same_on_neg_one: φ₁ (-1) = φ₂ (-1)) (same_on_nat: ∀ n: ℕ, φ₁ n = φ₂ n): (φ₁: ℚ → ℝ) = φ₂ :=
begin
  ext,
  suffices : ∀ z : ℤ, φ₁ z = φ₂ z,
  begin
    induction x,
    rw rat_mk_eq_div,
    repeat { rw div_eq_mul_inv, },
    have x_denom_ne_zero: (x_denom: ℚ) ≠ 0,
    {
      symmetry,
      norm_cast,
      exact (ne_of_lt x_pos),
    },
    rw monoid_with_zero_hom.map_mul φ₁,
    rw Γ₀_map_inv φ₁ x_denom x_denom_ne_zero,
    rw monoid_with_zero_hom.map_mul φ₂,
    rw Γ₀_map_inv φ₂ x_denom x_denom_ne_zero,
    rw this x_num,
    have := this (↑ x_denom),
    norm_cast at this,
    rw this,
  end,
  intro x,
  suffices : ∀ z : ℕ, φ₁ z = φ₂ z,
  begin
    induction x,
    simp [this],
    push_cast,
    conv {
      congr,
      rw neg_eq_neg_one_mul,
      skip,
      rw neg_eq_neg_one_mul,
      skip,
    },
    rw monoid_with_zero_hom.map_mul φ₁,
    rw monoid_with_zero_hom.map_mul φ₂,
    rw same_on_neg_one,
    simp,
    norm_cast,
    exact this _,
  end,
  intro x,
  cases x,
  simp,
  have := same_on_nat (nat.succ x_1),
  simp [-add_comm] at this,
  simp [-add_comm],
  rw this,
end

lemma abs_val_equiv_of_equiv_on_primes (abv abv': ℚ → ℝ)
  [habv: is_absolute_value abv] [habv': is_absolute_value abv']
  (α: ℝ) (α_ne_zero: α ≠ 0)
  (h: ∀ p: ℕ, prime p → (abv p) ^ α = abv' p): (λ r: ℚ, (abv r) ^ α) = abv' :=
begin
  have: ∀ n: ℕ, (abv n) ^ α = abv' n,
  {
    have inductive_step: ∀ q a: ℕ, prime q → (abv a) ^ α = abv' a
      → (abv (q * a: ℕ)) ^ α = abv' ((q * a): ℕ),
    {
      intros q a q_prime a_norms_eq,
      calc (abv (q * a: ℕ)) ^ α
        = abv (q*a: ℕ) ^ α
          : by { refl }
        ... = ((abv q) * (abv a)) ^ α
          : by { push_cast, rw abv_mul abv, }
        ... = (abv q) ^ α * (abv a) ^ α
          : by { rw real.mul_rpow (abv_nonneg abv q) (abv_nonneg abv a), }
        ... = (abv' q) * (abv' a)
          : by { rw [h q q_prime, a_norms_eq], }
        ... = abv' (q * a)
          : by { rw ← abv_mul abv', }
        ... = abv' ((q * a): ℕ)
          : by { norm_cast, },
    },
    apply induction_on_primes,
    {
      norm_cast,
      rw [abv_zero abv, abv_zero abv'],
      rw real.zero_rpow,
      exact α_ne_zero,
    },
    {
      norm_cast,
      rw [abv_one abv, abv_one abv'],
      rw real.one_rpow,
    },
    exact inductive_step,
  },
  
  set equiv_hom := hom_of_equiv abv α α_ne_zero with equiv_hom_def,
  set abv'_hom := abv_hom abv' with abv'_hom_def,
  have abv_eq_hom_fn: abv' = abv'_hom := rfl,
  have equiv_abs_eq_hom_fn: (λ r: ℚ, abv r ^ α) = equiv_hom := rfl,
  have same_on_neg_one: equiv_hom (-1) = abv'_hom (-1),
  {
    rw [← abv_eq_hom_fn, ← equiv_abs_eq_hom_fn],
    simp,
    rw [abv_neg abv, abv_neg abv'],
    rw [abv_one abv, abv_one abv'],
    rw real.one_rpow,
  },
  apply mul_mor_eq_of_eq_on_pnat equiv_hom abv'_hom same_on_neg_one,

  exact this, 
end
