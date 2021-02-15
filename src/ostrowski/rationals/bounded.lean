-- import data.real.cau_seq
import data.padics.padic_norm
import algebra.associated

import abvs_equiv

import valuations.basic
import valuations.bounded
import valuations.abv_pid

import ostrowski.rationals.basic

import for_mathlib.padic_norm
import for_mathlib.int
import for_mathlib.exp_log

open is_absolute_value

open_locale classical
noncomputable theory

lemma padic_norm_q (p: ℕ) (q: ℤ) (p_prime: prime p) (q_prime: prime q):
  padic_norm p q = if associated q p then 1/p else 1 :=
begin
  haveI: fact (nat.prime p) := nat.prime_iff_prime.2 p_prime,
  exact if h: associated q p
    then by {
      rw show padic_norm p q = padic_norm p p,
      by {
        rcases h.symm with ⟨ u, rfl ⟩,
        push_cast,
        rw abv_mul (padic_norm p),
        rw show padic_norm p (u: ℤ) = 1,
        by { cases units_int.values u with h h; simp [h], },
        rw mul_one,
      },
      simp [h, @padic_norm.padic_norm_p_of_prime p (nat.prime_iff_prime.2 p_prime)],
    }
    else by {
      unfold padic_norm,
      unfold padic_val_rat,
      have: multiplicity (p: ℤ) q = 0,
      {
        have p_int_prime: prime (p: ℤ) := nat.prime_iff_prime_int.1
          (nat.prime_iff_prime.2 p_prime),
        simp [h, multiplicity.multiplicity_eq_zero_of_not_dvd
          (λ h', h (primes_associated_of_dvd p_int_prime q_prime h').symm)],
      },
      simp [h, p_prime.1, q_prime.1, p_prime.ne_one, this],
    },
end

def rat_padic_abv (p: ℕ) (p_prime: nat.prime p): ℚ → ℝ := λ x: ℚ, (padic_norm p x: ℝ)

instance rat_padic_abv_is_absolute_value (p: ℕ) (p_prime: nat.prime p):
  is_absolute_value (rat_padic_abv p p_prime) :=
begin
  haveI: fact (nat.prime p) := p_prime,
  exact { abv_nonneg := by { unfold rat_padic_abv, norm_cast, exact abv_nonneg (padic_norm p), },
    abv_eq_zero := by { unfold rat_padic_abv, norm_cast, intro x, exact abv_eq_zero (padic_norm p), },
    abv_add := by { unfold rat_padic_abv, norm_cast, exact abv_add (padic_norm p), },
    abv_mul := by { unfold rat_padic_abv, norm_cast, exact abv_mul (padic_norm p), } }
end

def inj_ℤ_ℚ_hom: monoid_with_zero_hom ℤ ℚ :=
{ to_fun := λ k, k,
  map_zero' := by simp,
  map_one' := by simp,
  map_mul' := by simp }

def inj_ℚ_ℝ_hom: monoid_with_zero_hom ℚ ℝ :=
{ to_fun := λ k, k,
  map_zero' := by simp,
  map_one' := by simp,
  map_mul' := by simp }

lemma rat_abs_val_one_bounded_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (bounded: (∀ z : ℕ, abv z ≤ 1)):
      ∃ (p) [p_prime: nat.prime p], abvs_equiv abv (rat_padic_abv p p_prime) :=
begin
  set abv': ℤ → ℝ := (λ k, abv k) with abv'_def,
  haveI: is_absolute_value abv' := {
    abv_nonneg := λ k, by { rw abv'_def, dsimp, exact abv_nonneg abv k, },
    abv_eq_zero := λ k, by {
      rw abv'_def,
      dsimp,
      have: abv k = 0 ↔ (k: ℚ) = 0 := abv_eq_zero abv,
      norm_cast at this,
      exact this,
    },
    abv_add := λ h k, by { rw abv'_def, dsimp, push_cast, exact abv_add abv h k, },
    abv_mul := λ h k, by { rw abv'_def, dsimp, push_cast, exact abv_mul abv h k, }
  },
  have bounded': ∀ k: ℤ, abv' k ≤ 1,
  {
    intro k,
    cases k.nat_abs_eq with h; rw h,
    exact bounded k.nat_abs,
    rw abv_neg abv',
    exact bounded k.nat_abs,
  },
  have nontrivial': ∃ k: ℤ, k ≠ 0 ∧ abv' k ≠ 1,
  {
    by_contra h,
    push_neg at h,
    have h_abv: ∀ k: ℤ, k ≠ 0 → abv k = 1,
    from λ k hk, abv'_def ▸ h k hk,
    apply hnontriv,
    ext,
    exact if hx: x = 0
      then by { unfold trivial_abs, simp [hx, abv_zero abv], }
      else by {
        revert x,
        rw rat.forall,
        intros a b,
        intro h',
        have: a ≠ 0 ∧ b ≠ 0,
        {
          by_contra h,
          rw not_and_distrib at h,
          push_neg at h,
          apply h',
          simp [h],
        },
        unfold trivial_abs,
        simp [abv_div abv, h_abv a this.1, h_abv b this.2, this],
      },
  },

  obtain ⟨ p, p_prime, equiv ⟩: ∃ (p: ℤ) (p_prime: prime p),
    abvs_equiv abv' (sample_padic_abv p p_prime),
  from abv_bounded_padic abv' bounded' nontrivial',
  have p_abs_prime: nat.prime p.nat_abs := int.prime_iff_nat_abs_prime.1 p_prime,
  use [p.nat_abs, p_abs_prime],
  have p_abs_pos: 0 < (p.nat_abs: ℝ),
  { norm_cast, exact (gt_iff_lt.1 $ int.nat_abs_pos_of_ne_zero p_prime.1), },

  rcases equiv with ⟨ α, α_pos, h ⟩,
  have eq_α: ∀ x, (abv' x) ^ α = sample_padic_abv p p_prime x,
  { rw ← h, exact λ x, rfl, },
  set β := real.log (1/p.nat_abs) / real.log (1/2) with β_def,
  have β_pos: 0 < β,
  {
    refine div_pos_of_neg_of_neg
      (real.log_neg (div_pos zero_lt_one p_abs_pos) $ (div_lt_one p_abs_pos).2 _)
      (real.log_neg one_half_pos $ (div_lt_one _).2 one_lt_two),
    norm_cast, exact nat.prime.one_lt p_abs_prime,
    exact zero_lt_two,
  },
  have αβ_pos: 0 < α * β := mul_pos α_pos β_pos,

  have eq_β: ∀ x, sample_padic_abv p p_prime x ^ β = rat_padic_abv p.nat_abs p_abs_prime x,
  {
    unfold rat_padic_abv,
    suffices: (λ x, sample_padic_abv p p_prime x ^ β) = (λ x, padic_norm p.nat_abs x),
    {
      intro x,
      have: (λ x, sample_padic_abv p p_prime x ^ β) x = (λ x, padic_norm p.nat_abs x) x,
      by rw this,
      exact this,
    },
    haveI: fact (nat.prime p.nat_abs) := p_abs_prime,
    set φ₁ := hom_of_equiv (hom_of_abv (sample_padic_abv p p_prime)) β β_pos
      (by {
        have φ_f: sample_padic_abv p p_prime = hom_of_abv (sample_padic_abv p p_prime) := rfl,
        rw ← φ_f,
        exact abv_nonneg (sample_padic_abv p p_prime),
      }) with φ₁_def,
    set φ₂ := (inj_ℚ_ℝ_hom.comp $ hom_of_abv (padic_norm p.nat_abs)).comp inj_ℤ_ℚ_hom with φ₂_def,
    have φ₁_f: (λ x, sample_padic_abv p p_prime x ^ β) = φ₁ := rfl,
    have φ₂_f: (λ k: ℤ, (padic_norm p.nat_abs k: ℝ)) = φ₂ := rfl,
    rw [φ₁_f, φ₂_f],
    suffices: φ₁ = φ₂, by rw this,
    apply ext_hom_primes,
    {
      rw [← φ₁_f, ← φ₂_f],
      dsimp,
      intro u,
      cases units_int.values u with h h;
      simp [h, abv_neg (sample_padic_abv p p_prime), abv_one (sample_padic_abv p p_prime)],
    },
    {
      intros q hq,
      have q_prime := principal_ideal_ring.irreducible_iff_prime.1 hq,
      rw [← φ₁_f, ← φ₂_f],
      dsimp,
      rw padic_norm_q p.nat_abs q (nat.prime_iff_prime.1 p_abs_prime) q_prime,
      rw sample_padic_abv_on_primes p p_prime q q_prime,
      exact if h: associated q p
        then by {
          have: associated q p.nat_abs,
          from associated.trans h (int.associated_nat_abs p),
          simp only [h, this, rat.cast_coe_nat, rat.cast_div,
            rat.cast_one, if_true, eq_self_iff_true],
          rw β_def,
          apply log_inj_pos (real.rpow_pos_of_pos one_half_pos _)
            (div_pos zero_lt_one p_abs_pos),
          rw real.log_rpow one_half_pos,
          calc real.log (1/p.nat_abs) / real.log (1/2) * real.log (1/2)
            = real.log (1/p.nat_abs) * (real.log (1/2) / real.log (1/2)) : by ring
            ... = real.log (1/p.nat_abs) : by rw [div_self (real.log_ne_zero_of_ne_one
              (1/2) one_half_pos $ ne_of_lt one_half_lt_one), mul_one],
        }
        else by {
          have: ¬ associated q p.nat_abs,
          from λ h', h (associated.trans h' $ associated.symm $ int.associated_nat_abs _),
          simp [h, this],
        },
    },
  },

  use [α*β, αβ_pos],
  apply funext,
  rw rat.forall,
  intros a b,
  rw [abv_div abv, abv_div (rat_padic_abv _ _)],
  {
    rw real.div_rpow (abv_nonneg abv _) (abv_nonneg abv _),
    rw real.rpow_mul (abv_nonneg abv _),
    rw real.rpow_mul (abv_nonneg abv _),
    rw [eq_α a, eq_α b, eq_β a, eq_β b],
  },
  -- I didn't find a way to make the typeclasses work :/
  exact rat_padic_abv_is_absolute_value p.nat_abs p_abs_prime,
end
