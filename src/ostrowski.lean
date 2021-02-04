import data.padics
import topology.basic
import data.rat.basic
import data.real.cau_seq
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import topology.metric_space.basic
import topology.homeomorph
import topology.algebra.group_with_zero
import data.nat.prime
import data.nat.basic
import tactic.apply
import tactic.linarith
import topology.metric_space.basic
import ring_theory.unique_factorization_domain

import abvs_equiv
import for_mathlib.exp_log
import for_mathlib.nat_find
import ostrowski.rationals.bounded
import ostrowski.rationals.unbounded

section
open_locale classical
open list option is_absolute_value
noncomputable theory

variables {α : Type*} [ring α]

def metric_space_of_real_abv (abv: α → ℝ) [is_absolute_value abv] : metric_space α :=
{ dist := λ x y, abv $ x - y,
  dist_self := λ x, show abv (x-x) = 0, by simp[abv_zero abv],
  eq_of_dist_eq_zero := λ x y h, eq_of_sub_eq_zero $ (abv_eq_zero abv).mp h,
  dist_comm := abv_sub abv,
  dist_triangle := λ x y z, begin
    change abv (x-z) ≤ abv (x-y) + abv (y-z),
    rw show x - z = (x - y) + (y - z), by abel,
    apply abv_add,
  end}

-- rational metric space equipped of an absolute value
def metric_rat_with_abv (abv: ℚ → ℝ) [is_absolute_value abv]: metric_space ℚ := metric_space_of_real_abv abv

-- définition de l'équivalence de valeur absolues
def metric_space_eq {α: Type*} (d d' : metric_space α) : Prop :=
    d.to_uniform_space.to_topological_space = d'.to_uniform_space.to_topological_space

-- hypothèsqe 1: il existe n, tel que |n|_* > 1
-- lemme 1 : il existe une écriture en base a de b^n
-- lemme 2 : limite (a(nlog_a b + 1))^(1/n) = 1
-- lemme 3 : il existe lambda, pour tout n, |n|_* = n^lambda

-- hypothèse 2: pour tout n, |n|_* <= 1

-- stratégie:

-- par contraposée, on a qu'à prouver que si pour tout n : Q, (n = 0) ou (abv(n) = 1)
-- alors, on a que abv = trivial_abs OK?

-- rigoureusement, on contrapose
-- on introduit les éléments
-- on procède en discutant selon q = 0 ou non
-- on élimine assez vite le cas q = 0 par réécriture de la valeur absolue
-- puis ensuite, on se donne le cas qu'on veut, on cloture exfalso où ça a du sens
-- sinon on se ramène à démontrer déjà d'une part que trivial_abs q = 1 (trivial)
-- et du coup ça revient à démontrer que sous hypothèse de double inégalité, on a abv q = 1
-- ce qui est immédiat par antisymétrie.

-- TODO: what about n : N ?
lemma non_trivial_abs_has_an_rational_of_norm_non_null_and_not_one (abv : ℚ → ℝ) [is_absolute_value abv]
    : ((∃ q : ℚ, (abv q) ≠ (trivial_abs q)) →  (∃ n : ℚ, (n ≠ 0) ∧ (abv(n) < 1 ∨ abv(n) > 1))) :=
    (begin
    contrapose!,
    intros H q,
    by_cases (q = 0),
    rw h,
    rw [is_absolute_value.abv_zero abv, is_absolute_value.abv_zero trivial_abs],
    have c : trivial_abs q = 1,
    apply (trivial_abs_is_one_iff_nonzero_arg q).1,
    exact h,
    rw c,
    linarith [H q h]
    end)

def equiv_abs (α: ℝ) := λ q: ℚ, ((abs q: ℝ) ^ α)

def equiv_abs_neg (α: ℝ): ∀ q: ℚ, equiv_abs α (-q) = equiv_abs α q :=
begin
  intro q,
  unfold equiv_abs,
  push_cast,
  rw neg_eq_neg_one_mul,
  simp,
end

def equiv_abs_one {α: ℝ}: equiv_abs α 1 = 1 :=
begin
  unfold equiv_abs,
  simp,
end

def hom_of_equiv_abs (α: ℝ) (α_ne_zero: α ≠ 0):
  monoid_with_zero_hom ℚ ℝ := {
    to_fun := equiv_abs α,
    map_zero' := by {
      unfold equiv_abs,
      norm_cast,
      exact real.zero_rpow α_ne_zero,
    },
    map_one' := by {
      unfold equiv_abs,
      norm_cast,
      exact real.one_rpow α,
    },
    map_mul' := by {
      unfold equiv_abs,
      intros x y,
      push_cast,
      rw abs_mul,
      rw real.mul_rpow (abs_nonneg x) (abs_nonneg y),
    },
  }

lemma rat_abs_val_unbounded_real (abv: ℚ → ℝ)
    [habv : is_absolute_value abv]
    (exists_nat_unbounded : ¬ (∀ z : ℕ, abv (↑z) ≤ 1)):
    --∃ α: ℝ, abv = equiv_abs α :=
    abvs_equiv abv (λ x: ℚ, abs x) :=
    begin
        push_neg at exists_nat_unbounded,
        -- we want the smallest.
        set n₀ := nat.find exists_nat_unbounded,
        have n₀_spec := nat.find_spec exists_nat_unbounded,
        have n₀_smallest_spec: ∀ (a: ℕ), a < n₀ → abv a ≤ 1,
        {
          intros a ha,
          exact not_lt.1 (nat.find_min exists_nat_unbounded ha),
        },
        have aux0: ∀ (m: ℕ) (h: m ≤ 1), ¬ (1 < abv m),
        {
          intros m h,
          push_neg,
          have: m = 0 ∨ m = 1 := by dec_trivial!,
          apply or.elim this,
          intro h_zero,
          rw h_zero,
          rw_mod_cast is_absolute_value.abv_zero abv,
          exact zero_le_one,
          intro h_one,
          rw h_one,
          rw_mod_cast is_absolute_value.abv_one abv,
        },
        have n₀_not_one: n₀ > 1 := (nat.lt_find_iff exists_nat_unbounded 1).2 aux0, -- necessarily, n₀ > 1
        have n₀_ge_two: n₀ ≥ 2 := sorry, 
        apply abvs_equiv_symmetric,
        set α := real.log (abv n₀) / real.log n₀ with h_α,
        have h_n0_pow_α_eq_abv_n0: abv n₀ = n₀^α,
        {
          rw [real.rpow_def_of_pos, h_α, ← mul_div_assoc, mul_div_cancel_left, real.exp_log],
          apply (is_absolute_value.abv_pos abv).2,
          apply ne_of_gt,
          -- we throw this goal for now and we will focus on the log.
          -- so we can provide the same proof for the two similar goals.
          rotate 1,
          apply real.log_ne_zero_of_ne_one,
          rotate 1,
          norm_cast,
          exact ne_of_gt n₀_not_one,
          all_goals {
            norm_cast,
            exact lt_trans zero_lt_one (by assumption),
          }
        },
        use α,
        have zero_lt_α: 0 < α,
        {
          apply div_pos,
          have one_lt_abvn₀: 1 < abv n₀,
          {
            rw ← gt_iff_lt,
            exact n₀_spec,
          },
          exact (real.log_pos_iff (by linarith only [one_lt_abvn₀])).2
            one_lt_abvn₀,
          exact (real.log_pos_iff (by { norm_cast, linarith only [n₀_not_one], })).2
              (by { norm_cast, linarith only [n₀_not_one], }),
        },
        set abv_hom := hom_of_abv abv with abv_hom_def,
        set equiv_abs_hom := hom_of_equiv_abs α (ne.symm $ ne_of_lt zero_lt_α) with equiv_abs_def,
        have abv_eq_hom_fn: abv = abv_hom := rfl,
        have equiv_abs_eq_hom_fn: equiv_abs α = equiv_abs_hom := rfl,
        have same_on_neg_one: abv_hom (-1) = equiv_abs_hom (-1),
        {
          rw [← abv_eq_hom_fn, ← equiv_abs_eq_hom_fn],
          rw [abv_neg abv, equiv_abs_neg],
          rw [abv_one abv, equiv_abs_one],
        },
        use zero_lt_α,
        unfold equiv_abs at equiv_abs_eq_hom_fn,
        rw [abv_eq_hom_fn, equiv_abs_eq_hom_fn],
        symmetry,
        apply ext_hom_pnat _ _ same_on_neg_one,
        intro n,
        rw [← abv_eq_hom_fn, ← equiv_abs_eq_hom_fn],
        unfold equiv_abs,
        -- prove abv n = n^α
        have: abv n = n ^ α :=
        begin
          apply le_antisymm,
          apply nat_abs_val_le_nat_pow_alpha
           zero_lt_α n₀_ge_two h_n0_pow_α_eq_abv_n0 n₀_spec
           n₀_smallest_spec,
          apply nat_pow_alpha_le_nat_abs_val
           zero_lt_α n₀_ge_two h_n0_pow_α_eq_abv_n0 n₀_spec
           n₀_smallest_spec,
        end,
        rw this,
        congr' 1,
        rw abs_eq_self.2,
        all_goals { norm_cast },
        exact zero_le n,
    end

/- Théorème d'Ostrowski -/
theorem rat_abs_val_p_adic_or_real (abv: ℚ → ℝ)
    [habv: is_absolute_value abv]
    (hnontriv: abv ≠ trivial_abs):
    (abvs_equiv abv (λ x: ℚ, abs x))
    ∨
    (∃ (p) [hp: nat.prime p],
        @abvs_equiv _ _ abv (padic_norm_ℝ p) habv (@padic_is_abv p hp)) :=
    begin
        by_cases boundness : ∀ z : ℕ, abv z ≤ 1,
        {
            apply or.inr,
            exact rat_abs_val_one_bounded_padic _ hnontriv boundness,
        },
        {
            apply or.inl,
            exact rat_abs_val_unbounded_real abv boundness,
        }
    end
end