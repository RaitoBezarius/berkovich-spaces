import data.padics
import topology.basic
import data.rat.basic
import data.real.cau_seq
import topology.metric_space.basic
import topology.homeomorph
import data.nat.prime
import data.nat.basic
import tactic.apply
import tactic.linarith
import topology.metric_space.basic

section
open_locale classical
open list nnreal option is_absolute_value
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

-- théorème d'Ostrowski
-- prouver que la valeur absolue triviale est une valeur absolue
def trivial_abs : ℚ → ℝ := λ a,
    if a = 0 then 0
    else 1

instance : is_absolute_value trivial_abs :=
{ abv_nonneg := λ x, begin rw [trivial_abs], dsimp, split_ifs, exact le_refl 0, exact zero_le_one, end,
  abv_eq_zero := λ x, begin rw [trivial_abs], dsimp, split, contrapose!, intro, rw if_neg a, norm_num, intro, rw if_pos a, end,
  abv_add := λ x y, begin rw [trivial_abs], dsimp, split_ifs, any_goals { linarith,}, exfalso, rw [h_1,h_2] at h, simpa using h, end,
  abv_mul := λ x y, begin rw [trivial_abs], dsimp, split_ifs, any_goals {norm_num}, finish, finish, finish, finish, end }

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

-- integers values of absolute value determines entirely the absolute value.
theorem rat_abs_val_eq_of_eq_on_pnat (abv abv2 : ℚ → ℝ) [habv : is_absolute_value abv] [habv2 : is_absolute_value abv2] (h : ∀ n : ℕ+, abv n = abv2 n)
 : abv = abv2 :=
begin
  ext,
  suffices : ∀ z : ℤ, abv z = abv2 z,
  begin
    induction x,
    rw rat_mk_eq_div,
    rw is_absolute_value.abv_div abv,
    rw is_absolute_value.abv_div abv2,
    rw this x_num,
    have := this (↑ x_denom),
    norm_cast at this,
    rw this,
  end,
  intro x,
  suffices : ∀ z : ℕ, abv z = abv2 z,
  begin
    induction x,
    simp [this],
    push_cast,
    rw is_absolute_value.abv_neg abv,
    rw is_absolute_value.abv_neg abv2,
    norm_cast,
    exact this _,
  end,
  intro x,
  cases x,
  simp,
  rw is_absolute_value.abv_zero abv,
  rw is_absolute_value.abv_zero abv2,
  have := h ⟨nat.succ x_1, nat.succ_pos _⟩,
  simp [-add_comm] at this,
  simp [-add_comm],
  rw this,
end


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
lemma non_trivial_abs_has_an_rational_of_norm_non_null_and_not_one (abv : ℚ → ℚ) [is_absolute_value abv]
    : ((∃ q : ℚ, (abv q) ≠ (trivial_abs q)) →  (∃ n : ℚ, (n ≠ 0) ∧ (abv(n) < 1 ∨ abv(n) > 1))) :=
    (begin
    contrapose!,
    intros,
    by_cases (q = 0),
    rw h,
    rw [is_absolute_value.abv_zero abv, is_absolute_value.abv_zero trivial_abs],
    have b := a q,
    cases b with hq0 h_inequality,
    exfalso,
    exact h hq0,
    have c : trivial_abs q = 1,
    apply (trivial_abs_is_one_iff_nonzero_arg q).1,
    exact h,
    rw c,
    cases h_inequality with h_left_ineq h_right_ineq,
    apply le_antisymm,
    exact h_right_ineq,
    exact h_left_ineq,
    end)

lemma rat_abs_val_one_bounded_padic (abv : ℚ → ℚ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_rat_le_one: (∀ z : ℚ, abv z ≤ 1)):
      ∃ (p) [hp: nat.prime p],
        metric_space_eq
            (metric_rat_with_abv abv)
            (padic.metric_space p) := sorry
    
lemma rat_abs_val_unbounded_real (abv: ℚ → ℚ)
    [habv : is_absolute_value abv]
    (exists_rat_unbounded : ¬ (∀ z : ℕ, abv (↑z) ≤ 1)):
    metric_space_eq
        (metric_rat_with_abv abv)
        (rat.metric_space) :=
    begin
        push_neg at exists_rat_unbounded,
        have n0_spec := nat.find_spec exists_rat_unbounded,
        set n0 := nat.find exists_rat_unbounded,

    end

/- Théorème d'Ostrowski -/
theorem rat_abs_val_p_adic_or_real (abv: ℚ → ℚ)
    [habv: is_absolute_value abv]
    (hnontriv: abv ≠ trivial_abs):
    (metric_space_eq
        (metric_space_of_real_abv abv)
        (rat.metric_space))
    ∨
    (∃ (p) [hp: nat.prime p],
        (metric_space_eq
            (metric_rat_with_abv abv)
            (padic.metric_space p))) :=
    begin
        by_cases boundess : ∀ z ∈ ℚ, abv z ≤ 1,
        {
            apply or.inr,
            apply' rat_abs_val_one_bounded_padic,
        },
        {
            apply or.inl,
            exact rat_abs_val_unbdd_real _ _ _ _,
        }
    end
end