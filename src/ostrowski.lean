import data.padics
import topology.basic
import data.rat.basic
import data.real.cau_seq
import analysis.special_functions.exp_log
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

-- prouver que la valeur absolue triviale est une valeur absolue
def trivial_abs : ℚ → ℚ := λ a,
    if a = 0 then 0
    else 1

instance : is_absolute_value trivial_abs :=
{ abv_nonneg := λ x, begin rw [trivial_abs], dsimp, split_ifs, exact le_refl 0, exact zero_le_one, end,
  abv_eq_zero := λ x, begin rw [trivial_abs], dsimp, split, contrapose!, intro, rw if_neg ᾰ, norm_num, intro, rw if_pos ᾰ, end,
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
theorem rat_abs_val_eq_of_eq_on_pnat (abv abv2 : ℚ → ℝ) [habv : is_absolute_value abv] [habv2 : is_absolute_value abv2] (h : ∀ n : ℕ, abv n = abv2 n)
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
  have := h (nat.succ x_1),
  simp [-add_comm] at this,
  simp [-add_comm],
  rw this,
end


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
lemma non_trivial_abs_has_an_rational_of_norm_non_null_and_not_one (abv : ℚ → ℚ) [is_absolute_value abv]
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

def is_padic_norm 
  (p: ℕ) [fact p.prime]
  (abv: ℚ → ℚ) [is_absolute_value abv] :=
    (@padic_norm_e p _) ∘ (@padic.of_rat p _) = abv

lemma rat_abs_val_one_bounded_padic (abv : ℚ → ℚ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1)):
      ∃ (p) [hp: nat.prime p],
      @is_padic_norm p hp abv _ := sorry

-- all_nat_le_one become all_int_le_one

lemma nat_abs_val_le_nat_pow_alpha (abv: ℚ → ℝ)
  [habv: is_absolute_value abv] (n₀: ℕ) (n: ℕ):
  (abv n: ℝ) ≤ real.exp (real.log n * (real.log (abv n₀) / real.log n₀)) := sorry

lemma nat_pow_alpha_le_nat_abs_val (abv: ℚ → ℝ)
  [habv: is_absolute_value abv] (n₀: ℕ) (n: ℕ):
  real.exp (real.log n * (real.log (abv n₀) / real.log n₀)) ≤ (abv n: ℝ) := sorry

def equiv_abs (α: ℝ) (q: ℚ): ℝ := real.exp (α * real.log (@abs ℚ _ q))
lemma equiv_abs_is_absolute_value (α: ℝ): is_absolute_value (equiv_abs α) := sorry

lemma rat_abs_val_unbounded_real (abv: ℚ → ℝ)
    [habv : is_absolute_value abv]
    (exists_rat_unbounded : ¬ (∀ z : ℕ, abv (↑z) ≤ 1)):
    ∃ α: ℝ, abv = equiv_abs α :=
    begin
        push_neg at exists_rat_unbounded,
        -- we want the smallest.
        set n₀ := nat.find exists_rat_unbounded,
        have n₀_spec := nat.find_spec exists_rat_unbounded,
        have n₀_not_one: n₀ > 1 := sorry, -- necessarily, n₀ > 1.
        set α := real.log (abv n₀) / real.log n₀ with h_α,
        use α,
        apply rat_abs_val_eq_of_eq_on_pnat _ _,
        {
          intro n,
          unfold equiv_abs,
          -- prove abv n = n^α
          have: abv n = real.exp (real.log n * α) :=
          begin
            apply le_antisymm,
            apply nat_abs_val_le_nat_pow_alpha abv n₀ n,
            apply nat_pow_alpha_le_nat_abs_val abv n₀ n,
          end,
          rw this,
          congr' 1,
          rw abs_eq_self.2,
          push_cast,
          ac_refl,
          norm_cast,
          exact zero_le n,
          -- and n^α = |n|^α
        },
        exact habv,
        exact equiv_abs_is_absolute_value _,
    end

/- Théorème d'Ostrowski -/
theorem rat_abs_val_p_adic_or_real (abv: ℚ → ℚ)
    [habv: is_absolute_value abv]
    (hnontriv: abv ≠ trivial_abs):
    (∃ α : ℝ, real.of_rat ∘ abv = equiv_abs α)
    ∨
    (∃ (p) [hp: nat.prime p],
        @is_padic_norm p hp abv _) :=
    begin
        by_cases boundness : ∀ z : ℕ, abv z ≤ 1,
        {
            apply or.inr,
            exact rat_abs_val_one_bounded_padic _ hnontriv boundness,
        },
        {
            apply or.inl,
            sorry, -- projections are a bit annoying.
            -- exact rat_abs_val_unbounded_real abv boundness,
        }
    end
end