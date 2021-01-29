import data.padics
import topology.basic
import data.rat.basic
import data.real.cau_seq
import analysis.special_functions.exp_log
import analysis.special_functions.pow
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
def trivial_abs : ℚ → ℝ := λ a,
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

def is_padic_norm 
  (p: ℕ) [fact p.prime]
  (abv: ℚ → ℝ) [is_absolute_value abv] :=
    (λ r: ℚ, (padic_norm p r: ℝ)) = abv

lemma induction_on_primes [P: nat → Prop] (base_case: ∀ p: ℕ, prime p → P p)
  (h: ∀ p a: ℕ, prime p → P a → P (p * a)): ∀ n: ℕ, P n :=
begin
  sorry
end

lemma prime_norm_lt_one_of_bounded_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1)):
      ∃ p: ℕ, prime p ∧ abv p < 1 :=
begin
  -- First we find some `n ∈ ℕ*` such that `abv n < 1`.
  obtain ⟨ n, zero_lt_n, abvn_lt_one ⟩: ∃ n: ℕ, 0 < n ∧ abv n < 1,
  {
    -- `abv` is nontrivial so there is some `r ≠ 0` such that `abv r ≠ 1`.
    obtain ⟨ r, r_ne_zero, abvr_notone ⟩: ∃ r: ℚ, r ≠ 0 ∧ abv r ≠ 1,
    {
      -- Just some formal play, not much to say.
      by_contra h,
      push_neg at h,
      apply hnontriv,
      ext r,
      by_cases h': r = 0,
      {
        rw (abv_eq_zero abv).2 h',
        rw (abv_eq_zero trivial_abs).2 h',
      },
      {
        rw h r h',
        rw [trivial_abs],
        dsimp,
        split_ifs,
        refl,
      },
    },
    -- Let's write `r = a/b`. We get `(abv a)/(abv b) ≠ 1`, then `abv a ≠ abv b`.
    rcases r with ⟨ a, b, b_pos, a_b_coprimes ⟩,
    have not_eq: abv a ≠ abv b,
    {
      -- Just doing the calculus by hand.
      -- Is there a simpler way to do this ?
      rw rat_mk_eq_div at abvr_notone,
      rw is_absolute_value.abv_div abv at abvr_notone,
      intro h,
      rw h at abvr_notone,
      apply abvr_notone,
      ring,
      rw inv_mul_cancel,
      intro h,
      rw (abv_eq_zero abv) at h,
      norm_cast at h,
      linarith,
    },
    -- Then either `abv a` or `abv b` is strictly less than one,
    -- so we have some `n: ℕ` such that `abv n < 1`.
    obtain ⟨ zero_ne_a, zero_ne_b ⟩: 0 ≠ a ∧ 0 ≠ b,
    {
      by_contra h,
      rw ← or_iff_not_and_not at h,
      cases h,
      {
        -- `a = 0` but `r = a/b ≠ 0`.
        apply r_ne_zero,
        rw rat_mk_eq_div,
        rw ← h,
        norm_cast,
        exact rat.zero_mk b,
      },
      {
        -- `b = 0` but `b` is the denominator of `r`; `b_pos` says `0 < b`.
        linarith,
      },
    },

    by_cases abv b = 1,
    {
      -- If `abv b = 1`, we need to discuss wether `a ≥ 0` or not.
      rw h at not_eq,
      cases a,
      {
        -- `a ≥ 0`
        use a,
        rw ← int.coe_nat_eq a at not_eq,
        norm_cast at not_eq,
        have p: abv a ≤ 1,
        from all_nat_le_one a,
        rw lt_iff_le_and_ne,
        rw ← int.coe_nat_eq at zero_ne_a,
        norm_cast,
        norm_cast at zero_ne_a,
        exact ⟨ ⟨ zero_le a, zero_ne_a ⟩, lt_of_le_of_ne p not_eq ⟩,
      },
      {
        -- `a < 0`
        use a + 1,
        push_cast at not_eq,
        rw (abv_neg abv) at not_eq,
        have p: abv (a + 1) ≤ 1,
        from all_nat_le_one (a + 1),
        -- rw lt_iff_le_and_ne,
        push_cast,
        exact ⟨ nat.zero_lt_succ a, lt_of_le_of_ne p not_eq ⟩,
      },
    },
    {
      -- `abv b ≠ 1`, so we show `abv b < 1`, as `b: ℕ`, we get what we wanted.
      use b,
      have p: abv b ≤ 1,
      from all_nat_le_one b,
      exact ⟨ b_pos, lt_of_le_of_ne p h ⟩,
    },
  },

  /-
  We just got : `⟨ n, n_ne_zero, abvn_lt_one ⟩: ∃ n: ℕ, n ≠ 0 ∧ abv n < 1`
  Now we search for some prime `p` such that `abv p < 1`.
  We prove the existence by contradiction : let us suppose that `forall p, abv p < 1`.
  -/
  by_contradiction h,
  push_neg at h,

  -- First we prove that the absolute value commutes with arbitrary products
  have abv_prod_eq_prod_abv: ∀ l: list nat, abv (prod l: ℕ) = prod (list.map (λ k: ℕ, abv k) l),
  {
    intro l,
    induction l with r l h,
    {
      -- The result is clear for the empty list.
      simp,
      exact abv_one abv,
    },
    {
      -- We use the compatibility of absolute values with the product.
      simp,
      rw ← h,
      rw abv_mul abv,
    },
    -- This went surprisingly well !
  },

  -- then that in our case any prouct of primes is equal to `1`.
  -- (We use `= 1` because it avoids performing calculations by hand.)
  have prod_abv_primes_ge_one:
    ∀ l: list nat, (∀ k ∈ l, prime k) → prod (list.map (λ k: ℕ, abv k) l) = 1,
  {
    intro l,
    induction l with r l h',
    simp,
    {
      intro h_primes,
      simp,
      have p₁: abv r = 1 := le_antisymm
        (all_nat_le_one r)                      -- By hypothesis `|…| ≤ 1`.
        (h r (h_primes r (by { left, refl, }))) -- Everyone in `l` is prime therefore `|…| ≥ 1`;
      ,
      -- The product of the rest is equal to `1`.
      have p₂ := h' (λ r h, by { apply h_primes r, right, exact h, }),
      rw p₁,
      rw p₂,
      simp,
    },
  },

  /- the absolute value of the product of the prime factors of `n` is therefore
    greater than or equal to `1`. -/
  have prod_eq_one: abv (prod (nat.factors n): ℕ) = 1,
  {
    rw abv_prod_eq_prod_abv,
    apply prod_abv_primes_ge_one,
    intros p hp,
    rw ← nat.prime_iff_prime,
    exact @nat.mem_factors n p hp,
  },

  rw nat.prod_factors zero_lt_n at prod_eq_one,
  linarith only [abvn_lt_one, prod_eq_one],
end

lemma padic_norm_q (p: ℕ) (q: ℕ) (p_prime: prime p) (q_prime: prime q):
  (p = q → padic_norm p q = 1/p) ∧ (p ≠ q → padic_norm p q = 1) :=
begin
  split,
  {
    intro h, -- In the case where `p = q`
    have p: padic_val_rat p q = 1,
    {
      rw ← h,
      unfold padic_val_rat,
      simp [p_prime.1, prime.ne_one p_prime],
    },
    unfold padic_norm,
    rw p,
    simp [q_prime.1],
  },
  {
    intro h, -- In the case where `p ≠ q`
    have p: padic_val_rat p q = 0,
    {
      unfold padic_val_rat,
      simp [q_prime.1, prime.ne_one p_prime],
      suffices h: p^0 ∣ q ∧ ¬ p^1 ∣ q,
      {
        norm_cast,
        rw roption.get_eq_iff_eq_some,
        rw multiplicity.eq_some_iff.2 h,
        refl,
      },
      split,
      {
        simp,
      },
      {
        by_contra p_div_q,
        apply h,
        rw ← associated_iff_eq,
        simp at p_div_q,
        have q_div_p := dvd_symm_of_irreducible
          (irreducible_of_prime p_prime)
          (irreducible_of_prime q_prime)
          p_div_q,
        exact associated_of_dvd_dvd p_div_q q_div_p,
      },
    },
    unfold padic_norm,
    rw p,
    simp [q_prime.1],
  },
end

lemma abs_val_bounded_q (abv : ℚ → ℝ) [habv : is_absolute_value abv]
  (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1))
  (p: ℕ) (p_prime: prime p) (abvp_lt_one: abv p < 1):
  ∃ α: ℝ, ∀ q: ℕ, prime q →
    (p = q → abv q = (1/p) ^ α) ∧ (p ≠ q → abv q = 1 ^ α) :=
begin
  -- We set `α` such that it Just Works™
  set α := - real.log (abv p) / real.log p with α_def,
  use α,

  intros q q_prime,

  split,
  intro h,
  {
    -- When `p = q`, we just need to show that `abv p = p ^ (- α)`.
    have zero_lt_p: 0 < (p: ℝ),
    { norm_cast, exact nat.lt_of_le_and_ne (zero_le p) (ne.symm (p_prime.1)), },
    -- The result is clear by definition of `α`.
    -- The calculus that leads to it is yet long to formalize...
    rw ← h,
    suffices h: real.log (abv p) = real.log ((1/p) ^ α),
    {
      have p₁: abv p > 0,
      {
        apply gt_iff_lt.2,
        apply (abv_pos abv).2,
        norm_cast,
        exact p_prime.1,
      },
      have p₂: (1/p: ℝ)^α > 0,
      {
        apply real.rpow_pos_of_pos,
        rw one_div_pos,
        -- norm_cast,
        exact zero_lt_p,
      },
      apply le_antisymm,
      rw ← real.log_le_log p₁ p₂,
      exact le_of_eq h,
      rw ← real.log_le_log p₂ p₁,
      exact le_of_eq (eq.symm h),
    },
    have one_lt_p: 1 < p,
    from (nat.prime.one_lt ∘ nat.prime_iff_prime.2) p_prime,
    calc real.log (abv p) = real.log (abv p) * 1
        : by ring
      ... = real.log (abv p) * (real.log p / real.log p)
        : by { rw div_self, symmetry, apply ne_of_lt ∘ real.log_pos,
          norm_cast, exact one_lt_p, }
      ... = real.log (abv p) / real.log p * real.log p
        : by ring
      ... = real.log (p^(real.log (abv p) / real.log p))
        : by { rw ← real.log_rpow, exact zero_lt_p, }
      ... = real.log (p^(- (- real.log (abv p) / real.log p)))
        : by ring
      ... = real.log (p^(-α))     : by rw α_def
      ... = real.log (p^(-1 * α)) : by ring
      ... = real.log ((p ^ (-1: ℝ)) ^ α)
        : by { congr' 1, exact real.rpow_mul (le_of_lt zero_lt_p) (-1) α, }
      ... = real.log (((p ^ (1: ℝ))⁻¹) ^ α)
        : by { congr' 2, exact real.rpow_neg (le_of_lt zero_lt_p) 1, }
      ... = real.log ((p⁻¹) ^ α)
        : by { congr' 3, exact real.rpow_one p, }
      ... = real.log ((1/p) ^ α)  : by simp,
  },
  {
    intro h,
    rw real.one_rpow α,

    -- We reason by contradiction. Our hypothesis becomes `abv q < 1`.
    by_contradiction h',
    have abvq_lt_one: abv q < 1,
    from lt_iff_le_and_ne.2 ⟨ (all_nat_le_one q), h' ⟩,
    -- We find `N` such that `(abv p) ^ N, (abv q) ^ N < 1/2`.
    obtain ⟨ n, abvpn_lt_half, abvqn_lt_half ⟩: ∃ n: ℕ, ((abv p)^n < 1/2) ∧ ((abv q)^n < 1/2),
    {
      have geom_tendsto_zero: ∀ r: ℝ, (0 ≤ r) → (r < 1) →
        ∃ N: ℕ, ∀ n ≥ N, r^n < 1/2,
      {
        -- Again, some formal play.
        -- Went actually pretty nicely !
        intros r h₁ h₂,
        have p := metric.tendsto_at_top.1 (tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂),
        unfold dist at p,
        unfold abs at p,
        specialize p (1/2) (by linarith),
        rcases p with ⟨ N, hN ⟩,
        use N,
        intros n hn,
        specialize hN n hn,
        calc r^n = r^n - 0                 : by simp
          ... ≤ max (r^n - 0) (-(r^n - 0)) : le_max_left _ _
          ... < 1/2 : hN,
      },
      obtain ⟨ N₁, pN₁ ⟩: ∃ N: ℕ, ∀ n ≥ N, (abv p)^n < 1/2,
      { exact geom_tendsto_zero (abv p) (abv_nonneg abv p) abvp_lt_one },
      obtain ⟨ N₂, pN₂ ⟩: ∃ N: ℕ, ∀ n ≥ N, (abv q)^n < 1/2,
      { exact geom_tendsto_zero (abv q) (abv_nonneg abv q) abvq_lt_one },
      use max N₁ N₂,
      exact ⟨
        pN₁ (max N₁ N₂) (by linarith only [le_max_left N₁ N₂]),
        pN₂ (max N₁ N₂) (by linarith only [le_max_right N₁ N₂])
      ⟩,
    },
    -- We use Bézout to find `u`, `v` such that `1 = u * p^n + v * q^n`.
    obtain ⟨ u, v, bezout ⟩: ∃ u: ℤ, ∃ v: ℤ, 1 = u * p^n + v * q^n,
    {
      have p₁: ((p^n).gcd (q^n): ℤ) = (1: ℤ),
      {
        norm_cast,
        suffices coprimes: p.coprime q,
        { exact (nat.coprime.pow_left n ∘ nat.coprime.pow_right n) coprimes },
        rw nat.coprime_primes
          (nat.prime_iff_prime.2 p_prime)
          (nat.prime_iff_prime.2 q_prime),
        exact h,
      },
      use [(p^n).gcd_a (q^n), (p^n).gcd_b (q^n)],
      rw ← p₁,
      rw mul_comm _ (p^n: ℤ),
      rw mul_comm _ (q^n: ℤ),
      norm_cast,
      exact nat.gcd_eq_gcd_ab (p^n) (q^n),
    },
    have abv_rel_le_one: ∀ k: ℤ, abv k ≤ 1,
    {
      intro k,
      by_cases h: 0 < k,
      {
        rw ← abs_of_pos h,
        rw int.abs_eq_nat_abs,
        exact all_nat_le_one _,
      },
      {
        simp at h,
        rw ← abv_neg abv,
        norm_cast,
        rw ← abs_of_nonpos h,
        rw int.abs_eq_nat_abs,
        exact all_nat_le_one _,
      }
    },
    have abv_bezout_lt_one: abv (u * p^n + v * q^n) < 1,
    {
      -- Is there a way to simplify this ?
      -- (Of course these two properties could be gathered in one function...)
      have p₁: abv u * abv p ^ n ≤ 1 * abv p ^ n,
      { exact (mul_le_mul_right
        (pow_pos ((abv_pos abv).2 (by { norm_cast, exact p_prime.1, })) n)).2
        (abv_rel_le_one u), },
      have p₂: abv v * abv q ^ n ≤ 1 * abv q ^ n,
      { exact (mul_le_mul_right
        (pow_pos ((abv_pos abv).2 (by { norm_cast, exact q_prime.1, })) n)).2
        (abv_rel_le_one v), },
      calc abv (u * p^n + v * q^n)
        ≤ abv (u * p^n) + abv (v * q^n) : abv_add abv _ _
        ... = abv u * abv (p^n) + abv v * abv (q^n) : by { congr; rw abv_mul abv _ _, }
        ... = abv u * abv p ^ n + abv v * abv q ^ n : by { congr; rw abv_pow abv _ _, }
        ... ≤ 1 * abv p ^ n + 1 * abv q ^ n         : add_le_add p₁ p₂
        ... = abv p ^ n + abv q ^ n                 : by ring
        ... < 1/2 + 1/2                             : add_lt_add abvpn_lt_half abvqn_lt_half
        ... = 1                                     : by ring,
    },
    have absurd: (1: ℝ) < 1,
    {
      calc 1 = abv (1: ℤ)             : eq.symm (abv_one abv)
        ... = abv (u * p^n + v * q^n) : by { rw bezout, norm_cast, }
        ... < 1                       : abv_bezout_lt_one,
    },
    linarith only [absurd],
  },
end

lemma abs_val_equiv_of_equiv_on_primes (abv abv': ℚ → ℝ)
  [habv: is_absolute_value abv] [habv': is_absolute_value abv']
  (α: ℝ)
  (h: ∀ p: ℕ, prime p → (abv p) ^ α = abv' p): (λ r: ℚ, (abv r) ^ α) = abv' :=
begin
  have: ∀ n: ℕ, (abv n) ^ α = abv' n,
  {
    have base_case := h,
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
    exact base_case,
    exact inductive_step,
  },
  
  have comp_is_abv: is_absolute_value (λ r: ℚ, (abv r) ^ α),
  { sorry },
  apply @rat_abs_val_eq_of_eq_on_pnat (λ r: ℚ, (abv r) ^ α) abv' comp_is_abv _,
  exact this,
end

lemma rat_abs_val_one_bounded_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
      (hnontriv: abv ≠ trivial_abs)
      (all_nat_le_one: (∀ z : ℕ, abv z ≤ 1)):
      ∃ (p) [hp: nat.prime p],
      -- ∃ α: ℝ, abv = equiv_abs α
      @is_padic_norm p hp abv _ :=
begin
  obtain ⟨ p, p_prime, abvp_lt_one ⟩: ∃ p: ℕ, prime p ∧ abv p < 1,
  from prime_norm_lt_one_of_bounded_padic abv hnontriv all_nat_le_one,

  set α := - real.log (abv p) / real.log p with α_def,

  obtain ⟨ α, abv_val ⟩ := abs_val_bounded_q abv all_nat_le_one p p_prime abvp_lt_one,

  -- We show that `abv` is equivalent to the p-adic norm on all primes.
  have same_on_primes: ∀ q: ℕ, prime q → (padic_norm p q: ℝ) ^ α = abv q,
  {
    intros q q_prime,

    /-
    We have already calculated the values of the p-adic norm and of `abv` on
    all prime numbers (lemmas `abs_val_bounded_q` and `padic_norm_q`).
    -/
    have padic_norm := padic_norm_q p q p_prime q_prime,
    specialize abv_val q q_prime,

    by_cases h: p = q,
    {
      rw padic_norm.1 h,
      rw abv_val.1 h,
      simp,
    },
    {
      rw padic_norm.2 h,
      rw abv_val.2 h,
      simp,
    },
  },

  -- Now we reason by induction, by using prime numbers as the base case.
  
  set padic := λ q, (padic_norm p q: ℝ) with padic_def,
  have padic_is_absolute_value: is_absolute_value padic,
  from sorry, -- @padic_norm.is_absolute_value p (nat.prime_iff_prime.2 p_prime),

  have := @abs_val_equiv_of_equiv_on_primes padic abv
    padic_is_absolute_value _
    α same_on_primes,
  
  sorry  
end

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
theorem rat_abs_val_p_adic_or_real (abv: ℚ → ℝ)
    [habv: is_absolute_value abv]
    (hnontriv: abv ≠ trivial_abs):
    (∃ α : ℝ, abv = equiv_abs α)
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