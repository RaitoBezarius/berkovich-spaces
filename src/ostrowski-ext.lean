import data.nat.prime
import data.real.basic
import data.padics.padic_norm
import ring_theory.principal_ideal_domain
import data.real.cau_seq
import analysis.complex.exponential
import tactic.apply
import tactic.apply_fun

/- Ostrowski theorem, originally by Alex J. Best -/

section

open_locale classical
open list nnreal option

open padic_norm nat
open_locale real

lemma prod_lt_one_lt_one_of_nonneg {α : Type*} [linear_ordered_semiring α] [canonically_ordered_monoid α]
    {l : list α} (hl : l ≠ [])
    (hl_nonneg: ∀ (a : α) (ha: a ∈ l), a ≥ 0) (hlt : ∀ (a : α) (ha : a ∈ l), a ≤ 1) : (l.prod ≤ 1 ∧ l.prod ≥ 0) :=
begin
   induction l,
   split,
   rw prod_nil,
   rw prod_nil,
   exact zero_le_one,
   rw prod_cons,
   have hd_le_one := hlt l_hd (by simp),
   have hd_ge_zero := hl_nonneg l_hd (by simp),
   by_cases l_tl = [],
   split,
   simp only [h, hd_le_one, prod_nil, mul_one],
   simp only [h, prod_nil, mul_one, hd_ge_zero],
   have := l_ih h
    (begin intros b hb, convert hl_nonneg b _, rw mem_cons_iff, simp only [hb, or_true], end)
    (begin intros b hb, convert hlt b _, rw mem_cons_iff, simp only [hb, or_true], end),
    cases this with ha hb,
   split,
   have prod_le_one := mul_le_mul hd_le_one ha hb zero_le_one,
   rw mul_one at prod_le_one,
   exact prod_le_one,
   exact mul_nonneg hd_ge_zero hb,
end

-- TODO: make it so that α → β such that β is coercible to ℝ
-- f ~ g if exists some r real such that f = g^r
def equivalent (abv1 abv2 : ℚ → ℝ) [is_absolute_value abv1] [is_absolute_value abv2] := ∃ (r : ℝ) (hr : 0 < r), abv1 = ((λ x : ℝ, (x ^ r)) ∘ abv2)

instance is_absolute_value.setoid : setoid ({f : ℚ → ℝ // is_absolute_value f}) :=
{ r := λ x1 x2, @equivalent x1.1 x2.1 x1.2 x2.2,
  iseqv := begin
  split,
  {
    dunfold reflexive,
    intros,
    use ⟨1, by norm_num⟩,
  },
  split,
  {
    dunfold symmetric,
    intros,
    obtain ⟨r, hr, _⟩ := a,
    use [r⁻¹, inv_pos hr],
    ext,
    simp,

    have := congr_fun a_h_h x_1,
    simp at this,
    rw this,
    rw ← real.rpow_mul,
    rw mul_inv_cancel (ne_of_gt hr),
    simp,
    haveI := y.2,
    exact is_absolute_value.abv_nonneg y.val _,
  },
  {
    dunfold transitive,
    intros,
    obtain ⟨r, hr, _⟩ := a,
    obtain ⟨s, hs, _⟩ := a_1,
    use [s * r, mul_pos hs hr],
    ext,
    simp,

    have := congr_fun a_h_h x_1,
    simp at this,
    rw this,

    have := congr_fun a_1_h_h x_1,
    simp at this,
    rw this,

    rw ← real.rpow_mul,
    haveI := z.2,
    exact is_absolute_value.abv_nonneg z.val _,
  }
  end }

variables {α : Type*} [linear_ordered_field α] [archimedean α]
lemma pow_unbounded_below_of_lt_one (x : α) {y : α}
    (hy : 0 < y) (hx : 0 < x) (hy1 : y < 1) : ∃ n : ℕ, y ^ n < x :=
begin
  obtain n := pow_unbounded_of_one_lt (1/x) (one_lt_one_div hy hy1 : 1 < 1/y),
  use n,
  rw div_pow at h,
  simp [-one_div_eq_inv] at h,
  exact lt_of_one_div_lt_one_div hx h,
  exact ne_of_gt hy,
end

def trivial_abv : ℚ → ℝ := λ x, if x = 0 then 0 else 1

lemma rat_mk_eq_div (x_num : ℤ) (x_denom : ℕ) (x_pos : 0 < x_denom) (x_cop : coprime (int.nat_abs x_num) x_denom)
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

instance : is_absolute_value trivial_abv :=
{ abv_nonneg := λ x, begin rw [trivial_abv], dsimp, split_ifs, exact le_refl 0, exact zero_le_one, end,
  abv_eq_zero := λ x, begin rw [trivial_abv], dsimp, split, contrapose!, intro, rw if_neg a, norm_num, intro, rw if_pos a, end,
  abv_add := λ x y, begin rw [trivial_abv], dsimp, split_ifs, any_goals { linarith,}, exfalso, rw [h_1,h_2] at h, simpa using h, end,
  abv_mul := λ x y, begin rw [trivial_abv], dsimp, split_ifs, any_goals {norm_num}, finish, finish, finish, finish, end }

def is_equivalent := is_absolute_value.setoid.r

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
  have := h ⟨succ x_1, succ_pos _⟩,
  simp [-add_comm] at this,
  simp [-add_comm],
  rw this,
end

-- question: can we easily prove that coe ∘ some_abs_val still is an abs_val easily?
def real_padic_norm (p: ℕ): ℚ → ℝ := λ x : ℚ, real.of_rat (padic_norm p x)

instance (p: ℕ) [hp: nat.prime p]: is_absolute_value (real_padic_norm p) :=
{
    abv_nonneg := sorry,
    abv_eq_zero := sorry,
    abv_add := sorry,
    abv_mul := sorry
}

-- absolute values are monoid homemorphisms.
def hom_of_abv {α: Type*} [hlifield: linear_ordered_field α] (abv: α → ℝ) [habv: is_absolute_value abv]: monoid_hom α ℝ :=
{
    to_fun := abv,
    map_one' := is_absolute_value.abv_one abv,
    map_mul' := is_absolute_value.abv_mul abv
}

lemma rat_abs_val_bdd_padic (abv : ℚ → ℝ) [habv : is_absolute_value abv]
  (hnontriv : abv ≠ trivial_abv)
  (int_bdd : ∃ (B : ℚ), ∀ (z : ℕ), abv ↑z ≤ B) :
   ∃ (p) [hp : nat.prime p],
    is_equivalent ⟨abv, habv⟩ ⟨real_padic_norm p, by haveI := rat.discrete_linear_ordered_field; apply_instance⟩ :=
begin
    obtain ⟨B, int_lt_B⟩ := int_bdd,
    have all_nat_le_one : ∀ z : ℕ, abv z ≤ 1 :=
    begin
      contrapose! int_lt_B,
      obtain z := int_lt_B,
      obtain n := pow_unbounded_of_one_lt (↑B) int_lt_B_h,
      use z ^ n,
      push_cast,
      rwa is_absolute_value.abv_pow abv,
    end,
    have all_int_le_one : ∀ z : ℤ, abv z ≤ 1 :=
    begin
      intro,
      induction z,
      exact all_nat_le_one _,
      push_cast,
      rw is_absolute_value.abv_neg abv,
      exact_mod_cast all_nat_le_one _,
    end,
    have : ∃ z : ℕ+, abv z < 1 :=
    begin
      by_contra,
      push_neg at a,
      have : ∀ z : ℕ+, abv z = 1 := λ z, le_antisymm (all_nat_le_one z) (a z),
      apply hnontriv,
      apply rat_abs_val_eq_of_eq_on_pnat,
      intro,
      unfold trivial_abv,
      rw if_neg,
      exact this n,
      have := ne_of_gt n.2,
      intro,
      simpa using a_1,
    end,
    obtain ⟨z, hz⟩ := this,
    have : ∃ p ∈ factors z, abv p < 1 :=
    begin
      by_contra,
      push_neg at a,
      have : (factors z).prod = z := prod_factors z.2,
      have := congr_arg (abv ∘ coe) this,
      simp at this,
      -- FIXME: rewrite this using rw [symmetry, prod_hom …] at this, — sounds better.
      have hprod : coe (list.prod (factors z)) = list.prod ((factors z).map (coe : ℕ → ℚ)) :=
      begin
        symmetry,
        exact prod_hom (factors z) (coe : ℕ → ℚ),
      end,
      rw hprod at this,
      have all_factors_eq_one : ∀ p ∈ factors z, abv p = 1 :=
      begin
        intros p hp,
        apply le_antisymm,
        exact all_nat_le_one p,
        exact a p hp,
      end,
      suffices: abv (↑z) = 1,
      begin
        rw this at hz,
        linarith,
      end,
      have : abv (↑z) = prod (map (abv ∘ (coe : ℕ → ℚ)) (factors z)) :=
      begin
        have step_1 := list.prod_hom (map (coe : ℕ → ℚ) (factors ↑z)) (hom_of_abv abv),
        rw list.map_map at step_1,
        sorry -- TODO: need to understand better how to unbundle my homomorphism.
      end,
      suffices factors_value: map (abv ∘ (coe : ℕ → ℚ)) (factors z) = list.repeat 1 ((factors z).length),
      begin
        apply_fun prod at factors_value,
        simp at factors_value,
        rw factors_value at this,
        exact this,
      end,
      apply eq_repeat.2,
      split,
      exact length_map (abv ∘ coe) (factors z),
      intros b hb,
      have b_prime_exists : ∃ b_p, b_p ∈ (factors z) ∧ abv (↑b_p) = b := exists_of_mem_map hb,
      obtain b_p := b_prime_exists,
      cases b_prime_exists_h,
      have factor_b_p_eq_one := all_factors_eq_one b_p b_prime_exists_h_left,
      rw b_prime_exists_h_right at factor_b_p_eq_one,
      exact factor_b_p_eq_one,
    end,
    obtain ⟨p, p_fact, abv_p_lt_one⟩ := this,
    have : ∀ q (hpq : coprime p q), abv q = 1 :=
    begin
      by_contra,
      push_neg at a,
      obtain q := a,
      have : ∃ e : ℕ, abv (p ^ e) < 1/2 ∧ abv (q^e) < 1/2 :=
      begin
       conv
       {congr,funext, rw is_absolute_value.abv_pow abv,rw is_absolute_value.abv_pow abv,},
        have : abv q < 1 := lt_of_le_of_ne (all_int_le_one q) a_h.2,
        obtain n1 := pow_unbounded_below_of_lt_one (1/2) _ _ this,
        obtain n2 := pow_unbounded_below_of_lt_one (1/2) _ _ abv_p_lt_one,
        use max n1 n2,
        split,
        sorry,
        sorry,
        apply (is_absolute_value.abv_pos abv).2,
        simp,
        apply nat.prime.ne_zero,
        exact nat.mem_factors p_fact,
        exact one_half_pos,
        apply (is_absolute_value.abv_pos abv).2,
        simp,
        by_contra,
        cases a_h,
        rw a at a_h_left,
        have p_fact_absurd : p = 1 := (nat.coprime_zero_right p).1 a_h_left,
        have p_prime : nat.prime p := mem_factors p_fact,
        have := prime.ne_one p_prime,
        apply this,
        exact p_fact_absurd,
        exact one_half_pos,
      end,
      obtain ⟨e, pe_half, qe_half⟩ := this,
      have := gcd_eq_gcd_ab (p^e) (q^e),
      have coprime_pow_for_pq : nat.coprime (p ^ e) (q ^ e) := nat.coprime.pow e e a_h.1,
      have gcdpq_eq_one : nat.gcd (p^e) (q^e) = 1 := nat.coprime.gcd_eq_one coprime_pow_for_pq,
      rw gcdpq_eq_one at this,
      have one_eq_bezout := congr_arg (abv ∘ coe) this,
      simp at one_eq_bezout,
      rw is_absolute_value.abv_one abv at one_eq_bezout,
      have := is_absolute_value.abv_add abv (↑p ^ e * ↑(gcd_a (p ^ e) (q ^ e)))
        (↑q ^ e * ↑(gcd_b (p ^ e) (q ^ e))),
      simp at this,
      rw ← one_eq_bezout at this,
      rw is_absolute_value.abv_mul abv at this,
      rw is_absolute_value.abv_mul abv at this,
      have gcd_a_lt := all_int_le_one (gcd_a (p ^ e) (q ^ e)),
      have gcd_b_lt := all_int_le_one (gcd_b (p ^ e) (q ^ e)),
      have : abv (↑p ^ e) * abv ↑(gcd_a (p ^ e) (q ^ e)) < 1 / 2 :=
      begin
        have ineq := mul_lt_mul pe_half gcd_a_lt ((is_absolute_value.abv_pos abv).mpr _) (by norm_num),
        rw mul_one at ineq,
        exact ineq,
        sorry, -- FIXME: make me a lemma, prove that pgcd(p^e, q^e) = bq^e for some b in Z would provide that bq^e = 1 and that's impossible.
        -- notably because it would mean that b is inverse of q^e in Z, but only 1 and -1 has inverses in Z, thus q^e = +/- 1
        -- at the same time, that would mean that q = +- 1, that's impossible due to the fact that |q| < 1
      end,
        -- (mul_one (1/2)) ▸ (mul_lt_mul pe_half gcd_a_lt ((is_absolute_value.abv_pos abv).mpr _) (by norm_num)),
      have : abv (↑q ^ e) * abv ↑(gcd_b (p ^ e) (q ^ e)) < 1 / 2 :=
      begin
        have ineq := mul_lt_mul qe_half gcd_b_lt ((is_absolute_value.abv_pos abv).mpr _) (by norm_num),
        rw mul_one at ineq,
        exact ineq,
        sorry, -- same argument as below, applied for p^e this time.
      end,
      linarith, -- awesomeness. maths: basically, 1 = p^e * gcd_a + q^e * gcd_b < (gcd_a + gcd_b)/2 ≤ 1, absurd.
    end,
    have hp : p.prime := mem_factors p_fact,
    use [p, hp],
    let α := abv p,
    use [-(real.log α / real.log p)],
    have : 0 < -(real.log α / real.log ↑p) :=
    begin
      have log_alpha_neg : real.log α < 0 := real.log_neg _ (by exact_mod_cast abv_p_lt_one),
      work_on_goal 1 {
        exact (is_absolute_value.abv_pos abv).mpr (by exact_mod_cast nat.prime.ne_zero hp),
      },
      have log_p_pos : 0 < real.log p := real.log_pos (by exact_mod_cast hp.one_lt),
      rw neg_pos,
      exact div_neg_of_neg_of_pos log_alpha_neg log_p_pos,
    end,
    use this,
    ext,
    simp,
    suffices : ∀ x : ℤ, (abv ↑x : ℝ) = ((real_padic_norm p x) ^ -((real.log α) / (real.log ↑p))),
    begin
      induction x,
      have hn := this x_num,
      have hd := this x_denom,
      have := congr_arg2 ((/) : ℝ → ℝ → ℝ) hn hd,
      have padic_abs_xnum_nonzero : 0 ≤ real_padic_norm p ↑x_num := sorry,
      have padic_abs_xdenom_nonzero : 0 < real_padic_norm p ↑x_denom := sorry,
      norm_cast at this,
      rw ← is_absolute_value.abv_div abv at this,
      conv_rhs at this { rw div_eq_mul_inv, },
      rw ← real.rpow_neg at this,
      conv_rhs at this {
          congr, skip, congr, skip,
          rw neg_eq_neg_one_mul,
      },
      rw real.rpow_mul at this,
      rw ← real.mul_rpow at this,
      rw real.rpow_neg (lt_iff_le_and_ne.1 padic_abs_xdenom_nonzero).1 1 at this,
      rw real.rpow_one at this,
      norm_cast at this,
      convert this,
      rw rat_mk_eq_div x_num x_denom _ _,
      norm_cast,
      rw rat_mk_eq_div x_num x_denom _ _,
      sorry, -- it should be something akin to put the ^-1 in the absolute value, then use abv_mul, then some division theorem, and refl.
      exact padic_abs_xnum_nonzero,
      rw real.rpow_neg (lt_iff_le_and_ne.1 padic_abs_xdenom_nonzero).1 1,
      rw real.rpow_one,
      simp,
      repeat {exact (lt_iff_le_and_ne.1 padic_abs_xdenom_nonzero).1},
    end,
    intro,
    letI : principal_ideal_domain ℤ := by apply_instance,
    letI : unique_factorization_domain ℤ := principal_ideal_domain.to_unique_factorization_domain,
    apply unique_factorization_domain.induction_on_prime x_1,
    {
        sorry, -- should be trivial enough. but it does not work due to norm_cast issues.
      -- rw padic_norm.zero,
      -- rw is_absolute_value.zero abv,
    },
    {
      intros,
      -- FIXME: requires interface with nat_abs and absolute values.
      have abs_x2_eq_one: int.nat_abs x_2 = 1 := is_unit_int.1 a,
      sorry,
    },
    {
      intros,
      by_cases hpp1 : p = int.nat_abs p_1,
      -- strat: by multiplication, simplify the |a| and |a|_p^(-log(α)/log(p)) part (by a_3).
      -- then, we can move forward and rewrite p_1 by p
      -- then, we can unfold the real_padic_norm p p definition by p itself (by a_2).
      -- then, we can rewrite p^(log(a)/log(p)) = exp(log(p) * log(a)/log(p)) (by exp stuff)
      -- then, we can rewrite it as exp(log(a)) = a (by simp I suppose).
      -- thus, we have to prove that abv p = α, by definition of α (by assumption?).
      sorry,
      -- strat: immediately, we can prove that the rhs is zero, because (real_padic_norm p (…))^n = p^-(v_p(…)^n) = p^(0 * n) = p^0 = 1
      -- we have now to prove that |p_1 a| = |a|
      -- we have to prove that |p_1| = 1
      -- that's easy, because, by the first this in the context and the fact that p_1 must be coprime to p if p != p_1 and p_1, p are primes
      -- means that: abv p_1 = 1 ! :)
      sorry,
    }

end

/-

lemma ne_zero_one_one_lt (n0 : ℕ)
  (n0_ne_0 : n0 ≠ 0) (n0_ne_1 : n0 ≠ 1) : 1 < n0 := by omega

example (m n : ℕ) (h : m ≤ n): (↑( n - m) : ℝ) = (↑ n :ℝ) - (↑ m:ℝ) :=
begin
library_search
end

lemma coe_sum {α : Type*} {fs : finset α} {f : α → ℕ} : (↑ (sum fs f) : ℚ) = sum fs (coe ∘ f) :=
begin
sorry,
end

lemma coe_sum2 {α : Type*} {fs : finset α} {f : α → ℚ} : (↑ (sum fs f) : ℝ) = sum fs (coe ∘ f) :=
begin
sorry,
end
lemma rat_abs_val_unbdd_real (abv : ℚ → ℚ) [habv : is_absolute_value abv]
  --(hnontriv : ¬is_equivalent ⟨abv, habv⟩ ⟨trivial_abv, trivial_abv.is_absolute_value⟩)
  (int_bdd : ¬∃ (B : ℚ), ∀ (z : ℕ), abv ↑z ≤ B) :
  is_equivalent ⟨abv, habv⟩ ⟨abs, by apply_instance⟩ :=
begin
  push_neg at int_bdd,
  specialize int_bdd 1,
  have n0_spec := nat.find_spec int_bdd,
  set n0 := nat.find int_bdd,
  have n0_ne_0 : n0 ≠ 0 := by by_contra; simp at a; simp [a, is_absolute_value.abv_zero abv] at n0_spec; linarith,
  have n0_ne_1 : n0 ≠ 1 := by by_contra; simp at a; simp [a, is_absolute_value.abv_one abv] at n0_spec; linarith,
  have one_lt_n0 : 1 < n0 := ne_zero_one_one_lt _ n0_ne_0 n0_ne_1,
  have : ∀ n : ℕ, (↑ (abv n) : ℝ) ≤ ↑n ^ (real.log (abv n0) / real.log n0) :=
  begin
    intro,
    have h := base_expansion_spec n0 one_lt_n0 n,
    unfold base_expand at h,
    set l := base_expansion n0 one_lt_n0 n,
    replace h := congr_arg (abv ∘ coe) h,
    simp at h,
    rw coe_sum at h,
    have := is_absolute_value.abv_finset_sum_le abv (fintype.elems (fin (length l))) (coe ∘ λ (i : fin (length l)), ((nth_le l ↑i i.is_lt) * n0 ^ i.val)),
    /-have : (↑(abv (sum (fintype.elems (fin (length l))) (coe ∘ λ (i : fin (length l)), nth_le l ↑i _ * n0 ^ i.val))) : ℝ) ≤
      ↑(sum (fintype.elems (fin (length l))) (abv ∘ coe ∘ λ (i : fin (length l)), nth_le l ↑i _ * n0 ^ i.val)) := begin
      norm_cast,
      exact this,
    end,-/
    erw h at this,
    simp [is_absolute_value.abv_mul abv, is_absolute_value.abv_pow abv] at this,
    have le_aux : ∀ (x : fin l.length) (hx : x ∈ (fintype.elems (fin (length l)))), (
      (λ (x : fin (length l)), abv ↑(nth_le l ↑x x.is_lt) * abv ↑n0 ^ x.val) x ≤
      (λ (x : fin (length l)), abv ↑n0 ^ x.val) x) :=
    begin
      intros,
      simp,
      have : nth_le l ↑x x.is_lt ∈ l := nth_le_mem l ↑x _,
      have : nth_le l ↑x x.is_lt < n0 := base_expansion_le n0 one_lt_n0 n (nth_le l ↑x (x.is_lt)) this,
      have n0_min := nat.find_min int_bdd,
      specialize n0_min this,
      simp at n0_min,
      have : 0 ≤ abv ↑n0 ^ x.val := pow_nonneg (is_absolute_value.abv_nonneg _ _) _,

      exact mul_le_of_le_one_left this n0_min,
    end,
    have := le_trans this (finset.sum_le_sum le_aux),
    have le_aux : ∀ (x : fin l.length) (hx : x ∈ (fintype.elems (fin (length l)))), (
      (λ (x : fin (length l)), (abv ↑n0 : ℝ) ^ x.val) x ≤
      (λ (x : fin (length l)), (abv ↑n0 : ℝ) ^ (log ↑n / log ↑n0)) x) :=
    begin
      intros,
      simp,
      norm_cast,
      have := rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt n0_spec : (1 : ℝ) ≤ abv ↑n0)
      (begin
      transitivity (↑(l.length - 1) : ℝ),
      have := (le_pred_of_lt (x.is_lt)),
      exact_mod_cast this,
      have : 1 ≤ l.length := begin apply le_of_not_lt, intro, have := x.is_lt, have : (x.val < 0) := by linarith, exact nat.not_lt_zero _ this,  end,

      rw (cast_sub this : (↑(l.length - 1) : ℝ) = l.length - ↑ 1),
      rw cast_one,
      convert sub_le_sub_right (base_expansion_length n0 one_lt_n0 n) 1,
      symmetry,
      exact add_sub_cancel _ _,
      end : (x.val : ℝ) ≤ log ↑n / log ↑n0),
      convert this,
      push_cast,
      sorry,
    end,
    rw [← @rat.cast_le ℝ _ _] at this,
    push_cast at this,
    rw coe_sum2 at this,
    simp at this,
    push_cast at le_aux,
    have := le_trans (by exact_mod_cast this) (finset.sum_le_sum le_aux),
    rw finset.sum_const at this,
    rw (rfl : fintype.elems (fin l.length) = ⟨list.fin_range l.length, list.nodup_fin_range _⟩) at this,
    have card_is := fintype.card_fin l.length,
    rw fintype.card at card_is,
    rw univ at card_is,
    rw card_is at this,
    simp [l] at this,
    have := le_trans this base_expansion_length n0 one_lt_n0 n,
  end
end
#check fintype.elems (fin 5).


.

/- Ostrowski -/
theorem rat_abs_val_p_adic_or_real (abv : ℚ → ℚ) [habv : is_absolute_value abv]
(hnontriv : ¬ (is_equivalent ⟨abv, habv⟩ ⟨trivial_abv, by apply_instance⟩))
: is_equivalent ⟨abv, habv⟩ ⟨abs, by apply_instance⟩
∨ ∃ (p) [hp : nat.prime p], is_equivalent ⟨abv, habv⟩ ⟨padic_norm p, by haveI := rat.discrete_linear_ordered_field; apply_instance⟩ :=
begin
  by_cases int_bdd : ∃ B, ∀ z : ℕ, abv z ≤ B,
  {
    apply or.inr,
    apply' rat_abs_val_bdd_padic,
  },
  {
    apply or.inl,
    exact rat_abs_val_unbdd_real _ _ _ _,
  }
end -/
end