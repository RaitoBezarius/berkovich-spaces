import algebra.group_power
import algebra.char_p
import ring_theory.ideal_operations
import ring_theory.subring
import data.real.nnreal

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([Wedhorn])

The definition of a valuation we use here is Definition 1.22 of [Wedhorn]. `valuation R Γ₀`
is the type of valuations R → Γ₀, with a coercion to the underlying
function. If v is a valuation from R to Γ₀ then the induced group
homomorphism units(R) → Γ₀ is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in [Wedhorn; 1.27] is not strictly
speaking a relation, because v₁ : valuation R Γ₁ and v₂ : valuation R Γ₂ might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as Γ₀ varies) on a ring R is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) as the definition of equivalence.

The trivial valuation associated to a prime ideal P of R is `trivial P : valuation R Γ₀`.

The support of a valuation v : valuation R Γ₀ is `supp v`. If J is an ideal of R
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

Taken out the perfectoids formalization in Lean.
-/

local attribute [instance] classical.prop_decidable
noncomputable theory

local attribute [instance, priority 0] classical.DLO

open function ideal

universes u u₀ u₁ u₂ -- v is used for valuations

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections

notation `ℝ+` := nnreal
set_option old_structure_cmd true

section
variables (R) [ring R]

/-- The type of ℝ+-valued valuations on R. -/
structure valuation extends R →* ℝ+ :=
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) ≤ max (to_fun x) (to_fun y))

end

namespace valuation

section basic
variables (R) [ring R]

/-- A valuation is coerced to the underlying function R → ℝ+. -/
instance : has_coe_to_fun (valuation R) := { F := λ _, R → ℝ+, coe := valuation.to_fun }

/-- A valuation is coerced to a monoid morphism R → ℝ+. -/
instance : has_coe (valuation R) (R →* ℝ+) := ⟨valuation.to_monoid_hom⟩

variables {R} (v : valuation R) {x y z : R}

@[squash_cast, simp] lemma coe_coe : ((v : R →* ℝ+) : R → ℝ+) = v := rfl

@[simp] lemma map_zero : v 0 = 0 := v.map_zero'
@[simp] lemma map_one  : v 1 = 1 := v.map_one'
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.map_mul'
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ max (v x) (v y) := v.map_add'

@[simp] lemma map_pow  : ∀ x (n:ℕ), v (x^n) = (v x)^n :=
@is_monoid_hom.map_pow _ _ _ _ v (monoid_hom.is_monoid_hom v.to_monoid_hom)

@[ext] lemma ext {v₁ v₂ : valuation R} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
by { cases v₁, cases v₂, congr, funext r, exact h r }

lemma ext_iff {v₁ v₂ : valuation R} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
⟨λ h r, congr_arg _ h, ext⟩

-- The following definition is not an instance, because we have more than one v on a given R.
/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v (by apply_instance)

lemma units_of_nnreal_eq_one (u: units ℝ+): u = 1 := sorry

/-- If v is a valuation on a division ring then v(x) = 0 iff x = 0. -/
lemma zero_iff {K : Type u₀} [division_ring K]
  (v : valuation K) {x : K} : v x = 0 ↔ x = 0 :=
begin
  split,
  { contrapose!,
    intro h,
    have u := (units.map (v : K →* ℝ+) $ units.mk0 _ h),
    have u_eq_vx: ↑u = (v x) := sorry,
    rw ← u_eq_vx,
    rw units_of_nnreal_eq_one u,
    simp,
  },
  { intro h; exact h.symm ▸ v.map_zero },
end

lemma ne_zero_iff {K : Type u₀} [division_ring K]
  (v : valuation K) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
not_iff_not_of_iff v.zero_iff

@[simp] lemma map_inv' {K : Type u₀} [division_ring K]
  (v : valuation K) {x : K} (h : x ≠ 0) : v x⁻¹ = (v x)⁻¹ :=
begin
  have H: (v x ≠ 0) := (ne_zero_iff v).2 h,
  apply (nnreal.mul_eq_mul_left H).1,
  rw [← v.map_mul, mul_inv_cancel h, nnreal.mul_inv_cancel H, v.map_one],
end

@[simp] lemma map_inv {K : Type u₀} [discrete_field K]
  (v : valuation K) {x : K} : v x⁻¹ = (v x)⁻¹ :=
begin
  by_cases h : x = 0,
  { begin
    rw [h, inv_zero, map_zero],
    symmetry,
    exact nnreal.inv_zero,
    end },
  { exact v.map_inv' h }
end

@[simp] theorem unit_map_eq (u : units R) :
  (units.map (v : R →* ℝ+) u : ℝ+) = v u := rfl

lemma eq_one_of_pow_eq_one {γ: ℝ+} {n: ℕ} (hn: n ≠ 0) (H: γ^n = 1) : γ = 1 := sorry

@[simp] theorem map_neg_one : v (-1) = 1 :=
begin
  apply eq_one_of_pow_eq_one (nat.succ_ne_zero _) (_ : _ ^ 2 = _),
  rw [pow_two, ← v.map_mul],
  show v ((-1) * (-1)) = 1,
  rw [neg_one_mul, neg_neg, v.map_one]
end

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
calc v (-x) = v (-1 * x)   : by simp
        ... = v (-1) * v x : map_mul _ _ _
        ... = v x          : by simp

lemma map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
calc v (x - y) = v (-(y - x)) : by rw show x - y = -(y-x), by abel
           ... = _ : map_neg _ _

lemma map_sub_le_max (x y : R) : v (x - y) ≤ max (v x) (v y) :=
calc v (x-y) = v (x + -y)   : by simp
        ... ≤ max (v x) (v $ -y) : v.map_add _ _
        ... = max (v x) (v y)    : by rw map_neg

lemma map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) :=
begin
  suffices : ¬v (x + y) < max (v x) (v y),
    from or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this,
  intro h',
  wlog vyx : v y < v x using x y,
  { apply lt_or_gt_of_ne h.symm },
  { rw max_eq_left_of_lt vyx at h',
    apply lt_irrefl (v x),
    calc v x = v ((x+y) - y)         : by simp
         ... ≤ max (v $ x + y) (v y) : map_sub_le_max _ _ _
         ... < v x                   : max_lt h' vyx },
  { apply this h.symm,
    rwa [add_comm, max_comm] at h' }
end

lemma map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x :=
begin
  have := valuation.map_add_of_distinct_val v (ne_of_gt h).symm,
  rw max_eq_right (le_of_lt h) at this,
  simpa using this
end

/-- A ring homomorphism S → R induces a map valuation R Γ₀ → valuation S Γ₀ -/
def comap {S : Type u₁} [ring S] (f : S → R) [is_ring_hom f] (v : valuation R) :
  valuation S :=
by refine_struct { to_fun := v ∘ f, .. }; intros;
  simp [is_ring_hom.map_zero f, is_ring_hom.map_one f, is_ring_hom.map_mul f, is_ring_hom.map_add f]

@[simp] lemma comap_id : v.comap (id : R → R) = v := ext $ λ r, rfl

lemma comap_comp {S₁ : Type u₁} [ring S₁] {S₂ : Type u₂} [ring S₂]
(f : S₁ → S₂) [is_ring_hom f] (g : S₂ → R) [is_ring_hom g] :
  v.comap (g ∘ f) = (v.comap g).comap f :=
ext $ λ r, rfl

end basic -- end of section

/-- A valuation is trivial if it maps everything to 0 or 1.-/
def is_trivial [ring R] (v : valuation R) : Prop :=
∀ r:R, v r = 0 ∨ v r = 1

section trivial -- the trivial valuation
variable [comm_ring R]
variables (I : ideal R) [prime : I.is_prime]

/-- The trivial ℝ+-valued valuation associated to a prime ideal S of R. -/
def trivial : valuation R :=
{ to_fun := λ x, if x ∈ I then 0 else 1,
  map_zero' := if_pos I.zero_mem,
  map_one'  := if_neg (assume h, prime.1 (I.eq_top_iff_one.2 h)),
  map_mul'  := λ x y,
    if hx : x ∈ I then by rw [if_pos hx, zero_mul, if_pos (I.mul_mem_right hx)]
    else if hy : y ∈ I then by rw [if_pos hy, mul_zero, if_pos (I.mul_mem_left hy)]
    else have hxy : x * y ∉ I,
    by { assume hxy, replace hxy := prime.mem_or_mem hxy, tauto },
    by rw [if_neg hx, if_neg hy, if_neg hxy, mul_one],
  map_add'  := λ x y, begin
      split_ifs with hxy hx hy _ hx hy;
      try {simp}; try {exact le_refl _},
      { exact hxy (I.add_mem hx hy) }
    end }

lemma trivial_is_trivial (I : ideal R) [hI : I.is_prime] :
  (trivial I).is_trivial :=
begin
  intro r,
  by_cases (r ∈ I),
  left,
  apply if_pos h,
  right,
  apply if_neg h,
end

lemma is_trivial_iff_val_le_one {K : Type*} [division_ring K] {v : valuation K} :
  v.is_trivial ↔ ∀ x:K, v x ≤ 1 :=
begin
  split; intros h x,
  { cases h x; simp *, },
  { contrapose! h, cases h with h₁ h₂,
    by_cases hx : v x ≤ 1,
    { refine ⟨x⁻¹, _⟩,
      rw [v.map_inv'],
      apply (nnreal.lt_inv_iff_mul_lt h₁).2 _,
      rw one_mul,
      apply lt_of_le_of_ne hx h₂,
      { rwa v.ne_zero_iff at h₁, } },
    { push_neg at hx, exact ⟨_, hx⟩ } }
end

end trivial -- end of section


section equiv

variables [field R]
variables (v: valuation R)
variables (v₁: valuation R) (v₂: valuation R)

def is_equivalent: Prop := ∀ a : R, v₁ a < 1 → v₂ a < 1

-- maybe move it to the definition of valuation?
def has_triangular_inequality (v: valuation R): Prop := ∀ (a b : R), v (a + b) ≤ v a + v b

-- yes, we can take powers of positive real numbers by positive real numbers.
instance: has_pow ℝ+ ℝ+ := sorry


-- [@Artin, Theorem 1, Section 1, Chapter 1].
theorem non_trivial_equivalent_valuations_eq_one_implies_eq_one
  (hnontriv: ¬ is_trivial v₁)
  (hequiv: is_equivalent v₁ v₂): ∀ a : R, v₁ a = 1 → v₂ a = 1 := sorry

-- [@Artin, Theorem 2, Section 1, Chapter 1].
theorem non_trivial_equivalent_valuations_exists_a_eq_pow_a
  (hnontriv: ¬ is_trivial v₁)
  (hequiv: is_equivalent v₁ v₂): ∃ a : ℝ+, ∀ x : R, v₂ x = (v₁ x) ^ a := sorry

-- [@Artin, Theorem 3, Section 1, Chapter 1].
theorem all_non_trivial_valuations_are_equivalent_to_valuation_with_triangular_inequality
  (hontriv: ¬ is_trivial v): ∃ v' : valuation R, is_equivalent v v' ∧ has_triangular_inequality v' := sorry

-- show that this induces an equivalence relation over non trivial valuations.

end equiv

section archimedean

variables [field R]
variables (v: valuation R)

-- [@Artin, Section 3, Chapter 1].
def is_archimedean: Prop := ¬ (∀ a : R, v a ≤ 1 → v (1 + a) ≤ 1)

-- [@Artin, Theorem 5, Section 3, Chapter 1].
theorem val_add_le_max_val (hnonarchimedean: ¬ is_archimedean v) (a b: R): v (a + b) ≤ max (v a) (v b) := sorry

-- [@Artin, Corollary 5.1, Section 3, Chapter 1].
lemma val_add_eq (hnonarchimedean: ¬is_archimedean v) (a b: R): v a < v b → v (a + b) = v b := sorry

-- a nice generalization would be to take val_add_eq and use it for an arbitrary sum of N elements.
-- lemma val_sum_eq (hnonarchimedean: ¬is_archimedean v) (f: list R): 

-- [@Artin, Theorem 6, Section 3, Chapter 1].
theorem val_is_nonarchimedean_iff_rat_values_bdd: ¬is_archimedean v ↔ ∃ M: ℝ+, ∀ r : ℤ, v r ≤ M := sorry 

-- [@Artin, Corollary unamed, Section 3, Chapter 1]
lemma fields_with_finite_characteristic_are_nonarchimedean: (ring_char R) > 0 → ∀ v : valuation R, ¬ is_archimedean v := sorry

end archimedean

section supp
variables  [comm_ring R]
variables (v : valuation R)

lemma le_zero_iff {x: ℝ+}: x ≤ 0 ↔ x = 0 :=
begin
  split,
  intro h,
  apply le_antisymm,
  exact h,
  cases x,
  exact x_property,
  intro h,
  rw h,
end

/-- The support of a valuation v : R → ℝ+ is the ideal of R where v vanishes. -/
def supp : ideal R :=
{ carrier := {x | v x = 0},
  zero := map_zero v,
  add  := λ x y hx hy, le_zero_iff.mp $
    calc v (x + y) ≤ max (v x) (v y) : v.map_add x y
               ... ≤ 0               : max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy),
  smul  := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _ }

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 := iff.rfl
-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance : ideal.is_prime (supp v) :=
⟨λ (h : v.supp = ⊤), one_ne_zero $ show (1 : ℝ+) = 0,
from calc 1 = v 1 : v.map_one.symm
        ... = 0   : show (1:R) ∈ supp v, by rw h; trivial,
 λ x y hxy, begin
    show v x = 0 ∨ v y = 0,
    change v (x * y) = 0 at hxy,
    rw [v.map_mul x y] at hxy,
    exact (canonically_ordered_comm_semiring.mul_eq_zero_iff _ _).1 hxy,
  end⟩

/-- v(a)=v(a+s) if s ∈ supp(v). -/
lemma val_add_supp (a s : R) (h : s ∈ supp v) : v (a + s) = v a :=
begin
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a,
  { intros a' s' h', refine le_trans (v.map_add a' s') (max_le (le_refl _) _), simp [h'], },
  apply le_antisymm (aux a s h),
  calc v a = v (a + s + -s) : by simp
       ... ≤ v (a + s)      : aux (a + s) (-s) (by rwa ←ideal.neg_mem_iff at h)
end

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
definition on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → ℝ+ :=
λ q, quotient.lift_on' q v $ λ a b h,
calc v a = v (b + (a - b)) : by simp
     ... = v b             : v.val_add_supp b (a - b) (hJ h)

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
definition on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation J.quotient :=
{ to_fun := v.on_quot_val hJ,
  map_zero' := v.map_zero,
  map_one'  := v.map_one,
  map_mul'  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add'  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
ext $ λ r,
begin
  refine @quotient.lift_on_beta _ _ (J.quotient_rel) v (λ a b h, _) _,
  calc v a = v (b + (a - b)) : by simp
       ... = v b             : v.val_add_supp b (a - b) (hJ h)
end

end supp -- end of section

section supp_comm
variable [comm_ring R]
variables (v : valuation R)

lemma comap_supp {S : Type u₁} [comm_ring S] (f : S → R) [is_ring_hom f] :
  supp (v.comap f) = ideal.comap f v.supp :=
ideal.ext $ λ x,
begin
  rw [mem_supp_iff, ideal.mem_comap, mem_supp_iff],
  refl,
end

lemma self_le_supp_comap (J : ideal R) (v : valuation (quotient J)) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
by rw [comap_supp, ← ideal.map_le_iff_le_comap]; simp

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation J.quotient) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
ext $ by { rintro ⟨x⟩, refl }

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

lemma supp_quot_supp : supp (v.on_quot (le_refl _)) = 0 :=
by rw supp_quot; exact ideal.map_quotient_self _

lemma quot_preorder_comap {J : ideal R} (hJ : J ≤ supp v) :
preorder.lift (ideal.quotient.mk J) (v.on_quot hJ).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, iff.rfl

end supp_comm -- end of section

end valuation
