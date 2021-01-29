import data.padics
import data.real.cau_seq
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import data.nat.prime
import data.nat.basic
import tactic.apply
import tactic.linarith
import topology.metric_space.basic

open is_absolute_value

variables (α: ℝ)

def abvs_equiv {β} [ring β] (abv: β → ℝ) (abv': β → ℝ) [is_absolute_value abv] [is_absolute_value abv'] :=
  ∃ α: ℝ, 0 < α ∧ (λ x: β, (abv x) ^ α) = abv'

theorem abvs_equiv_reflexive {β} [ring β]:
  ∀ (abv: β → ℝ) [is_abv: is_absolute_value abv], @abvs_equiv _ _ abv abv is_abv is_abv :=
begin
  intros abv is_abv,
  use [1, by linarith],
  simp,
end

theorem abvs_equiv_symmetric {β} [ring β]:
  ∀ (abv abv': β → ℝ) [abv_abv: is_absolute_value abv] [abv'_abv: is_absolute_value abv'],
    @abvs_equiv _ _ abv abv' abv_abv abv'_abv → @abvs_equiv _ _ abv' abv abv'_abv abv_abv :=
begin
  intros abv abv' abv_abv abv'_abv p,
  rcases p with ⟨ α, zero_lt_α, hα ⟩,
  use [α⁻¹, by simp [zero_lt_α]],
  ext x,
  have abvx_nonneg: 0 ≤ abv x,
  from @abv_nonneg _ _ _ _ abv abv_abv x,
  symmetry,
  calc abv x = abv x ^ (1: ℝ)          : by rw real.rpow_one
    ... = abv x ^ (α * α⁻¹)            : by { simp [(ne.symm ∘ ne_of_lt) zero_lt_α], }
    ... = (abv x ^ α) ^ (α⁻¹)          : by { rw real.rpow_mul abvx_nonneg, }
    ... = ((λ x, abv x ^ α) x) ^ (α⁻¹) : by simp
    ... = (abv' x) ^ (α⁻¹)             : by rw hα,
end


theorem abvs_equiv_transitive {β} [ring β]:
  ∀ (abv abv' abv'': β → ℝ) [abv_abv: is_absolute_value abv] [abv'_abv: is_absolute_value abv']
      [abv''_abv: is_absolute_value abv''],
    @abvs_equiv _ _ abv abv' abv_abv abv'_abv → @abvs_equiv _ _ abv' abv'' abv'_abv abv''_abv →
      @abvs_equiv _ _ abv abv'' abv_abv abv''_abv :=
begin
  intros abv abv' abv'' abv_abv abv'_abv abv''_abv abv_equiv_abv' abv'_equiv_abv'',
  rcases abv_equiv_abv' with ⟨ α, zero_lt_α, hα ⟩,
  rcases abv'_equiv_abv'' with ⟨ γ, zero_lt_γ, hγ ⟩,
  use [α * γ, by simp [zero_lt_α, zero_lt_γ]],
  ext x,
  have abvx_nonneg: 0 ≤ abv x,
  from @abv_nonneg _ _ _ _ abv abv_abv x,
  rw real.rpow_mul abvx_nonneg,
  rw [← hγ, ← hα],
end
