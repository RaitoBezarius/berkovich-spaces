import analysis.special_functions.exp_log

lemma real.log_ne_zero_of_ne_one (x: ℝ) (hx_pos: 0 < x) (hx: x ≠ 1): real.log x ≠ 0 :=
begin
  by_cases (1 < x),
  exact ne_of_gt (real.log_pos h),
  push_neg at h,
  exact ne_of_lt (real.log_neg hx_pos (lt_of_le_of_ne h hx)),
end

lemma log_inj_pos {x y: ℝ} (x_pos: 0 < x) (y_pos: 0 < y):
  real.log x = real.log y → x = y :=
λ h, le_antisymm
  ((real.log_le_log x_pos y_pos).1 $ le_of_eq h)
  ((real.log_le_log y_pos x_pos).1 $ le_of_eq $ eq.symm h)
