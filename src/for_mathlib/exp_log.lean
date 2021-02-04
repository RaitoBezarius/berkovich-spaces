import analysis.special_functions.exp_log

lemma real.log_ne_zero_of_ne_one (x: ℝ) (hx_pos: 0 < x) (hx: x ≠ 1): real.log x ≠ 0 :=
begin
  by_cases (1 < x),
  exact ne_of_gt (real.log_pos h),
  push_neg at h,
  exact ne_of_lt (real.log_neg hx_pos (lt_of_le_of_ne h hx)),
end