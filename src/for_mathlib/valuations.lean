import data.real.basic
import data.real.cau_seq
import .nat_digits
import .list

lemma list.abv_sum_le_sum_abv
  {α β} [ring α] [linear_ordered_field β]
  (abv: α → β)
  [habv: is_absolute_value abv]
  (L: list α): abv (L.sum) ≤ (L.map abv).sum :=
  begin
    induction L with hd tl hl,
    { simp [list.map, is_absolute_value.abv_zero abv] },
    { simp [list.map],
      exact calc abv (hd + tl.sum) ≤ abv hd + abv tl.sum : is_absolute_value.abv_add abv hd tl.sum
      ... ≤ abv hd + (list.map abv tl).sum : add_le_add_left hl _,
    }
  end