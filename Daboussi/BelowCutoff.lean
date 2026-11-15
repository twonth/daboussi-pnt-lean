import Daboussi.Limsup

namespace Daboussi

/-- The error from replacing floor(t)/t by 1 is at most a/t. -/
theorem floor_error {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ a * (1 - (⌊t⌋₊ : ℝ) / t) ∧ a * (1 - (⌊t⌋₊ : ℝ) / t) ≤ a / t := by
  have ht0 : 0 < t := by linarith
  have hf := Nat.floor_le ht0.le
  have hf' := Nat.lt_floor_add_one t
  have hdiv : (⌊t⌋₊ : ℝ) / t ≤ 1 := (div_le_one ht0).mpr hf
  constructor
  · exact mul_nonneg a_nonneg (by linarith)
  · apply (le_div_iff₀ ht0).mpr
    have hmul := mul_le_mul_of_nonneg_left (show t - (⌊t⌋₊ : ℝ) ≤ 1 by linarith) a_nonneg
    calc
      a * (1 - (⌊t⌋₊ : ℝ) / t) * t = a * (t - (⌊t⌋₊ : ℝ)) := by
        field_simp
      _ ≤ a := by simpa using hmul

theorem deficit_below {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    max (a - |M t| / t) 0 - a / t ≤ deficit y t := by
  have hf := floor_error ht
  have hp := positive_part_sub (a - |M t| / t)
    (a * (1 - (⌊t⌋₊ : ℝ) / t)) hf.1
  have heq : a - |M t| / t - a * (1 - (⌊t⌋₊ : ℝ) / t) =
      a * (⌊t⌋₊ : ℝ) / t - |M t| / t := by ring
  rw [heq] at hp
  unfold deficit
  rw [smoothM_eq_M hty, psi_eq_floor hty]
  linarith [hf.2]

theorem excess_below {t y ε : ℝ} (ht : 1 ≤ t) (hty : t ≤ y)
    (hε : 0 ≤ ε) (hM : |M t| / t ≤ a + ε) :
    excess y t ≤ ε + a / t := by
  have hf := (floor_error ht).2
  unfold excess
  rw [smoothM_eq_M hty, psi_eq_floor hty]
  apply max_le
  · have heq : |M t| / t - a * (⌊t⌋₊ : ℝ) / t =
        |M t| / t - a + a * (1 - (⌊t⌋₊ : ℝ) / t) := by ring
    rw [heq]
    linarith
  · exact add_nonneg hε (div_nonneg a_nonneg (by linarith))

end Daboussi
