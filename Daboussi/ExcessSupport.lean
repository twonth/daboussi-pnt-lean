import Daboussi.ExcessRecurrence
import Daboussi.SmoothIntegrability

open MeasureTheory

namespace Daboussi

theorem excess_eq_zero_below {t : ℝ} (ht : t < 1) (y : ℝ) : excess y t = 0 := by
  have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [excess, smoothM, psi, smoothNumbers, hf]

theorem excess_eq_zero_above {y t : ℝ} (hy : 2 ≤ y) (ht : (primorial y : ℝ) ≤ t) :
    excess y t = 0 := by
  have ht0 : 0 ≤ t := (Nat.cast_nonneg _).trans ht
  unfold excess
  rw [smoothM_support hy ht, abs_zero, zero_div]
  exact max_eq_right (by linarith [div_nonneg (mul_nonneg a_nonneg (psi_nonneg t y)) ht0])

theorem excess_support {y : ℝ} (hy : 2 ≤ y) :
    Function.support (excess y) ⊆ Set.Icc 1 (primorial y : ℝ) := by
  intro t ht
  constructor
  · by_contra h
    exact ht (excess_eq_zero_below (lt_of_not_ge h) y)
  · by_contra h
    exact ht (excess_eq_zero_above hy (le_of_lt (lt_of_not_ge h)))

theorem excess_global_integrable {y : ℝ} (hy : 2 ≤ y) : Integrable (excess y) := by
  have h := (integrable_indicator_iff measurableSet_Icc).mpr (excess_integrable y (primorial y))
  rwa [Set.indicator_eq_self.mpr (excess_support hy)] at h

theorem excess_mul_global_integrable {y : ℝ} (hy : 2 ≤ y) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 1 (primorial y : ℝ))) :
    Integrable (fun t => excess y t * g t) := by
  have h := (integrable_indicator_iff measurableSet_Icc).mpr
    ((excess_integrable y (primorial y)).mul_continuousOn hg isCompact_Icc)
  have hs : Function.support (fun t => excess y t * g t) ⊆ Set.Icc 1 (primorial y : ℝ) := by
    intro t ht
    apply excess_support hy
    intro he
    exact ht (by simp [he])
  rwa [Set.indicator_eq_self.mpr hs] at h

theorem excess_moment_integrable {y : ℝ} (hy : 2 ≤ y) :
    IntegrableOn (fun t => excess y t * Real.log t / t) (Set.Ioi 1) := by
  have hc : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc 1 (primorial y : ℝ)) := by
    apply ContinuousOn.div
    · exact Real.continuousOn_log.mono (fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])
    · exact continuousOn_id
    · intro t ht; linarith [ht.1]
  simpa only [IntegrableOn, mul_div_assoc] using
    (excess_mul_global_integrable hy hc).restrict (s := Set.Ioi (1 : ℝ))

end Daboussi
