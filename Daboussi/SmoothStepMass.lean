import Daboussi.SmoothIntegrability

open Finset MeasureTheory

namespace Daboussi

noncomputable def stepMass (y : ℝ) : ℝ :=
  ∑ j ∈ Ico 1 (primorial y), |smoothM j y| * ((j : ℝ)⁻¹ - ((j : ℝ) + 1)⁻¹)

theorem tailKernel_difference {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    tailKernel j t - tailKernel (j + 1) t =
      if ⌊t⌋₊ = j then t⁻¹ * t⁻¹ else 0 := by
  have hf := Nat.floor_eq_iff' (R := ℝ) (a := t) (show j ≠ 0 by omega)
  unfold tailKernel
  simp only [Set.indicator, Set.mem_Ici]
  simp only [hf]
  split_ifs <;> simp_all <;> linarith

theorem smooth_abs_kernel_expansion {y : ℝ} (hy : 2 ≤ y) {t : ℝ} (ht : 1 ≤ t) :
    |smoothM t y| / t / t = ∑ j ∈ Ico 1 (primorial y),
      |smoothM j y| * (tailKernel j t - tailKernel (j + 1) t) := by
  have hf : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hterm (j : ℕ) (hj : j ∈ Ico 1 (primorial y)) := tailKernel_difference (mem_Ico.mp hj).1 t
  rw [sum_congr rfl (fun (j : ℕ) hj => congrArg (fun z => |smoothM j y| * z) (hterm j hj))]
  simp only [mul_ite, mul_zero]
  by_cases hP : ⌊t⌋₊ < primorial y
  · have hm : ⌊t⌋₊ ∈ Ico 1 (primorial y) := mem_Ico.mpr ⟨hf, hP⟩
    have he : smoothM (⌊t⌋₊ : ℝ) y = smoothM t y := by simp [smoothM, smoothNumbers]
    simp [hm, he]
    ring
  · have hm : ⌊t⌋₊ ∉ Ico 1 (primorial y) := by simp [hP]
    have hPt : (primorial y : ℝ) ≤ t :=
      (Nat.cast_le.mpr (le_of_not_gt hP)).trans (Nat.floor_le (by linarith))
    rw [smoothM_support hy hPt]
    simp [hm]

/-- The finite sum in the comparison proposition is the absolute smooth Möbius mass. -/
theorem smooth_abs_mass_eq_stepMass {y : ℝ} (hy : 2 ≤ y) :
    logMass (fun t => |smoothM t y| / t) = stepMass y := by
  have heq : (fun t => |smoothM t y| / t / t) =ᵐ[volume.restrict (Set.Ioi 1)]
      (fun t => ∑ j ∈ Ico 1 (primorial y),
        |smoothM j y| * (tailKernel j t - tailKernel (j + 1) t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact smooth_abs_kernel_expansion hy ht.le
  unfold logMass
  rw [integral_congr_ae heq, integral_finset_sum]
  · unfold stepMass
    apply sum_congr rfl
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
    have hj0 : (0 : ℝ) < j := by linarith
    rw [integral_const_mul, integral_sub
      (tailKernel_integrable hj0).restrict (tailKernel_integrable (by linarith : (0 : ℝ) < (j : ℝ) + 1)).restrict,
      tailKernel_mass hj1, tailKernel_mass (by linarith : (1 : ℝ) ≤ (j : ℝ) + 1)]
  · intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
    exact (((tailKernel_integrable hj0).restrict).sub
      ((tailKernel_integrable (by linarith : (0 : ℝ) < (j : ℝ) + 1)).restrict)).const_mul _

end Daboussi
