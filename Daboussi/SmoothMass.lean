import Daboussi.SmoothHarmonic
import Daboussi.TailKernels
import Mathlib.MeasureTheory.Function.Floor

open Finset MeasureTheory

namespace Daboussi

theorem measurable_psi (y : ℝ) : Measurable (fun t => psi t y) := by
  classical
  let f : ℕ → ℝ := fun N => ((Icc 1 N).filter (Smooth y)).card
  change Measurable (fun t : ℝ => f ⌊t⌋₊)
  exact (measurable_of_countable f).comp Nat.measurable_floor

theorem smooth_kernel_hasSum {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    HasSum (fun n : Nat.factoredNumbers (smallPrimes y) => tailKernel (n : ℕ) t)
      (psi t y / t / t) := by
  classical
  let S := Nat.factoredNumbers (smallPrimes y)
  let s : Finset S := (Icc 1 ⌊t⌋₊).subtype (fun n => n ∈ S)
  have hnpos (n : S) : 1 ≤ (n : ℕ) := Nat.pos_of_ne_zero n.prop.1
  have hzero : ∀ n : S, n ∉ s → tailKernel (n : ℕ) t = 0 := by
    intro n hn
    have hnt : ¬((n : ℕ) : ℝ) ≤ t := by
      intro hle
      apply hn
      exact mem_subtype.mpr (mem_Icc.mpr ⟨hnpos n, Nat.le_floor hle⟩)
    exact Set.indicator_of_notMem hnt _
  have hterm (n : S) (hn : n ∈ s) : tailKernel (n : ℕ) t = t⁻¹ * t⁻¹ := by
    have hmem := mem_Icc.mp (mem_subtype.mp hn)
    have ht0 : 0 ≤ t := by
      by_contra ht
      have hz : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have hle : ((n : ℕ) : ℝ) ≤ t :=
      (Nat.cast_le.mpr hmem.2).trans (Nat.floor_le ht0)
    exact Set.indicator_of_mem hle _
  have hcard : (s.card : ℝ) = psi t y := by
    simp only [s, card_subtype, psi, smoothNumbers]
    congr 2
    ext n
    simp only [mem_filter]
    rw [smooth_iff_factored hy]
  have hsum : (∑ n ∈ s, tailKernel (n : ℕ) t) = psi t y / t / t := by
    rw [sum_congr rfl hterm]
    simp only [sum_const, nsmul_eq_mul, hcard]
    ring
  exact hsum ▸ hasSum_sum_of_ne_finset_zero hzero

theorem smooth_mass_integrable {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun t => psi t y / t / t) (Set.Ioi 1) := by
  let S := Nat.factoredNumbers (smallPrimes y)
  have hp (n : S) : (1 : ℝ) ≤ (n : ℕ) := by
    exact_mod_cast (Nat.pos_of_ne_zero n.prop.1)
  have hF (n : S) : Integrable (tailKernel (n : ℕ)) (volume.restrict (Set.Ioi 1)) :=
    (tailKernel_integrable (by linarith [hp n])).restrict
  apply integrable_nonneg_series hF (fun n t => tailKernel_nonneg _ _) (smooth_kernel_hasSum hy)
  · exact ((measurable_psi y).div measurable_id |>.div measurable_id).aestronglyMeasurable
  · have he : (fun n : S => ∫ t in Set.Ioi (1 : ℝ), tailKernel (n : ℕ) t) =
        (fun n : S => ((n : ℕ) : ℝ)⁻¹) := by
      funext n
      exact tailKernel_mass (hp n)
    rw [he]
    exact smooth_harmonic_summable y

/-- Equation (positive-mass), proved by summing the kernels 1_[n,∞)(t)/t². -/
theorem smooth_mass_eq_euler_product {y : ℝ} (hy : 0 ≤ y) :
    logMass (fun t => psi t y / t) = ∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let S := Nat.factoredNumbers (smallPrimes y)
  have hp (n : S) : (1 : ℝ) ≤ (n : ℕ) := by
    exact_mod_cast (Nat.pos_of_ne_zero n.prop.1)
  have hF (n : S) : Integrable (tailKernel (n : ℕ)) (volume.restrict (Set.Ioi 1)) :=
    (tailKernel_integrable (by linarith [hp n])).restrict
  have he (n : S) : (∫ t in Set.Ioi (1 : ℝ), tailKernel (n : ℕ) t) = ((n : ℕ) : ℝ)⁻¹ :=
    tailKernel_mass (hp n)
  have hn : Summable (fun n : S => ∫ t in Set.Ioi (1 : ℝ), ‖tailKernel (n : ℕ) t‖) := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (tailKernel_nonneg _ _), he]
    exact smooth_harmonic_summable y
  have hswap := integral_tsum_of_summable_integral_norm hF hn
  have hfun : (fun t => ∑' n : S, tailKernel (n : ℕ) t) = (fun t => psi t y / t / t) := by
    funext t
    exact (smooth_kernel_hasSum hy t).tsum_eq
  rw [hfun] at hswap
  simp_rw [he] at hswap
  exact hswap.symm.trans (smooth_harmonic_hasSum y).tsum_eq

end Daboussi
