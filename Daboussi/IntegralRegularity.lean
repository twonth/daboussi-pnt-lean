import Daboussi.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Finset MeasureTheory

namespace Daboussi

attribute [local instance] Classical.propDecidable

theorem smoothM_as_sum (t y : ℝ) :
    smoothM t y = ∑ n ∈ Icc 1 ⌊t⌋₊,
      if Smooth y n then (ArithmeticFunction.moebius n : ℝ) else 0 := by
  classical
  simp only [smoothM, smoothNumbers, sum_filter]

theorem psi_as_sum (t y : ℝ) :
    psi t y = ∑ n ∈ Icc 1 ⌊t⌋₊, if Smooth y n then (1 : ℝ) else 0 := by
  classical
  simp [psi, smoothNumbers]

theorem summatory_integrable (c : ℕ → ℝ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => ∑ n ∈ Icc 1 ⌊t⌋₊, c n) (Set.Icc 1 x) := by
  simpa only [one_mul] using
    (integrableOn_mul_sum_Icc c (m := 1) (a := 1) (b := x) (g := fun _ => (1 : ℝ))
      (by norm_num) continuousOn_const.integrableOn_Icc)

theorem smoothM_integrable (y x : ℝ) :
    IntegrableOn (fun t => smoothM t y) (Set.Icc 1 x) := by
  classical
  simpa only [smoothM_as_sum] using
    summatory_integrable (fun n => if Smooth y n then (ArithmeticFunction.moebius n : ℝ) else 0) x

theorem psi_integrable (y x : ℝ) :
    IntegrableOn (fun t => psi t y) (Set.Icc 1 x) := by
  classical
  simpa only [psi_as_sum] using
    summatory_integrable (fun n => if Smooth y n then (1 : ℝ) else 0) x

theorem continuousOn_inv_Icc (x : ℝ) :
    ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) := by
  exact continuousOn_id.inv₀ fun t ht => (show t ≠ 0 by linarith [ht.1])

theorem excess_log_integrable (y x : ℝ) :
    IntegrableOn (fun t => excess y t / t) (Set.Icc 1 x) := by
  have hMa : IntegrableOn (fun t => |smoothM t y|) (Set.Icc 1 x) := (smoothM_integrable y x).abs
  have hPa : IntegrableOn (fun t => a * psi t y) (Set.Icc 1 x) := (psi_integrable y x).const_mul a
  have hM := hMa.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc
  have hP := hPa.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc
  have hE : IntegrableOn (excess y) (Set.Icc 1 x) := by
    have heq : excess y = ((fun t => |smoothM t y| * t⁻¹) -
        (fun t => a * psi t y * t⁻¹)) ⊔ (0 : ℝ → ℝ) := by
      funext t
      simp [excess, div_eq_mul_inv]
    rw [heq]
    exact (hM.sub hP).sup (integrable_zero ℝ ℝ (volume.restrict (Set.Icc 1 x)))
  simpa only [div_eq_mul_inv] using hE.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc

theorem deficit_log_integrable (y x : ℝ) :
    IntegrableOn (fun t => deficit y t / t) (Set.Icc 1 x) := by
  have hMa : IntegrableOn (fun t => |smoothM t y|) (Set.Icc 1 x) := (smoothM_integrable y x).abs
  have hPa : IntegrableOn (fun t => a * psi t y) (Set.Icc 1 x) := (psi_integrable y x).const_mul a
  have hM := hMa.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc
  have hP := hPa.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc
  have hD : IntegrableOn (deficit y) (Set.Icc 1 x) := by
    have heq : deficit y = ((fun t => a * psi t y * t⁻¹) -
        (fun t => |smoothM t y| * t⁻¹)) ⊔ (0 : ℝ → ℝ) := by
      funext t
      simp [deficit, div_eq_mul_inv]
    rw [heq]
    exact (hP.sub hM).sup (integrable_zero ℝ ℝ (volume.restrict (Set.Icc 1 x)))
  simpa only [div_eq_mul_inv] using hD.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc

end Daboussi
