import Daboussi.Arithmetic
import Daboussi.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Calculus.Deriv.Inv

open Finset ArithmeticFunction MeasureTheory

namespace Daboussi

private theorem sum_from_zero {f : ℕ → ℝ} (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Icc 0 N, f n) = ∑ n ∈ Icc 1 N, f n := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons]
  simp only [hf, zero_add]
  rw [← Icc_add_one_left_eq_Ioc]
  rfl

theorem harmonic_partial_summation (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ) / n) =
      M x / x + ∫ t in (1 : ℝ)..x, M t / t / t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (show t ≠ 0 by linarith [ht.1])).differentiableAt
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (show t ≠ 0 by linarith [ht.1])
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 1 x) := by
    simpa only [deriv_inv'] using hc.integrableOn_Icc
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (moebius n : ℝ)) (by simp) x hdiff hi
  have hs (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, (moebius n : ℝ)) = M t :=
    sum_from_zero (by simp) _
  have hl : (∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * (moebius n : ℝ)) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ) / n := by
    rw [sum_from_zero (by simp)]
    apply sum_congr rfl
    intro n _
    simp [div_eq_mul_inv, mul_comm]
  have he : (fun t : ℝ => deriv (fun u : ℝ => u⁻¹) t *
        ∑ n ∈ Icc 0 ⌊t⌋₊, (moebius n : ℝ)) = (fun t => -(M t / t / t)) := by
    funext t
    rw [hs t, deriv_inv]
    simp [div_eq_mul_inv, pow_two]
    ring
  rw [hl, hs x, he, integral_neg] at h
  rw [intervalIntegral.integral_of_le hx]
  convert h using 1 <;> ring

/-- Equation (signed) of §2, with the paper's strict constant 3. -/
theorem signed_integral_bound (x : ℝ) (hx : 1 ≤ x) :
    |∫ t in (1 : ℝ)..x, M t / t / t| < 3 := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hh := harmonic_mobius_bound ⌊x⌋₊ hN
  rw [← Icc_add_one_left_eq_Ioc] at hh
  simp only [Nat.zero_add] at hh
  have hp := harmonic_partial_summation x hx
  have hnorm : |M x / x| ≤ 1 := by
    rw [abs_div, abs_of_pos (show 0 < x by linarith)]
    exact (div_le_one (by linarith)).mpr (abs_M_le_self (by linarith))
  have htri := abs_add_le (∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ) / n) (-(M x / x))
  rw [abs_neg, hp] at htri
  have hsimp : M x / x + (∫ t in (1 : ℝ)..x, M t / t / t) + -(M x / x) =
      ∫ t in (1 : ℝ)..x, M t / t / t := by ring
  rw [hsimp] at htri
  rw [hp] at hh
  linarith

end Daboussi
