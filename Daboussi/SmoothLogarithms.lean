import Daboussi.SmoothConvolution
import Daboussi.SignedIntegral
import Daboussi.IntegralRegularity

open Finset ArithmeticFunction MeasureTheory
attribute [local instance] Classical.propDecidable

namespace Daboussi

theorem smooth_mul_iff (y : ℝ) (m n : ℕ) :
    Smooth y (m * n) ↔ Smooth y m ∧ Smooth y n := by
  constructor
  · intro h
    exact ⟨fun p hp hd => h p hp (dvd_mul_of_dvd_left hd n),
      fun p hp hd => h p hp (dvd_mul_of_dvd_right hd m)⟩
  · rintro ⟨hm, hn⟩ p hp hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hm p hp hd
    · exact hn p hp hd

noncomputable def restrictSmooth (y : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Smooth y n then f n else 0, by simp⟩

theorem restrictSmooth_mul (y : ℝ) (f g : ArithmeticFunction ℝ) :
    restrictSmooth y f * restrictSmooth y g = restrictSmooth y (f * g) := by
  ext n
  rw [mul_apply]
  by_cases hn : Smooth y n
  · simp only [restrictSmooth, coe_mk, if_pos hn, mul_apply]
    apply sum_congr rfl
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hs : Smooth y d.1 ∧ Smooth y d.2 := (smooth_mul_iff y _ _).mp (he ▸ hn)
    simp [hs.1, hs.2]
  · simp only [restrictSmooth, coe_mk, if_neg hn, mul_apply]
    apply sum_eq_zero
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hs : ¬ (Smooth y d.1 ∧ Smooth y d.2) := by
      rw [← smooth_mul_iff, he]; exact hn
    split_ifs <;> simp_all

theorem sum_restrictSmooth_mu (y x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, restrictSmooth y moebius n) = smoothM x y := by
  simp only [restrictSmooth, coe_mk, intCoe_apply, smoothM, smoothNumbers, sum_filter,
    ← Icc_add_one_left_eq_Ioc, Nat.zero_add]

theorem sum_restrictSmooth_zeta (y x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, restrictSmooth y zeta n) = psi x y := by
  simp only [restrictSmooth, coe_mk, psi, smoothNumbers, ← Icc_add_one_left_eq_Ioc, Nat.zero_add]
  rw [← sum_boole]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [zeta_apply, hn0]

/-- The two logarithmic divisor identities restricted to smooth numbers. -/
theorem smooth_mu_log_sum (y x : ℝ) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, if Smooth y n then -(moebius n : ℝ) * Real.log n else 0) =
      ∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * smoothM (x / d) y := by
  have h := sum_Ioc_mul_eq_sum_sum (restrictSmooth y vonMangoldt)
    (restrictSmooth y moebius) ⌊x⌋₊
  rw [restrictSmooth_mul] at h
  have hin (d : ℕ) : (∑ n ∈ Ioc 0 (⌊x⌋₊ / d), restrictSmooth y moebius n) =
      smoothM (x / d) y := by
    rw [← Nat.floor_div_natCast]; exact sum_restrictSmooth_mu y _
  simp_rw [hin] at h
  rw [← Icc_add_one_left_eq_Ioc] at h
  simp only [Nat.zero_add] at h
  rw [← h]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp only [restrictSmooth, coe_mk, mul_comm vonMangoldt, mul_apply]
  rw [show (∑ d ∈ n.divisorsAntidiagonal, (moebius : ArithmeticFunction ℝ) d.1 * vonMangoldt d.2) =
    -(moebius n : ℝ) * Real.log n by simpa using mobius_log_convolution n (Nat.pos_of_ne_zero hn0)]

theorem smooth_psi_log_sum (y x : ℝ) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, if Smooth y n then Real.log n else 0) =
      ∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * psi (x / d) y := by
  have h := sum_Ioc_mul_eq_sum_sum (restrictSmooth y vonMangoldt)
    (restrictSmooth y zeta) ⌊x⌋₊
  rw [restrictSmooth_mul, vonMangoldt_mul_zeta] at h
  have hin (d : ℕ) : (∑ n ∈ Ioc 0 (⌊x⌋₊ / d), restrictSmooth y zeta n) =
      psi (x / d) y := by
    rw [← Nat.floor_div_natCast]; exact sum_restrictSmooth_zeta y _
  simp_rw [hin] at h
  simpa only [restrictSmooth, coe_mk, log_apply, ← Icc_add_one_left_eq_Ioc, Nat.zero_add] using h

theorem log_partial_summation (c : ℕ → ℝ) (hc : c 0 = 0) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, c n * Real.log n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, c n) * Real.log x -
        ∫ t in 1..x, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / t := by
  have hs (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
      (∑ n ∈ Icc 0 N, f n) = ∑ n ∈ Icc 1 N, f n := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons, hf, zero_add,
      ← Icc_add_one_left_eq_Ioc]
    rfl
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := by
    intro t ht; exact (Real.hasDerivAt_log (by linarith [ht.1])).differentiableAt
  have hi : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    change IntegrableOn (fun t => deriv Real.log t) (Set.Icc 1 x)
    simpa only [Real.deriv_log] using (continuousOn_inv_Icc x).integrableOn_Icc (μ := volume)
  have h := sum_mul_eq_sub_integral_mul₀ c hc x hd hi
  rw [hs _ (by simp), hs c hc] at h
  simp_rw [hs c hc, Real.deriv_log] at h
  rw [intervalIntegral.integral_of_le hx]
  simpa only [mul_comm, div_eq_mul_inv] using h

/-- The signed smooth Möbius logarithmic identity, before taking absolute values. -/
theorem smoothM_log_identity (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    smoothM x y * Real.log x =
      -(∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * smoothM (x / d) y) +
        ∫ t in 1..x, smoothM t y / t := by
  have h := log_partial_summation (fun n => if Smooth y n then (moebius n : ℝ) else 0)
    (by simp) hx
  have he (t : ℝ) : (∑ n ∈ Icc 1 ⌊t⌋₊, if Smooth y n then (moebius n : ℝ) else 0) =
      smoothM t y := (smoothM_as_sum t y).symm
  simp_rw [he] at h
  have hc := smooth_mu_log_sum y x
  have hn : (∑ n ∈ Icc 1 ⌊x⌋₊, if Smooth y n then -(moebius n : ℝ) * Real.log n else 0) =
      -(∑ n ∈ Icc 1 ⌊x⌋₊, (if Smooth y n then (moebius n : ℝ) else 0) * Real.log n) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro n _; split_ifs <;> ring
  rw [hn, h] at hc
  linarith

theorem psi_log_identity (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    psi x y * Real.log x =
      (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * psi (x / d) y) +
        ∫ t in 1..x, psi t y / t := by
  have h := log_partial_summation (restrictSmooth y zeta) (by simp) hx
  have he (t : ℝ) : (∑ n ∈ Icc 1 ⌊t⌋₊, restrictSmooth y zeta n) = psi t y := by
    simpa only [← Icc_add_one_left_eq_Ioc, Nat.zero_add] using sum_restrictSmooth_zeta y t
  simp_rw [he] at h
  have hs : (∑ n ∈ Icc 1 ⌊x⌋₊, restrictSmooth y zeta n * Real.log n) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, if Smooth y n then Real.log n else 0 := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp [restrictSmooth, zeta_apply, hn0]
  rw [hs, smooth_psi_log_sum] at h
  linarith

end Daboussi
