import Daboussi.SmoothSupport
import Mathlib.Algebra.Order.Floor.Semifield

open Finset ArithmeticFunction

namespace Daboussi

attribute [local instance] Classical.propDecidable

noncomputable def restrictCoprime (P : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime P then f n else 0, by simp⟩

theorem restrictCoprime_mul (P : ℕ) (f g : ArithmeticFunction ℝ) :
    restrictCoprime P f * restrictCoprime P g = restrictCoprime P (f * g) := by
  ext n
  rw [mul_apply]
  by_cases hn : n.Coprime P
  · simp only [restrictCoprime, coe_mk, if_pos hn, mul_apply]
    apply sum_congr rfl
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    have hc : d.1.Coprime P ∧ d.2.Coprime P := by
      rw [← Nat.coprime_mul_iff_left, he]
      exact hn
    split_ifs <;> simp_all
  · simp only [restrictCoprime, coe_mk, if_neg hn, mul_apply]
    apply sum_eq_zero
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    by_cases h1 : d.1.Coprime P
    · have h2 : ¬ d.2.Coprime P := by
        intro h2
        apply hn
        rw [← he, Nat.coprime_mul_iff_left]
        exact ⟨h1, h2⟩
      simp [h2]
    · simp [h1]

theorem restrictCoprime_one (P : ℕ) : restrictCoprime P 1 = 1 := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp [restrictCoprime]
  · simp [restrictCoprime, one_apply, hn]

noncomputable def smallMu (P : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∣ P then (moebius n : ℝ) else 0, by simp⟩

theorem smallMu_mul_zeta (P : ℕ) :
    smallMu P * (zeta : ArithmeticFunction ℝ) = restrictCoprime P zeta := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hg : n.gcd P ≠ 0 := Nat.gcd_ne_zero_left hn
  have hs : n.divisors.filter (fun d => d ∣ P) = (n.gcd P).divisors := by
    ext d
    simp [Nat.mem_divisors, hn, hg, Nat.dvd_gcd_iff, and_comm]
  rw [coe_mul_zeta_apply]
  simp only [smallMu, coe_mk]
  rw [← sum_filter, hs, divisor_sum_mu]
  simp [restrictCoprime, zeta_apply, hn, Nat.coprime_iff_gcd_eq_one]

/-- The smooth/rough Möbius factorization, derived by Dirichlet convolution.
This is the same splitting identity as the paper's unique-factorization argument. -/
theorem mobius_split (P : ℕ) :
    (moebius : ArithmeticFunction ℝ) = smallMu P * restrictCoprime P moebius := by
  have hi : restrictCoprime P zeta * restrictCoprime P moebius = 1 := by
    rw [restrictCoprime_mul, coe_zeta_mul_coe_moebius, restrictCoprime_one]
  calc
    (moebius : ArithmeticFunction ℝ) =
        (moebius : ArithmeticFunction ℝ) * (restrictCoprime P zeta * restrictCoprime P moebius) := by rw [hi, mul_one]
    _ = ((moebius : ArithmeticFunction ℝ) * (smallMu P * zeta)) * restrictCoprime P moebius := by
      rw [smallMu_mul_zeta, mul_assoc]
    _ = smallMu P * restrictCoprime P moebius := by
      rw [mul_left_comm (moebius : ArithmeticFunction ℝ) (smallMu P) zeta,
        coe_moebius_mul_coe_zeta, mul_one]

theorem smallMu_eq_smooth {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    smallMu (primorial y) n = if Smooth y n then (moebius n : ℝ) else 0 := by
  classical
  by_cases hn : Squarefree n
  · simp only [smallMu, coe_mk, squarefree_smooth_iff_dvd hy hn]
  · simp [smallMu, moebius_eq_zero_of_not_squarefree hn]

theorem sum_smallMu {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, smallMu (primorial y) n) = smoothM x y := by
  simp_rw [smallMu_eq_smooth hy]
  rw [← sum_filter]
  simp only [smoothM, smoothNumbers, ← Icc_add_one_left_eq_Ioc, Nat.zero_add]

/-- The first display in the proof of the smooth comparison proposition. -/
theorem M_split {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    M x = ∑ c ∈ Icc 1 ⌊x⌋₊,
      if c.Coprime (primorial y) then (moebius c : ℝ) * smoothM (x / c) y else 0 := by
  have h := sum_Ioc_mul_eq_sum_sum (restrictCoprime (primorial y) moebius)
    (smallMu (primorial y)) ⌊x⌋₊
  rw [mul_comm (restrictCoprime (primorial y) moebius), ← mobius_split] at h
  have hin (c : ℕ) : (∑ n ∈ Ioc 0 (⌊x⌋₊ / c), smallMu (primorial y) n) =
      smoothM (x / c) y := by
    rw [← Nat.floor_div_natCast]
    exact sum_smallMu hy _
  simp_rw [hin] at h
  simpa only [M, intCoe_apply, restrictCoprime, coe_mk, ite_mul, zero_mul,
    ← Icc_add_one_left_eq_Ioc, Nat.zero_add] using h

theorem abs_M_le_rough_sum {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    |M x| ≤ ∑ c ∈ Icc 1 ⌊x⌋₊,
      if c.Coprime (primorial y) then |smoothM (x / c) y| else 0 := by
  rw [M_split hy]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro c _
  by_cases hc : c.Coprime (primorial y)
  · simp only [if_pos hc, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_mu_le_one c)
  · simp [hc]

end Daboussi
