import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! The two Möbius inversion identities used in §§2 and 4. -/

open Finset ArithmeticFunction

namespace Daboussi

theorem divisor_sum_mu (n : ℕ) :
    (∑ d ∈ n.divisors, (moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, one_apply] using h

/-- Equation (muchebyshev), expressed with the divisor antidiagonal.
The support of von Mangoldt is exactly the positive prime powers. -/
theorem mobius_log_convolution (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisorsAntidiagonal,
      (moebius d.1 : ℝ) * vonMangoldt d.2) = -(moebius n : ℝ) * Real.log n := by
  apply (sum_eq_iff_sum_mul_moebius_eq (f := fun n => -(moebius n : ℝ) * Real.log n)
    (g := fun n => vonMangoldt n)).mp ?_ n hn
  intro m _
  simpa only [neg_mul, sum_neg_distrib, neg_neg, log_apply] using
    congrArg Neg.neg (sum_moebius_mul_log_eq (n := m))

/-- Summing the divisor identity: the floor-weighted Möbius sum equals 1. -/
theorem mobius_floor_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Ioc 0 N, (moebius d : ℝ) * (N / d : ℕ)) = 1 := by
  have h := sum_Ioc_mul_zeta_eq_sum (moebius : ArithmeticFunction ℝ) N
  rw [coe_moebius_mul_coe_zeta] at h
  simp only [intCoe_apply] at h
  rw [← h]
  simp [one_apply, hN]

/-- The bounded harmonic Möbius sum at the start of §2. -/
theorem harmonic_mobius_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Ioc 0 N, (moebius d : ℝ) / d| < 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have herr (d : ℕ) (hd : d ∈ Ioc 0 N) :
      |(moebius d : ℝ) * ((N : ℝ) / d - (N / d : ℕ))| < 1 := by
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hlo : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hmod : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd0
    have hid : (d : ℝ) * (N / d : ℕ) + (N % d : ℕ) = N := by
      exact_mod_cast Nat.div_add_mod N d
    have hhi : (N : ℝ) / d - (N / d : ℕ) < 1 := by
      have hdiv := (div_lt_iff₀ hdR).mpr (show (N : ℝ) < ((N / d : ℕ) + 1) * d by nlinarith)
      linarith
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hmu : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
    exact (mul_le_of_le_one_left (sub_nonneg.mpr hlo) hmu).trans_lt hhi
  have hsum : |∑ d ∈ Ioc 0 N,
      (moebius d : ℝ) * ((N : ℝ) / d - (N / d : ℕ))| < N := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, |(moebius d : ℝ) * ((N : ℝ) / d - (N / d : ℕ))| :=
        abs_sum_le_sum_abs _ _
      _ < ∑ _d ∈ Ioc 0 N, (1 : ℝ) := by
        apply sum_lt_sum (fun d hd => (herr d hd).le)
        exact ⟨1, mem_Ioc.mpr ⟨by omega, hN⟩, herr 1 (mem_Ioc.mpr ⟨by omega, hN⟩)⟩
      _ = N := by simp
  have hid : (N : ℝ) * (∑ d ∈ Ioc 0 N, (moebius d : ℝ) / d) - 1 =
      ∑ d ∈ Ioc 0 N, (moebius d : ℝ) * ((N : ℝ) / d - (N / d : ℕ)) := by
    rw [← mobius_floor_sum N hN, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [← hid] at hsum
  have htri := abs_add_le
    ((N : ℝ) * (∑ d ∈ Ioc 0 N, (moebius d : ℝ) / d) - 1) 1
  simp only [sub_add_cancel, abs_one, abs_mul, abs_of_pos hNpos] at htri
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end Daboussi
