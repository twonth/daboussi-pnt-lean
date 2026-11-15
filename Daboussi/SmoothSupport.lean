import Daboussi.Arithmetic
import Daboussi.Basic
import Mathlib.NumberTheory.SmoothNumbers

open Finset ArithmeticFunction

namespace Daboussi

noncomputable def smallPrimes (y : ℝ) : Finset ℕ := Nat.primesLE ⌊y⌋₊
noncomputable def primorial (y : ℝ) : ℕ := ∏ p ∈ smallPrimes y, p

theorem mem_smallPrimes {y : ℝ} (hy : 0 ≤ y) (p : ℕ) :
    p ∈ smallPrimes y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  simp only [smallPrimes, Nat.mem_primesLE]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨hp, (Nat.cast_le.mpr hle).trans (Nat.floor_le hy)⟩
  · rintro ⟨hp, hpy⟩
    exact ⟨Nat.le_floor hpy, hp⟩

theorem primorial_ne_zero (y : ℝ) : primorial y ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro p hp
  exact (Nat.mem_primesLE.mp hp).2.ne_zero

theorem primorial_primeFactors (y : ℝ) : (primorial y).primeFactors = smallPrimes y := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (Nat.mem_primesLE.mp hp).2

theorem smooth_iff_factored {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    Smooth y n ↔ n ∈ Nat.factoredNumbers (smallPrimes y) := by
  rw [Nat.mem_factoredNumbers']
  constructor
  · intro h p hp hpn
    exact (mem_smallPrimes hy p).mpr ⟨hp, h p hp hpn⟩
  · intro h p hp hpn
    exact ((mem_smallPrimes hy p).mp (h p hp hpn)).2

theorem squarefree_smooth_iff_dvd {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : Squarefree n) :
    Smooth y n ↔ n ∣ primorial y := by
  rw [smooth_iff_factored hy, Nat.mem_factoredNumbers_iff_primeFactors_subset]
  have hd := Nat.prod_primeFactors_dvd_iff (n := n) (primorial_ne_zero y)
  rw [Nat.prod_primeFactors_of_squarefree hn, primorial_primeFactors] at hd
  exact ⟨fun h => hd.mpr h.2, fun h => ⟨hn.ne_zero, hd.mp h⟩⟩

theorem smooth_of_dvd_primorial {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : n ∣ primorial y) :
    Smooth y n := by
  rw [smooth_iff_factored hy, Nat.mem_factoredNumbers_iff_primeFactors_subset]
  refine ⟨ne_zero_of_dvd_ne_zero (primorial_ne_zero y) hn, ?_⟩
  have h := Nat.primeFactors_mono hn (primorial_ne_zero y)
  simpa only [primorial_primeFactors] using h

theorem primorial_gt_one {y : ℝ} (hy : 2 ≤ y) : 1 < primorial y := by
  have hm : 2 ∈ smallPrimes y := (mem_smallPrimes (by linarith) 2).mpr ⟨Nat.prime_two, by simpa using hy⟩
  have hd : 2 ∣ primorial y := dvd_prod_of_mem (fun p => p) hm
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (primorial_ne_zero y)) hd
  omega

/-- Only squarefree smooth integers contribute, hence the sum is supported below P. -/
theorem smoothM_support {y t : ℝ} (hy : 2 ≤ y) (ht : (primorial y : ℝ) ≤ t) :
    smoothM t y = 0 := by
  classical
  have hy0 : 0 ≤ y := by linarith
  have hP0 := primorial_ne_zero y
  have hP1 := primorial_gt_one hy
  have hsubset : (primorial y).divisors ⊆ smoothNumbers t y := by
    intro n hn
    have hnd := Nat.dvd_of_mem_divisors hn
    have hn0 := Nat.pos_of_mem_divisors hn
    have hnP := Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) hnd
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hn0, Nat.le_floor ((Nat.cast_le.mpr hnP).trans ht)⟩,
      smooth_of_dvd_primorial hy0 hnd⟩
  have heq : smoothM t y = ∑ n ∈ (primorial y).divisors, (moebius n : ℝ) := by
    unfold smoothM
    symm
    apply sum_subset hsubset
    intro n hn hnot
    have hs : Smooth y n := (mem_filter.mp hn).2
    have hnsq : ¬Squarefree n := by
      intro hsq
      have hnd := (squarefree_smooth_iff_dvd hy0 hsq).mp hs
      exact hnot (Nat.mem_divisors.mpr ⟨hnd, hP0⟩)
    simp [moebius_eq_zero_of_not_squarefree hnsq]
  rw [heq, divisor_sum_mu]
  simp [show primorial y ≠ 1 by omega]

end Daboussi
