import Daboussi.SmoothConvolution
import Daboussi.CoprimeCounting

open Finset ArithmeticFunction

namespace Daboussi

theorem floor_div_eq_band {x : ℝ} (hx : 0 ≤ x) {c j : ℕ}
    (hc : 1 ≤ c) (hj : 1 ≤ j) :
    ⌊x / c⌋₊ = j ↔ x / (j + 1) < c ∧ (c : ℝ) ≤ x / j := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [Nat.floor_eq_iff (div_nonneg hx hc0.le)]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hj1).mpr
      have h := (div_lt_iff₀ hc0).mp hhi
      push_cast
      nlinarith
    · apply (le_div_iff₀ hj0).mpr
      have h := (le_div_iff₀ hc0).mp hlo
      nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hc0).mpr
      have h := (le_div_iff₀ hj0).mp hhi
      nlinarith
    · apply (div_lt_iff₀ hc0).mpr
      have h := (div_lt_iff₀ hj1).mp hlo
      push_cast at h
      nlinarith

theorem smoothM_as_bands {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y)
    {c : ℕ} (hc : c ∈ Icc 1 ⌊x⌋₊) :
    |smoothM (x / c) y| = ∑ j ∈ Ico 1 (primorial y),
      if ⌊x / c⌋₊ = j then |smoothM j y| else 0 := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (mem_Icc.mp hc).1
  have hcx : (c : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hc).2).trans (Nat.floor_le hx)
  have hj1 : 1 ≤ ⌊x / c⌋₊ := Nat.le_floor (by
    have h : (1 : ℝ) ≤ x / c := (le_div_iff₀ hc0).mpr (by simpa using hcx)
    simpa using h)
  by_cases hj : ⌊x / c⌋₊ < primorial y
  · have hmem : ⌊x / c⌋₊ ∈ Ico 1 (primorial y) := mem_Ico.mpr ⟨hj1, hj⟩
    have he : smoothM (⌊x / c⌋₊ : ℝ) y = smoothM (x / c) y := by simp [smoothM, smoothNumbers]
    simp [hmem, he]
  · have hP : (primorial y : ℝ) ≤ x / c :=
      (Nat.cast_le.mpr (le_of_not_gt hj)).trans (Nat.floor_le (div_nonneg hx hc0.le))
    rw [smoothM_support hy hP, abs_zero]
    have hnot : ⌊x / c⌋₊ ∉ Ico 1 (primorial y) := by simp [hj]
    simp [hnot]

theorem band_filter_eq {x : ℝ} (hx : 0 ≤ x) {j P : ℕ} (hj : 1 ≤ j) :
    (Icc 1 ⌊x⌋₊).filter (fun c : ℕ => c.Coprime P ∧ ⌊x / (c : ℝ)⌋₊ = j) =
      (Ioc ⌊x / (j + 1)⌋₊ ⌊x / j⌋₊).filter (fun c => c.Coprime P) := by
  ext c
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hc1, hcx⟩, hcp, hfloor⟩
    have hband := (floor_div_eq_band hx hc1 hj).mp hfloor
    exact ⟨⟨(Nat.floor_lt (div_nonneg hx hj1.le)).mpr hband.1, Nat.le_floor hband.2⟩, hcp⟩
  · rintro ⟨⟨hcl, hcu⟩, hcp⟩
    have hc1 : 1 ≤ c := by omega
    have hcl' := (Nat.floor_lt (div_nonneg hx hj1.le)).mp hcl
    have hcu' : (c : ℝ) ≤ x / j := (Nat.cast_le.mpr hcu).trans (Nat.floor_le (div_nonneg hx hj0.le))
    have hxj : x / j ≤ x := by
      apply (div_le_iff₀ hj0).mpr
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith
    exact ⟨⟨hc1, Nat.le_floor (hcu'.trans hxj)⟩, hcp,
      (floor_div_eq_band hx hc1 hj).mpr ⟨hcl', hcu'⟩⟩

theorem abs_M_le_bands {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y) :
    |M x| ≤ ∑ j ∈ Ico 1 (primorial y), |smoothM j y| *
      roughInterval (primorial y) (x / (j + 1)) (x / j) := by
  apply (abs_M_le_rough_sum (by linarith) x).trans_eq
  calc
    (∑ c ∈ Icc 1 ⌊x⌋₊, if c.Coprime (primorial y) then |smoothM (x / c) y| else 0) =
        ∑ c ∈ Icc 1 ⌊x⌋₊, ∑ j ∈ Ico 1 (primorial y),
          if c.Coprime (primorial y) ∧ ⌊x / c⌋₊ = j then |smoothM j y| else 0 := by
      apply sum_congr rfl
      intro c hc
      by_cases hcp : c.Coprime (primorial y)
      · rw [if_pos hcp, smoothM_as_bands hx hy hc]
        apply sum_congr rfl
        intro j _
        split_ifs <;> simp_all
      · simp [hcp]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter, sum_const, nsmul_eq_mul, band_filter_eq hx (mem_Ico.mp hj).1]
      simp only [roughInterval]
      ring

end Daboussi
