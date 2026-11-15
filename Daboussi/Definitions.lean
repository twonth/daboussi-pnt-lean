import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.LiminfLimsup

/-! The functions in Pollack's manuscript. All sums start at 1. -/

open Finset Filter MeasureTheory

namespace Daboussi

/-- The ordinary summatory Möbius function, with a real argument. -/
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)

/-- Every prime divisor of `n` is at most `y`. In particular, 1 is smooth. -/
def Smooth (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ y

noncomputable def smoothNumbers (x y : ℝ) : Finset ℕ := by
  classical
  exact (Icc 1 ⌊x⌋₊).filter (Smooth y)

noncomputable def smoothM (x y : ℝ) : ℝ :=
  ∑ n ∈ smoothNumbers x y, (ArithmeticFunction.moebius n : ℝ)

noncomputable def psi (x y : ℝ) : ℝ := (smoothNumbers x y).card

noncomputable def a : ℝ := limsup (fun x : ℝ => |M x| / x) atTop

noncomputable def excess (y t : ℝ) : ℝ :=
  max (|smoothM t y| / t - a * psi t y / t) 0

noncomputable def deficit (y t : ℝ) : ℝ :=
  max (a * psi t y / t - |smoothM t y| / t) 0

/-- Integration against dt/t on [1,∞). -/
noncomputable def logMass (f : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ), f t / t

noncomputable def fundamentalIntegral (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, max (a - |M t| / t) 0 / t

end Daboussi
