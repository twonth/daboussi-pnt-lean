import Daboussi.Basic

open MeasureTheory

namespace Daboussi

/-- Proposition 3 rewritten as a comparison of positive and negative parts.
The integrability assumptions are stated explicitly, because Lean's Bochner
integral takes the value zero for a nonintegrable function. -/
theorem balance_of_comparison (y : ℝ)
    (hE : IntegrableOn (fun t => excess y t / t) (Set.Ioi 1))
    (hD : IntegrableOn (fun t => deficit y t / t) (Set.Ioi 1))
    (hcomp : 0 ≤ logMass (fun t => |smoothM t y| / t - a * psi t y / t)) :
    logMass (deficit y) ≤ logMass (excess y) := by
  have heq : (fun t => (|smoothM t y| / t - a * psi t y / t) / t) =
      (fun t => excess y t / t - deficit y t / t) := by
    funext t
    rw [← excess_sub_deficit y t, sub_div]
  unfold logMass at *
  rw [heq, integral_sub hE hD] at hcomp
  linarith

end Daboussi
