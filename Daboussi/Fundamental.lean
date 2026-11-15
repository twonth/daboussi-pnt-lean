import Daboussi.ExcessEstimate
import Daboussi.DeficitControl

open Filter
open scoped Topology

namespace Daboussi

/-- The Fundamental Lemma: the logarithmic mean of the deficit tends to zero. -/
theorem fundamental_lemma :
    Tendsto (fun x => fundamentalIntegral x / Real.log x) atTop (nhds 0) :=
  fundamental_of_excess smooth_excess_small deficit_control

/-- The signed-integral estimate and the geometric-block argument force a = 0. -/
theorem limsup_eq_zero : a = 0 :=
  a_zero_of_fundamental fundamental_lemma block_deficit_growth

end Daboussi
