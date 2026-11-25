import LRSpectrumFull.Sext6.K313.Discharge16
import LRSpectrumFull.Sext6.T2Height
import LRSpectrumFull.Sext6.LRC5

/- **Theorem A, no hypotheses.** Six distinct positive integers with `ML ≤ 1/7` are `c · (1,…,6)` up to order.
Chain: `LRC5` (from our `five_speed_spectrum_final`) gives the height bound `21^5`; the 16 kernel-certified clean primes give the box
`21^5 = 4,084,101` (`TheoremBox_P16_T2`); `TheoremA16_LRC5` assembles them. (`Discharge16` also gives
the boxes `41,912,890` and `17,010,000`; they are not used by this assembly.) -/
namespace LRSpectrumFull
namespace Sext6

theorem TheoremA_unconditional : TheoremA := TheoremA16_LRC5 LRC5 ResidueDataSub_P16

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.TheoremA_unconditional
