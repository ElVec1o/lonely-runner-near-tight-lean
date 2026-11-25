/-
# PairTab4: kernel decision of the grid table for c_1 = 4  [AK, 2026-11-24]
-/
import LRSpectrumFull.Sext6.PairDefs

namespace LRSpectrumFull
namespace Sext6

theorem T2_4 : T2 4 := by decide +kernel

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.T2_4
