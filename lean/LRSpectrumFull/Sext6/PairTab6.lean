/-
# PairTab6: kernel decision of the grid table for c_1 = 6  [AK, 2026-11-24]
-/
import LRSpectrumFull.Sext6.PairDefs

namespace LRSpectrumFull
namespace Sext6

theorem T2_6 : T2 6 := by decide +kernel

end Sext6
end LRSpectrumFull

#print axioms LRSpectrumFull.Sext6.T2_6
