import Ventus.Arith.MultiplierCSA

namespace Ventus.Arith

-- 复现 mcsaColumns_map_length 的末段，分步隔离 maxRecDepth
example (a b : BitVec 33) (i : Nat) (h2 : i < mcsaInitLens33.length) : True := by
  have hstep : mcsaInitLens33[i]'h2
      = ((mulRowIndices 33).filter fun i' => mcsaRowCover33 i' i).length := by
    unfold mcsaInitLens33
    rw [List.getElem_map, List.getElem_range]
  trivial

end Ventus.Arith
