import HexDecodeStdio.Outcome
import HexEncodeStdio.AllocatorOperational

namespace Project.HexEncodeStdio

/-! `ReachesOrOOM` and its composition lemmas live in `HexDecodeStdio.Outcome`,
shared with the decode proofs, and are re-exported under this namespace. -/
export Project.HexDecodeStdio (
  ReachesOrOOM ReachesOrOOM.refl ReachesOrOOM.prepend
  ReachesOrOOM.prependReaches ReachesOrOOM.bind ReachesOrOOM.of_reaches)

end Project.HexEncodeStdio
