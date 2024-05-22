import Mathlib

import Clvm.Result
import Clvm.Run


-- "node_applies" means "program does not fail when run for some deep enough depth"
def node_applies (n args: Node) := ∃ k, is_ok (apply_node k n args)


-- quoted_node_applies
example (args: Node): node_applies (Node.pair OP_Q n) args := by
  use 1
  simp [node_applies, is_ok]
  use n
  rfl
