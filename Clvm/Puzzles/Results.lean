import Mathlib

import Clvm.Run

import Clvm.HalfBaked


-- "node_applies" means "program does not fail when run for some deep enough depth"
def node_applies (n args: Node) := ∃ k, is_ok (apply_node k n args)


-- quoted_node_applies
example (args: Node): node_applies (Node.pair OP_Q n) args := by
  simp [node_applies, is_ok]
  use 1, n
  simp [apply_node, small_int_to_atom, OP_Q]
