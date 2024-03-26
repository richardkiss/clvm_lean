import Mathlib

import Init.Coe
import Init.Data
import Init.Data.ByteArray
import Init.Data.Fin
import Init.Data.Nat
import Init.Data.Nat.Bitwise

import Init.Data.UInt
import Init.Prelude
import Init.Tactics
--import Init.Data.Nat.Lemmas

import Clvm.Atom
import Clvm.Basic
import Clvm.Casts
import Clvm.Coe
import Clvm.Hex
import Clvm.Node
import Clvm.Opcodes
import Clvm.Result
import Clvm.RoundTripInt
import Clvm.Run
import Clvm.Serde
import Clvm.Util

import Std.Classes.Cast
--import Std.Data.Int.Init.Lemmas
import Std.Data.UInt


--import Mathlib.Algebra.EuclideanDomain.Defs
--import Mathlib.Tactic.LibrarySearch
--import Mathlib.Data.Fin.Basic


-- we have here several theorems about running programs

def quote_one : Node := "ff0101"


-- n is a node. We have (a (q . n) 0) => n

theorem run_quote_x_is_x { n: Node } : apply (Node.pair 1 n) Node.nil = Result.ok n := by
  rfl

-- (q . 1).replace("r", n) => (1 . n)

theorem replace_quote_one_r_with_x_is_quote_x { x: Node } : replace quote_one [Replacement.mk "r" x] = Node.pair 1 x := by
  have hq : quote_one = Node.pair 1 1 := by
    rfl
  rw [hq]
  simp [replace]
  have split: split_replacements [{ path := nodepath_for_string "r", replacement := x }] = ( [], [{ path := 1, replacement := x }], none ) := by
    rfl
  rw [split]
  simp


-- try following paths

-- brun '2 (x . y)' => x
theorem follow_path_2 { x y: Node } : apply 2 (Node.pair x y) = Result.ok x := by
  rfl

-- brun '3 (x . y)' => y
theorem follow_path_3 { x y: Node } : apply 3 (Node.pair x y) = Result.ok y := by
  rfl

-- (i (q . 1) 2 3)
def if_example_true : Node := [3, (Node.pair 1 1), 2, 3]

-- brun (i (q . 1) 2 3) (x . y) => x
theorem check_if_true { x y: Node } : apply if_example_true (Node.pair x y) = Result.ok x := by
  rfl


def if_example_false : Node := [3, (Node.pair 1 0), 2, 3]

-- brun (i (q . 0) 2 3) (x . y) => y
theorem check_if_false { x y: Node } : apply if_example_false (Node.pair x y) = Result.ok y := by
  rfl

-- brun (+) n => 0
theorem run_add_nil_is_0 { n: Node } : apply (Node.pair OP_ADD.toNat Node.nil) n = Result.ok 0 := by
  rfl


def cons_example : Node := [4, 2, 3]

-- brun (c 2 3) (x . y) => (x . y)
theorem run_cons { x y: Node } : apply cons_example (Node.pair x y) = Result.ok (Node.pair x y) := by
  rfl

-- brun (f 1) (x . y) => x
theorem run_first { x y: Node } : apply [OP_F.toNat, 1] (Node.pair x y) = Result.ok x := by
  rfl

-- brun (r 1) (x . y) => y
theorem run_rest { x y: Node } : apply [OP_R.toNat, 1] (Node.pair x y) = Result.ok y := by
  rfl


def is_atom (n: Node): Bool := match n with
  | Node.atom _ => true
  | _ => false

-- (l n) => 0 or 1 depending on whether n is an atom
theorem op_list { x: Node } : handle_op_l [x] = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl

-- brun (l 1) x => 0 or 1
theorem run_list { x: Node } : apply [OP_L.toNat, 1] x = Result.ok (if is_atom x then Node.nil else Node.one) := by
  cases x <;> rfl


def strlen_example : Node := [OP_STRLEN.toNat, 1]

-- brun (strlen 1) x => a.size (where a is the atom for x)
theorem run_strlen { a: Atom } : apply strlen_example a = Result.ok (Node.atom a.length) :=
  rfl


-- many theorems will use `int_list_to_node_list` so we make sure they work right

theorem try_int_list_to_node_list { z0 z1 : Int } : (int_list_to_node_list [z0, z1]) = [Node.atom (int_to_atom z0), Node.atom (int_to_atom z1)] := by
  rfl


-- TODO: rewrite using induction on the list rather than the length

theorem try_int_list_to_node_list_general {k : Nat} : (∀ zl : List Int, zl.length ≤ k → (int_list_to_node_list zl) = zl.map int_to_atom) := by
  induction' k with k0 ih
  intro z_list
  intro h_length
  have h_nil: z_list = [] := by
    cases z_list with
    | nil => rfl
    | cons head tail =>
      simp
      unfold List.length at h_length
      linarith
  rw [h_nil]
  rfl
  intro z_list
  intro h_length
  cases z_list with
  | nil => rfl
  | cons z0 z_tail =>
    have h_tail: z_tail.length ≤ k0 := by
      simp [List.length] at h_length
      linarith
    unfold int_list_to_node_list
    unfold List.map
    have h_tail2: (int_list_to_node_list z_tail) = z_tail.map int_to_atom := by
      exact ih z_tail h_tail
    rw [h_tail2]
    rfl



-- we use `node_to_list` a lot in handle_op_xxx so let's prove it works right

def identity (n: Node) : Result Node Node := Result.ok n

theorem node_to_list_on_nil : node_to_list Node.nil identity = Result.ok [] := by
  rfl

-- node_to_list works on a single atom
example (n: Node) : node_to_list (Node.pair n Node.nil) identity = Result.ok [n] := by
  rfl

-- node_to_list works on two atoms
example (n1 n2 : Node) : node_to_list (Node.pair n1 (Node.pair n2 Node.nil)) identity = Result.ok [n1, n2] := by
  rfl


def atoms_only (n: Node) : Result Node Node :=
  match n with
  | Node.atom _ => Result.ok n
  | _ => Result.err n "not an atom"


-- define "rightmost_node" as the atom we hit when we repeatedly go to the right
def rightmost_node (n: Node): Atom :=
  match n with
  | Node.atom a => a
  | Node.pair _ rest => rightmost_node rest

-- adding something to the beginning of an existing list doesn't change the rightmost node
theorem rightmost_idempotent { n1 n2 : Node } : rightmost_node (Node.pair n1 n2) = rightmost_node n2 := by
  rfl


-- define "right_depth" as the distance to the rightmost node
def right_depth (n: Node) : Nat := match n with
  | Node.atom _ => 0
  | Node.pair _ n2 => 1 + (right_depth n2)


-- the depth is at least one if a node is not an atom
example { n1 n2 : Node } : right_depth (Node.pair n1 n2) ≥ 1 := by
  unfold right_depth
  exact Nat.le_add_right 1 (right_depth n2)

-- the depth goes up one at a time
example { n1 n2 : Node } : right_depth (Node.pair n1 n2) = 1 + right_depth n2 := by
  unfold right_depth
  cases n2 <;> rfl

-- prove `node_to_list` works on nil
example : node_to_list Node.nil atoms_only = Result.ok [] := by
  rfl

-- define a new property : "is_nil_terminated_list" which is true if the rightmost node is nil

def is_nil_terminated_list (n: Node): Prop := (rightmost_node n).length = 0

-- adding something to the beginning of an existing list doesn't change the nil-terminated property
theorem nil_terminated_idempotent { n1 n2 : Node } : is_nil_terminated_list (Node.pair n1 n2) = is_nil_terminated_list n2 := by
  rfl


-- the first step for many handle_op_xxx functions is to convert a node to a list of nodes with node_to_node_list_terminator
-- let's prove it works right
lemma node_list_terminator_ind { n1 n2 : Node } : node_to_node_list_terminator (Node.pair n1 n2) = ⟨ n1 :: (node_to_node_list_terminator n2).1, (node_to_node_list_terminator n2).2⟩ := by
  rfl


-- for all nodes, the second element of the result of node_to_node_list_terminator is the rightmost node

theorem node_to_node_list_terminator_ok { n : Node } : (node_to_node_list_terminator n).2 = rightmost_node n := by
  induction' n with atom n1 n2 _ h2
  rfl
  unfold rightmost_node
  rw [← h2]
  rfl



-- now let's work on (node_to_node_list_terminator).1

def alt_node_to_node_list_terminator_without_terminator (n: Node) : (List Node) :=
  match n with
  | Node.atom _ => []
  | Node.pair n1 n2 => n1 :: alt_node_to_node_list_terminator_without_terminator n2


-- we will show that (node_to_node_list_terminator).1 is the same as alt_node_to_node_list_terminator_without_terminator
theorem node_to_node_list_terminator_1 { n : Node } : (node_to_node_list_terminator n).1 = alt_node_to_node_list_terminator_without_terminator n := by
  induction' n with atom n1 n2 _ h2
  rfl
  unfold node_to_node_list_terminator
  simp
  rw [h2]
  rfl


-- and here's the simpler version
theorem node_to_node_list_terminator_rewrite { n : Node } : node_to_node_list_terminator n = ⟨ alt_node_to_node_list_terminator_without_terminator n, rightmost_node n ⟩ := by
  rw [← node_to_node_list_terminator_1, ← node_to_node_list_terminator_ok]


-- now we can prove that node_to_list works on a list of atoms

-- theorem node_to_atoms_only_list_on_one_atom (a: Atom) : node_to_list (Node.pair (Node.atom a) Node.nil) atoms_only = Result.ok [n] := by
--   have h_is_ok : atoms_only (Node.atom a) = Result.ok (Node.atom a) := by rfl


-----
-- some more handle_op_xxx opcodes


-- set_option maxHeartbeats 1000000

-- (l n) => 0 or 1 depending on whether n is an atom

theorem op_sha256 { a: Atom } : handle_op_sha256 [Node.atom a] = Result.ok (Node.atom (sha256 a.data)) := by
  rfl


example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp


example: int_to_atom (11: UInt8).toNat = (11: Int) := by simp



example : (int_to_atom (UInt8.toNat OP_SHA256)) = #[11] := by
  unfold OP_SHA256
  unfold UInt8.toNat
  unfold UInt8.val
  unfold Fin.val
  unfold UInt8.instOfNat
  conv_lhs => simp


theorem cast_helper (u : Nat) : (instNatCastInt.1 u) = u := by simp


example : Int.ofNat (11: UInt8).toNat = (11: Int) := by
  simp

example: Int.ofNat (11: UInt8).val.val = (11: Int) := by simp



def is_ok (f: α → Result β γ) (p: α) := ∃ r, f p = Result.ok r


lemma args_to_int_okay_nil_terminated: is_ok args_to_int n → (is_nil_terminated_list n) := by
  intro h
  obtain ⟨r, h0⟩ := h
  by_contra h1
  unfold is_nil_terminated_list at h1
  unfold args_to_int at h0
  unfold node_to_list at h0
  rw [node_to_node_list_terminator_rewrite] at h0
  simp at h0
  unfold Atom.length at h1
  have hgt: List.length (rightmost_node n).data > 0 := by
    by_contra hgtn
    have hgt0: List.length (rightmost_node n).data = 0 := by
      linarith
    exact h1 hgt0
  simp [hgt] at h0



theorem round_trip_int_cast (zs: List Int) : args_to_int ((node_list_to_node ∘ int_list_to_node_list) zs) = Result.ok zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>

    simp

    unfold int_list_to_node_list
    unfold node_list_to_node
    unfold args_to_int
    unfold node_to_list
    simp only [gt_iff_lt]

    have zzz0: is_nil_terminated_list (node_list_to_node (int_list_to_node_list zs)) := by
      simp at ih
      exact args_to_int_okay_nil_terminated ⟨zs, ih⟩

    have zzz1: List.length (node_to_node_list_terminator (node_list_to_node (int_list_to_node_list zs))).2 = 0 := by
      rw [node_to_node_list_terminator_rewrite]
      congr

    have zzz: (node_to_node_list_terminator (Node.pair (Node.atom (int_to_atom z)) (node_list_to_node (int_list_to_node_list zs)))).2.length = 0 := by
      rw [node_to_node_list_terminator_rewrite]
      congr

    simp [zzz]
    unfold node_to_node_list_terminator
    unfold List.map
    unfold list_result_to_result_list
    simp [atom_to_int_cast]
    unfold only_atoms
    simp

    simp at ih
    unfold args_to_int at ih
    unfold node_to_list at ih
    simp at ih
    simp [zzz1] at ih
    simp [ih]
    exact round_trip_int





theorem run_sha256_atom { a: Atom } : apply [OP_SHA256.toNat, 1] a = Result.ok (Node.atom (sha256 a)) := by
  rfl


theorem run_sha256_two_atoms { a1 a2: Atom } : apply [OP_SHA256.toNat, 2, 5] [a1, a2] = Result.ok (Node.atom (sha256 (a1 ++ a2))) := by
  rfl


theorem run_sha256_three_atoms { a1 a2 a3: Atom } : apply [OP_SHA256.toNat, 2, 5, 11] [a1, a2, a3] = Result.ok (Node.atom (sha256 ((a1 ++ a2) ++ a3))) := by
  rfl


theorem op_add_nil : handle_op_add Node.nil = Result.ok 0 := by rfl


theorem op_add_n_numbers { zs : List Int } : handle_op_add zs = Result.ok (Node.atom (int_to_atom (zs.foldl (fun a b => (a + b)) 0))) := by
  unfold handle_op_add
  rw [round_trip_int_cast]


def quote_node (n: Node) : Node := Node.pair ([OP_Q] : Atom) n


def quoted_nodes (ns : List Node) : Node :=
  match ns with
  | [] => Node.nil
  | n :: ns0 =>
      Node.pair (quote_node n) (quoted_nodes ns0)


#eval quoted_nodes [1, 2, 3]




lemma map_or_err_to_quoted_nodes {hv: v > 0} { f: Node -> Result Node Node } { ns: List Node } : map_or_err (fun n => apply_node v n args) (quoted_nodes ns) = Result.ok (node_list_to_node ns) := by
  induction ns with
  | nil => rfl
  | cons head tail h_tail =>
    simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
    unfold quote_node OP_Q
    simp [atom_cast]
    simp [h_tail]
    unfold apply_node
    have hv0: ¬ v = 0 := by linarith
    simp [hv0]
    rfl


theorem run_add_nil: apply ([OP_ADD.toNat, 0]: Node) (0: Node) = Result.ok 0 := by
  rfl


theorem run_add_one_number {z: Int}: apply ([OP_ADD.toNat, 1]: Node) (z: Node) = Result.ok (z: Node) := by
  simp
  unfold UInt8.toNat OP_ADD
  simp [nat_list_to_int_list, int_list_to_node_list]
  have h16: int_to_atom 16 = [16] := by
    rfl
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h16, h1]
  simp [atom_cast, max_255]
  simp [node_list_to_node]

  -- input arguments are simplified
  unfold apply apply_node
  simp
  unfold OP_Q OP_A Atom.length
  simp
  simp [getElem!]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]

  simp [handle_opcode]

  unfold handle_op_add
  simp [List.foldl, args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]
  congr
  exact round_trip_int


theorem run_add_two_numbers {z1 z2: Int}: apply ([OP_ADD.toNat, 2, 5]: Node) ([z1, z2]: Node) = Result.ok ((z1 + z2): Node) := by
  simp
  unfold UInt8.toNat OP_ADD
  simp [nat_list_to_int_list, int_list_to_node_list]
  have h16: int_to_atom 16 = [16] := by
    rfl
  have h2: int_to_atom 2 = [2] := by
    rfl
  have h5: int_to_atom 5 = [5] := by
    rfl
  rw [h16, h2, h5]
  simp [atom_cast, max_255]
  simp [node_list_to_node]

  -- input arguments are simplified
  unfold apply apply_node
  simp
  unfold OP_Q OP_A Atom.length
  simp
  simp [getElem!]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  simp [handle_opcode]
  simp [handle_op_add]

  unfold List.foldl

  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]
  rw [round_trip_int, round_trip_int]


theorem run_add_two_quoted_numbers {z1 z2: Int}: apply ([((OP_ADD.toNat): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Result.ok ((z1 + z2): Node) := by
  simp
  unfold UInt8.toNat OP_ADD
  simp [node_list_to_node]

  -- input arguments are simplified
  simp [apply, apply_node]
  have h16: int_to_atom 16 = [16] := by
    rfl
  rw [h16]
  simp [atom_cast, max_255, getElem!, OP_Q, OP_A, Atom.length]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  unfold apply_node
  simp
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h1]
  simp [atom_cast, Atom.length, max_255, getElem!, OP_Q, OP_A]

  simp [handle_opcode]
  simp [handle_op_add]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]
  rw [round_trip_int, round_trip_int]


#print axioms run_add_two_quoted_numbers


theorem run_mul_two_quoted_numbers {z1 z2: Int}: apply ([((OP_MUL.toNat): Node), (Node.pair 1 z1), (Node.pair 1 z2)]: Node) Node.nil = Result.ok ((z1 * z2): Node) := by
  simp
  unfold UInt8.toNat OP_MUL
  simp [node_list_to_node]

  -- input arguments are simplified
  simp [apply, apply_node]
  have h18: int_to_atom 18 = [18] := by
    rfl
  rw [h18]
  simp [atom_cast, max_255, getElem!, OP_Q, OP_A, Atom.length]

  simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
  unfold apply_node
  simp
  have h1: int_to_atom 1 = [1] := by
    rfl
  rw [h1]
  simp [atom_cast, Atom.length, max_255, getElem!, OP_Q, OP_A]

  simp [handle_opcode]
  simp [handle_op_mul]
  simp [args_to_int, node_to_list, node_to_node_list_terminator, list_result_to_result_list]
  rw [round_trip_int, round_trip_int]


def node_applies (k: Nat) (n args: Node) := is_ok (fun n => apply_node k n args) n


lemma quoted_node_is_ok (args: Node): node_applies 1 (Node.pair OP_Q n) args := by
  simp [node_applies, is_ok]
  use n
  rfl


lemma map_or_err_is_ok (ns: List Node) (args: Node) : (∀ n ∈ ns, node_applies k n args) → is_ok (map_or_err (fun n ↦ apply_node k n args)) ns := by
  induction ns with
  | nil =>
    simp [node_list_to_node]
    unfold apply_node
    simp [map_or_err, is_ok]
  | cons head tail ih =>
    intros h0
    unfold is_ok
    unfold map_or_err
    simp
    unfold node_list_to_node
    simp
    have hn: ∀ n ∈ tail, node_applies k n args := by
      intros n hn
      exact h0 n (List.mem_cons_of_mem head hn)
    have h_ok: is_ok (map_or_err (fun n ↦ apply_node k n args)) tail := by
      exact ih hn
    unfold is_ok at h_ok
    obtain ⟨r, h1⟩ := h_ok
    rw [h1]
    simp
    have h_head: node_applies k head args := by
      exact h0 head (List.mem_cons_self head tail)
    unfold node_applies is_ok at h_head
    obtain ⟨r1, h2⟩ := h_head
    simp at h2
    use Node.pair r1 r
    rw [h2]



---- unfinished proofs go after this line



lemma concat_of_quoted_nodes_is_okay (ns: List Node) (f: Node): node_applies 2 (Node.pair (Node.atom [OP_CONCAT.toNat]) (quoted_nodes ns)) 0 := by
  unfold UInt8.toNat OP_CONCAT
  simp [atom_cast, max_255]
  simp [node_applies, is_ok]
  obtain ⟨r, h0⟩ := map_or_err_is_ok ns 0
  simp [apply_node]
  simp [Atom.length, OP_Q, OP_A, getElem!]
  induction ns with
  | nil =>
    unfold map_or_err
    unfold quoted_nodes
    simp
    simp [handle_opcode, handle_op_concat]
    simp [node_to_list]
    rw [node_to_node_list_terminator_rewrite]
    simp [alt_node_to_node_list_terminator_without_terminator, rightmost_node]
    simp [list_result_to_result_list]
  | cons head tail ih =>
    unfold map_or_err
    unfold quoted_nodes
    simp
    obtain ⟨r, h0⟩ := ih
    rw [h0]

  unfold quoted_nodes
  rfl


theorem run_add_n_numbers { zs: List Int } : program = (Node.pair ([OP_ADD.toNat] : Atom) (quoted_nodes zs)) → apply program 0 =
    Result.ok (Node.atom (int_to_atom (zs.foldl (fun (a b: Int) => a + b) 0))) := by

  unfold UInt8.toNat OP_ADD
  simp [atom_cast, max_255]

  intro hp
  induction zs with
  | nil =>

    unfold apply apply_node
    simp
    simp [hp]
    simp [Atom.length, OP_Q, OP_A, getElem!]

    rfl

  | cons head tail ih =>

    unfold apply apply_node
    simp
    simp [hp]
    simp [Atom.length, OP_Q, OP_A, getElem!]
    rw [map_or_err_to_quoted_nodes]
    unfold node_list_to_node
    simp
    simp [pure, List.ret]
    simp [handle_opcode]
    simp [handle_op_add]
    simp [args_to_int, node_to_list]
    rw [node_to_node_list_terminator_rewrite]
    simp [alt_node_to_node_list_terminator_without_terminator, rightmost_node]










    simp [map_or_err, apply_node, node_at, atom_to_nat, node_at_wdepth, list_nat_to_nat]
    simp [hp]
    simp [Atom.length, OP_Q, OP_A, getElem!]
    unfold map_or_err
    simp [handle_opcode]



    simp [handle_opcode]
    simp [handle_op_add]
    rfl






    simp [int_to_atom, nat_to_atom, List.map, max_255, List.foldr, List.foldl, List.length, nat_to_atom.inner_func]

    unfold getElem instGetElemArrayNatLtInstLTNatSize Array.size Array.get List.get
    simp

    simp







    simp [apply, apply_node, Node.nil]
    simp [atom_to_nat, node_at, node_at_wdepth, list_nat_to_nat]
    simp





  | cons head tail ih =>
    sorry
