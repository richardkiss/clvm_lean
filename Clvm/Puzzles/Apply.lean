import Mathlib

import Clvm.Atom
import Clvm.Coe
import Clvm.Ints.Basic
import Clvm.Node
import Clvm.Run

import Clvm.Puzzles.Casts
import Clvm.Puzzles.Results


section Apply


def map_args (k: Nat) (sp: Node) (env: Node) := map_or_err (fun node ↦ apply_node k node env) sp


@[simp]
def maps_unique_inducts_at (k: Nat) := ∀ sp env, is_ok (map_args k sp env) →
    map_args k sp env = map_args k.succ sp env

@[simp]
def maps_ok_next_at (k: Nat) := ∀ sp env, is_ok (map_args k sp env) → is_ok (map_args k.succ sp env)


lemma ok_op_applies_maps (h_q: op.data ≠ [OP_Q]) :
    is_ok (apply_node k.succ (Node.pair (Node.atom op) sp) env) →
    is_ok (map_args k sp env) := by

  intro h_is_ok
  by_contra h_not_ok
  obtain ⟨ n, h1 ⟩ := not_ok h_not_ok
  simp [map_args] at h1
  simp [apply_node, h_q, h1, is_ok, bind, Except.bind] at h_is_ok



def Except.as_ok  (r: Except β Node) :=
  match r with
  | Except.ok x => x
  | Except.error _ => Node.nil


def map_simple (f : Node → Except (Node × String) Node) (n_list: Node) : Node :=
  match n_list with
  | Node.atom _ => Node.nil
  | Node.pair n rest => Node.pair (f n).as_ok (map_simple f rest)


lemma map_or_err_to_simple (h_ok: is_ok (map_or_err f n)) : map_or_err f n = Except.ok (map_simple f n) := by
  induction n with
  | atom a => simp [map_or_err, map_simple]
  | pair n rest _ h =>

    have h_fn_ok: is_ok (f n) := by
      by_contra h1
      obtain ⟨ n1, h2 ⟩ := not_ok h1
      unfold map_or_err at h_ok
      simp [h2] at h_ok
      cases h_moe: map_or_err f rest with
      | ok _ =>
          rw [h_moe] at h_ok
          unfold is_ok at h_ok
          simp [bind, Except.bind] at h_ok
      | error _ =>
          rw [h_moe] at h_ok
          unfold is_ok at h_ok
          simp [bind, Except.bind] at h_ok

    obtain ⟨ n1, h1 ⟩ := h_fn_ok
    unfold map_or_err
    simp [h1]

    have h_f_rest_ok: is_ok (map_or_err f rest) := by
      by_contra h3
      obtain ⟨ n2, h4 ⟩ := not_ok h3
      unfold map_or_err is_ok at h_ok
      simp [h4, bind, Except.bind] at h_ok

    simp [h_f_rest_ok] at h
    simp [h, h1]
    simp [map_simple, h1, Except.as_ok, bind, Except.bind, pure, Except.pure]


lemma map_or_err_inducts (h_ok: is_ok (map_or_err f (Node.pair n0 tail))) : map_or_err f (Node.pair n0 tail) = Except.ok (Node.pair (f n0).as_ok (map_or_err f tail).as_ok) := by
  have h_tail_ok: is_ok (map_or_err f tail) := by
    by_contra h
    obtain ⟨ n, h1 ⟩ := not_ok h
    simp [map_or_err, map_simple, h1, is_ok, bind, Except.bind] at h_ok

  simp [(map_or_err_to_simple h_ok), (map_or_err_to_simple h_tail_ok), map_simple, Except.as_ok]


lemma map_args_inducts (h_ok: is_ok (map_args k (Node.pair n0 tail) env)) : map_args k (Node.pair n0 tail) env = Except.ok (Node.pair (apply_node k n0 env).as_ok (map_args k tail env).as_ok) := by
  unfold map_args at *
  apply map_or_err_inducts at h_ok
  exact h_ok


@[simp]
def applies_unique_at (k: Nat) := ∀ n env, is_ok (apply_node k n env) → apply_node k n env = apply_node k.succ n env


@[simp]
def applies_unique_to (k0: Nat) := ∀ k ≤ k0, applies_unique_at k


lemma tail_maps_ok: is_ok (map_args k (Node.pair head tail) env) → is_ok (map_args k tail env) := by
  intro h_ok
  by_contra h
  obtain ⟨ n, h1 ⟩ := not_ok h
  apply map_args_inducts at h_ok
  simp [map_args] at *
  simp [map_or_err, h1, bind, Except.bind] at h_ok


lemma head_maps_ok: is_ok (map_args k (Node.pair head tail) env) → is_ok (apply_node k head env) := by
  intro h_ok
  obtain ⟨ r0, h_tail_ok ⟩ := tail_maps_ok h_ok
  simp [map_args] at h_tail_ok
  by_contra h
  obtain ⟨ n, h1 ⟩ := not_ok h
  unfold map_args map_or_err at h_ok
  simp [h_tail_ok, h1, is_ok, bind, Except.bind] at h_ok


lemma applies_unique_at_maps_next_to: applies_unique_at k0 → maps_ok_next_at k0 := by
  simp
  intro h_applies sp env h_is_ok

  induction sp with
  | atom _ => simp [map_args, map_or_err, is_ok]
  | pair n0 n1 _ h_n1 =>

    obtain h_head_ok := (head_maps_ok h_is_ok)
    obtain h_head := h_applies n0 env h_head_ok
    obtain h_tail_ok := h_n1 (tail_maps_ok h_is_ok)

    obtain ⟨ r0, h_head_ok ⟩ := h_head_ok
    obtain ⟨ r1, h_tail_ok ⟩ := h_tail_ok

    rw [h_head_ok] at h_head
    simp [map_args] at *
    simp [map_args, map_or_err]
    simp [h_head, h_tail_ok]
    rw [← h_head]
    simp [is_ok, bind, Except.bind, pure, Except.pure]


lemma applies_unique_at_maps_unique_inducts_at (k0: Nat) : applies_unique_at k0 → maps_unique_inducts_at k0 := by
  simp
  intro h_applies sp env h_is_ok

  have h_maps: maps_ok_next_at k0 := by
    apply applies_unique_at_maps_next_to
    exact h_applies

  simp at h_maps

  induction sp with
  | atom _ => simp [map_args, map_or_err, is_ok]
  | pair n0 n1 _ ih =>
    simp [map_args_inducts h_is_ok]
    simp [map_args_inducts ((h_maps (Node.pair n0 n1) env) h_is_ok)]
    simp [h_applies n0 env (head_maps_ok h_is_ok)]
    simp [ih (tail_maps_ok h_is_ok)]


lemma apply_op_oks {env sp: Node} : is_ok (apply_node k0.succ (Node.pair (Node.atom op) sp) env) →
  op.data = [OP_A] →
  ∃ np nenv term,
    (
      sp = Node.pair np (Node.pair nenv (Node.atom term))
      ∧ is_ok (apply_node k0 ((apply_node k0 np env).as_ok) (apply_node k0 nenv env).as_ok)
    )
  := by
    intro h_is_ok h_a

    have h_q : op.data ≠ [OP_Q] := by
      simp [h_a, OP_A, OP_Q]

    obtain h_map_simple := map_or_err_to_simple (ok_op_applies_maps h_q h_is_ok)

    simp [apply_node, map_or_err, h_a, OP_A, OP_Q, h_map_simple] at h_is_ok

    induction sp with
    | atom a => simp [map_simple, is_ok, Except.err, exactly_two_args, bind, Except.bind] at h_is_ok
    | pair n0 n1 _ _ =>
      induction n1 with
      | atom a => simp [map_simple, is_ok, Except.err, exactly_two_args, bind, Except.bind] at h_is_ok
      | pair nenv n2 _ _ =>
        induction n2 with
        | atom term =>
          use n0, nenv, term
          simp [map_simple]
          simp [map_simple] at h_is_ok
          exact h_is_ok
        | pair n3 n4 _ _ => simp [map_simple, is_ok, Except.err, exactly_two_args, bind, Except.bind] at h_is_ok


lemma applies_unique_at_next (k0: Nat) : applies_unique_at k0 → applies_unique_at k0.succ := by

  intro h_applies n env h_is_ok

  match n with
  | Node.atom a => simp [apply_node, is_ok] at *
  | Node.pair n0 sp =>
    match n0 with
    | Node.pair n2 n3 => simp [apply_node, is_ok]
    | Node.atom op =>
      unfold apply_node
      simp

      have h_maps_unique_at_k0 : maps_unique_inducts_at k0 := by
        apply applies_unique_at_maps_unique_inducts_at
        exact h_applies

      by_cases h_q: op.data = [OP_Q]
      simp [h_q]

      have h_moe_ok : is_ok (map_or_err (fun node ↦ apply_node k0 node env) sp) := by
        exact ok_op_applies_maps h_q h_is_ok

      have h_map_eq : map_or_err (fun node ↦ apply_node k0 node env) sp = map_or_err (fun node ↦ apply_node k0.succ node env) sp := by
        apply h_maps_unique_at_k0 sp env h_moe_ok

      simp [h_q]
      simp [← h_map_eq]
      simp [(map_or_err_to_simple h_moe_ok)]

      by_cases h_a: op.data ≠ [OP_A]
      simp [h_a]

      simp at h_a
      simp [h_a]

      obtain ⟨ n_p, n_env, n_ra, h_sp, h_r_nenv ⟩ := apply_op_oks h_is_ok h_a

      simp [h_sp]
      unfold map_simple map_simple map_simple
      simp [exactly_two_args, bind, Except.bind, is_ok, pure, Except.pure]
      simp [(h_applies (Except.as_ok (apply_node k0 n_p env)) (Except.as_ok (apply_node k0 n_env env)) h_r_nenv)]


end Apply
