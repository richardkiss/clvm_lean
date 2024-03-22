import Clvm.Atom
import Clvm.Casts
import Clvm.Node
import Clvm.Util


instance : CoeOut Atom Node := ⟨Node.atom⟩

instance : Coe Int Atom := ⟨int_to_atom⟩

instance : Coe Atom Int := ⟨atom_to_int⟩

instance : CoeOut Nat Atom where
  coe := int_to_atom ∘ Int.ofNat


instance : CoeOut Int Atom where
  coe := int_to_atom

instance Atom.instOfNat: OfNat Atom n where
  ofNat := int_to_atom (Int.ofNat n)


def node_list_to_node : List Node → Node
  | [] => Node.nil
  | x::xs => Node.pair x (node_list_to_node xs)


instance : Coe (List Node) Node where
  coe := node_list_to_node


def int_list_to_node_list : List Int → List Node
  | [] => []
  | x::xs => int_to_atom x :: int_list_to_node_list xs


instance : Coe (List Int) Node where
  coe := node_list_to_node ∘ int_list_to_node_list


def nat_list_to_int_list : List Nat → List Int
  | [] => []
  | x::xs => Int.ofNat x :: nat_list_to_int_list xs


instance : Coe (List Nat) Node where
  coe := node_list_to_node ∘ int_list_to_node_list ∘ nat_list_to_int_list


instance : Coe String Node where
  coe := h2n


instance : Coe (List Int) Node where
  coe := node_list_to_node ∘ int_list_to_node_list


instance : Coe (List Atom) Node where
  coe := node_list_to_node ∘ (List.map Node.atom)
