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


instance : Coe Int Node where
  coe := λ n => Node.atom (int_to_atom n)


def nat_list_to_int_list (ns: List Nat) := ns.map Int.ofNat


instance : Coe (List Nat) Node where
  coe := node_list_to_node ∘ int_list_to_node_list ∘ nat_list_to_int_list


instance : Coe (List Int) Node where
  coe := node_list_to_node ∘ int_list_to_node_list


instance : Coe (List Atom) Node where
  coe := node_list_to_node ∘ (List.map Node.atom)


instance : CoeOut (List Nat) (List UInt8) where
  coe := List.map UInt8.ofNat
