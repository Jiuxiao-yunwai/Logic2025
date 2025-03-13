-- T1
-- 1.1 proper binary tree
inductive Node : Type
| base : String → Node

open Node

def Node_to_String : Node → String
| base str => str

instance : ToString Node where
  toString := Node_to_String

inductive PBT : Type
-- Base case
| p_node : Node → PBT
-- Induction steps
| p_family: Node → PBT → PBT → PBT
-- parent node + left Tree + right Tree  = PBT

open PBT

def PBT_to_String : PBT → String
  -- Base case
  | p_node s => toString s
  -- Induction steps
  | p_family p l r =>
    toString p ++ " " ++ PBT_to_String l ++ " ^ " ++ PBT_to_String r ++ " ^ "

instance : ToString PBT where
  toString := PBT_to_String

def A : Node := base "A"
def B : Node := base "B"
def C : Node := base "C"
def D : Node := base "D"
def E : Node := base "E"
def F : Node := base "F"
def G : Node := base "G"
def H : Node := base "H"
def I : Node := base "I"

def ex_PBT : PBT :=
  p_family A (p_family B (p_node D) (p_family E (p_node H) (p_node I))) (p_family C (p_node F) (p_node G))

#eval toString ex_PBT

def PBT_cal_leaf_node : PBT → Nat
  | p_node _ => 1
  | p_family _ l r => PBT_cal_leaf_node l + PBT_cal_leaf_node r

def PBT_cal_parent_node : PBT → Nat
  | p_node _ => 0
  | p_family _ l r => 1 + PBT_cal_parent_node l + PBT_cal_parent_node r

#eval PBT_cal_leaf_node ex_PBT
#eval PBT_cal_parent_node ex_PBT

theorem PBT_parent_node_equals_to_leaf_node_plus_1 :
  ∀ t : PBT , (PBT_cal_parent_node t) + 1= (PBT_cal_leaf_node t) := by
  intro t
  induction t
  case p_node => rfl
  case p_family p l r IH_l IH_r =>
    simp [PBT_cal_leaf_node, PBT_cal_parent_node, IH_l, IH_r]
    omega
