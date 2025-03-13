-- T1
-- 1.1 proper binary tree

inductive PBT : Type
-- Base case
| p_node : String → PBT
-- Induction steps
| p_family: PBT → PBT → PBT → PBT
-- parent node + left Node + right node  = PBT

open PBT

def PBT_to_String : PBT → String
  -- Base case
  | p_node s => s
  -- Induction steps
  | p_family p l r => PBT_to_String p ++ " "++ PBT_to_String l ++ " ^ " ++ PBT_to_String r ++ " ^ "

instance : ToString PBT where
  toString := PBT_to_String

def A : PBT := p_node "A"
def B : PBT := p_node "B"
def C : PBT := p_node "C"
def D : PBT := p_node "D"
def E : PBT := p_node "E"
def F : PBT := p_node "F"
def G : PBT := p_node "G"
def H : PBT := p_node "H"
def I : PBT := p_node "I"

def ex_PBT : PBT :=
  p_family A (p_family B D (p_family E H I)) (p_family C F G)

#eval toString ex_PBT
