-- T1
-- 1.1 proper binary tree

inductive PBT : Type
-- Base case
| p_node : String → PBT
-- Induction steps
| p_family: PBT → PBT → PBT → PBT
-- left Node + right node + parent node = PBT

open PBT
