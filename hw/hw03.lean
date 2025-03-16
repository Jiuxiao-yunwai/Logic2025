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


-- 1.2 SpecialString

--
-- ANS here !
--
inductive BS101Even : Type
  -- "101"+"1"/"0"
  | base : Bool → BS101Even
  -- Str + 2
  | append2 : BS101Even → Bool → Bool → BS101Even
open BS101Even

inductive BSMod5 : Type
  -- 2
  | base : Bool → Bool → BSMod5
  -- 2+5n
  | append5 : BSMod5 → Bool → Bool → Bool → Bool → Bool → BSMod5
open BSMod5

inductive BSEvenZeros : Type
  -- Empty
  | base : BSEvenZeros

  | append1 : BSEvenZeros →  BSEvenZeros
  | append00: BSEvenZeros →  BSEvenZeros
open BSEvenZeros
-- ANS end

inductive BinaryString : Type where
  | empty : BinaryString
  | append : BinaryString → Bool → BinaryString

open BinaryString

def BinaryString.toString : BinaryString → String
  | empty => ""
  | append s b => toString s ++ (if b then "1" else "0")

def exStr1 : BinaryString := append (append (append (append empty true) false) true) false
#eval toString exStr1

def BinaryString.length : BinaryString → Nat
  | empty => 0
  | append s _ => 1 + length s
#eval exStr1.length

def BinaryString.countZeros : BinaryString → Nat
  | empty => 0
  | append s b => (if b then 0 else 1) + countZeros s
#eval exStr1.countZeros

def BS101Even.toBinaryString : BS101Even → BinaryString
  | .base b => append (append (append (append empty true) false) true) b
  | .append2 s b1 b2 => append (append s.toBinaryString b1) b2

def BSMod5.toBinaryString : BSMod5 → BinaryString
  | .base b1 b2 => append (append empty b1) b2
  | .append5 s b1 b2 b3 b4 b5 =>
    append (append (append (append (append s.toBinaryString b1) b2) b3) b4) b5

def BSEvenZeros.toBinaryString : BSEvenZeros → BinaryString
  | .base => empty
  | .append1 s => append s.toBinaryString true
  | .append00 s => append (append s.toBinaryString false) false

-- emamples

-- "101" + true = "1011"
def bs101_1 : BS101Even := base true
#eval bs101_1.toBinaryString.toString
-- "101" + false = "1010"
def bs101_2 : BS101Even := .base false
#eval bs101_2.toBinaryString.toString
-- "101010"
def bs101_3 : BS101Even := .append2 bs101_2 true false
#eval bs101_3.toBinaryString.toString

-- "10"
def bsMod5_1 : BSMod5 := base true false
#eval bsMod5_1.toBinaryString.toString
-- "1000000"
def bsMod5_2 : BSMod5 := append5 bsMod5_1 false false false false false
#eval bsMod5_2.toBinaryString.toString
-- "100000011111"
def bsMod5_3 : BSMod5 := .append5 bsMod5_2 true true true true true
#eval bsMod5_3.toBinaryString.toString

-- ""
def evenZeros1 : BSEvenZeros := base
#eval evenZeros1.toBinaryString.toString
-- "00"
def evenZeros2 : BSEvenZeros := .append00 evenZeros1
#eval evenZeros2.toBinaryString.toString
-- "001"
def evenZeros3 : BSEvenZeros := .append1 evenZeros2
#eval evenZeros3.toBinaryString.toString
-- "00100"
def evenZeros4 : BSEvenZeros := .append00 evenZeros3
#eval evenZeros4.toBinaryString.toString

-- Proof
theorem zero_count_parity :
  ∀ (s : BinaryString), ( (countZeros s) % 2 = 0 ) ∨ ( (countZeros s) % 2 = 1) := by
  intro s
  induction s
  case empty =>
    simp [countZeros]
  case append s b ih =>
    -- 归纳步骤：假设对s命题成立（ih），考虑追加字符b后的新字符串
    induction b
    case true =>
      simp [countZeros, ih]  -- 简化，直接应用归纳假设
    case false =>
      -- 若追加的是false（0），0的个数加1
      induction ih   -- 根据归纳假设分情况讨论
      case inl h_even =>
        -- 情况1：s中0的个数是偶数（countZeros s % 2 = 0）
        simp [countZeros, h_even, Nat.add_mod]
        <;> omega
      case inr h_odd =>
        -- 情况2：s中0的个数是奇数（countZeros s % 2 = 1）
        simp [countZeros, h_odd, Nat.add_mod]
        <;> omega
