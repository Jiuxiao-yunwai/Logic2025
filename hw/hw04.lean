-- Before Question
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Bool.Basic
set_option linter.unnecessarySeqFocus false

inductive WFF : Type where
  | p_atm : String → WFF
  | p_not : WFF → WFF
  | p_and : WFF → WFF → WFF
  | p_or  : WFF → WFF → WFF
  | p_imp : WFF → WFF → WFF
  | p_iff : WFF → WFF → WFF

open WFF

def WFF_to_String : WFF → String
  -- Base case
  | p_atm s   => s
  -- Induction steps
  | p_not φ   => "(¬" ++ WFF_to_String φ ++  ")"
  | p_and φ ψ => "(" ++ WFF_to_String φ ++ " ∧ " ++ WFF_to_String ψ ++ ")"
  | p_or  φ ψ => "(" ++ WFF_to_String φ ++ " ∨ " ++ WFF_to_String ψ ++ ")"
  | p_imp φ ψ => "(" ++ WFF_to_String φ ++ " → " ++ WFF_to_String ψ ++ ")"
  | p_iff φ ψ => "(" ++ WFF_to_String φ ++ " ↔ " ++ WFF_to_String ψ ++ ")"

/-- Utility function for fancy outputs --/
instance : ToString WFF where
  toString := WFF_to_String

-- T1

def v_atom (S : Finset String) (s : String) : Bool :=
  if s ∈ S then true else false

def v (v_atom : String → Bool) : WFF → Bool
  | p_atm s   => v_atom s
  | p_not φ   => not (v v_atom φ)
  | p_and φ ψ => and (v v_atom φ) (v v_atom ψ)
  | p_or  φ ψ => or (v v_atom φ) (v v_atom ψ)
  | p_imp φ ψ => or (not (v v_atom φ)) (v v_atom ψ)
  | p_iff φ ψ => (v v_atom φ) = (v v_atom ψ)

theorem T1 (v_atom : String → Bool) (φ ψ χ : WFF) :
  v v_atom (p_and φ (p_or ψ χ)) = v v_atom (p_or (p_and φ ψ) (p_and φ χ)) := by
  -- 合并简化规则，避免重复应用
  simp [v, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm, Bool.or_assoc, Bool.or_comm,
    Bool.or_left_comm, Bool.and_or_distrib_left]

-- T2
theorem T2 (v_atoms : String → Bool) (ϕ ψ : WFF) :
  v v_atoms (p_iff ϕ ψ) = v v_atoms (p_and (p_imp ϕ ψ) (p_imp ψ ϕ)) := by
  simp [v, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm, Bool.or_assoc, Bool.or_comm,
    Bool.or_left_comm, Bool.and_or_distrib_left]
  -- 通过逻辑等价式证明等式成立
  <;> cases v v_atoms ϕ
  <;> cases v v_atoms ψ
  <;> rfl

-- T3
theorem T3 (v_atoms : String → Bool) (ϕ ψ : WFF) (h : v v_atoms ϕ = false) :
  v v_atoms (p_imp ϕ ψ) = true := by
  -- 根据蕴含式的定义，展开真值计算
  simp [v, h]

-- T4

def atoms : WFF → Finset String
  | p_atm s   => {s}
  | p_not φ   => atoms φ
  | p_and φ ψ => atoms φ ∪ atoms ψ
  | p_or  φ ψ => atoms φ ∪ atoms ψ
  | p_imp φ ψ => atoms φ ∪ atoms ψ
  | p_iff φ ψ => atoms φ ∪ atoms ψ

theorem T4 (v₁ v₂ : String → Bool) (φ : WFF) (h : ∀ s ∈ atoms φ, v₁ s = v₂ s) :
  v v₁ φ = v v₂ φ := by
  induction φ with
  | p_atm s =>
    -- 基例：原子命题，直接应用条件h
    simp_all [v, atoms]
  | p_not φ ih =>
    -- 归纳步骤：否定式，应用归纳假设
    simp_all [v, atoms, ih]
  | p_and φ ψ ih_φ ih_ψ =>
    -- 归纳步骤：合取式，应用归纳假设
    simp_all [v, atoms, ih_φ, ih_ψ]
  | p_or φ ψ ih_φ ih_ψ =>
    -- 归纳步骤：析取式，应用归纳假设
    simp_all [v, atoms, ih_φ, ih_ψ]
  | p_imp φ ψ ih_φ ih_ψ =>
    -- 归纳步骤：蕴含式，应用归纳假设
    simp_all [v, atoms, ih_φ, ih_ψ]
  | p_iff φ ψ ih_φ ih_ψ =>
    -- 归纳步骤：等价式，应用归纳假设
    simp_all [v, atoms, ih_φ, ih_ψ]
