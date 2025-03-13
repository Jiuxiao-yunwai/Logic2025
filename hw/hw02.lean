import Mathlib.Data.Real.Basic
-- T1

-- 定义一个结构体 Human，表示人类的属性
structure Human where
  isBaby: Bool          -- 是否是婴儿
  isIllogical: Bool     -- 是否不合逻辑
  isDespised: Bool      -- 是否被鄙视
  canManageCrocodile: Bool -- 是否能管理鳄鱼

-- 公理 1: 婴儿是不合逻辑的
axiom babies_are_illogical: ∀ (p: Human), p.isBaby → p.isIllogical

-- 公理 2: 能管理鳄鱼的人不会被鄙视
axiom nobody_is_despised_who_can_manage_a_crocodile: ∀ (p: Human), p.canManageCrocodile → ¬ p.isDespised

-- 公理 3: 不合逻辑的人会被鄙视
axiom illogical_persons_are_despised: ∀ (p: Human), p.isIllogical → p.isDespised

-- 定理: 婴儿不能管理鳄鱼
theorem Babies_cannot_manage_crocodiles: ∀ (p:Human), p.isBaby → ¬ p.canManageCrocodile := by
  -- 引入一个 Human 类型的变量 p，并假设 p 是婴儿
  intro p baby
  -- 根据公理 1，p 是不合逻辑的
  have h_illogical: p.isIllogical := babies_are_illogical p baby
  -- 根据公理 3，p 会被鄙视
  have h_despised: p.isDespised := illogical_persons_are_despised p h_illogical

  -- 将 p.isDespised 转换为双重否定 ¬¬p.isDespised
  have h_not_not_despised : ¬¬p.isDespised := not_not_intro h_despised

  -- 使用 modus tollens (mt) 从公理 2 推导出 ¬p.canManageCrocodile
  exact mt (nobody_is_despised_who_can_manage_a_crocodile p) h_not_not_despised

-- T2
structure Kitty where
  isTeachable: Bool
  isLoveFish: Bool
  playWithGorilla: Bool
  hasTail: Bool
  hasWhiskers: Bool
  hasGreenEyes: Bool
-- No kitten,that lovesfish,is unteachable;
axiom ax1_No_kitten_that_lovesfish_is_unteachable: ∀ p:Kitty, ¬ (p.isLoveFish → ¬ p.isTeachable)
-- No kitten without a tail will play with a gorilla;
axiom ax2_No_kitten_without_a_tail_will_play_with_a_gorilla: ∀ p:Kitty, ¬ (¬ p.hasTail → p.playWithGorilla)
-- Kittens with whiskers always love fish
axiom ax3_Kittens_with_whiskers_always_love_fish: ∀ p:Kitty, p.hasWhiskers → p.isLoveFish
-- No teachable kitten has green eyes
axiom ax4_No_teachable_kitten_has_green_eyes: ∀ p:Kitty, ¬ (p.isTeachable → p.hasGreenEyes)
-- No kittens have tails unless they have whiskers.
axiom ax5_No_kittens_have_tails_unless_they_have_whiskers: ∀ p:Kitty, ¬ ( p.hasTail ∧ ¬ p.hasWhiskers)

theorem Kitten_with_green_eyes_will_play_with_a_gorilla: ∀ p:Kitty, p.hasGreenEyes → p.playWithGorilla := by
  intro p hGreenEyes  -- 假设存在猫咪 p 有绿色眼睛（p.hasGreenEyes = true）
  by_contra hNotPlay  -- 反证法：假设结论不成立（p.playWithGorilla = false）

  -- 根据公理 ax2：¬p.hasTail → ¬p.playWithGorilla
  have hNoTail := ax2_No_kitten_without_a_tail_will_play_with_a_gorilla p
  simp_all  -- 简化后得到 ¬p.hasTail（p.hasTail = false）

  -- 根据公理 ax5：p.hasTail → p.hasWhiskers 的逆否命题 ¬p.hasWhiskers → ¬p.hasTail
  have hNoWhiskers := ax5_No_kittens_have_tails_unless_they_have_whiskers p
  simp_all  -- 简化后得到 ¬p.hasWhiskers（p.hasWhiskers = false）

  -- 根据公理 ax3：p.hasWhiskers → p.isLoveFish 的逆否命题 ¬p.isLoveFish → ¬p.hasWhiskers
  have hNoLoveFish := ax3_Kittens_with_whiskers_always_love_fish p
  -- simp_all  -- 简化后得到 ¬p.isLoveFish（p.isLoveFish = false）

  -- 根据公理 ax1：¬(p.isLoveFish → ¬p.isTeachable) 逻辑等价于 p.isLoveFish ∧ p.isTeachable
  have hTeachable := ax1_No_kitten_that_lovesfish_is_unteachable p
  simp_all  -- 分解得到 p.isTeachable = true（与后续步骤矛盾）

  -- 根据公理 ax4：¬(p.isTeachable → p.hasGreenEyes) 逻辑等价于 p.isTeachable ∧ ¬p.hasGreenEyes
  have hContradiction := ax4_No_teachable_kitten_has_green_eyes p
  simp_all  -- 已知 p.hasGreenEyes = true，得到矛盾 p.isTeachable ∧ false → false
