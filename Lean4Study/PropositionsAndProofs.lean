-- https://aconite-ac.github.io/theorem_proving_in_lean4_ja/propositions_and_proofs.html

-- Propは命題を表す型
variable {p : Prop}
variable {q : Prop}

-- theorem t1 としていくつか定義したいが、名前が被るので example を使う
example : p -> q -> p := fun hp : p => fun _ : q => hp
example : p -> q -> p :=
  fun hp : p =>
  fun _ : q =>
  show p from hp

theorem t1 (hp : p) (_ : q) : p := hp

/-
Conjunction(連言)
式 And.intro h1 h2 は証明 h1 : p と証明 h2 : q を使って p ∧ q の証明を構築する。
∧は\and と入力、∨ は\or と入力
⟨ は \< と入力、⟩ は \> と入力
-/
section Conjunction

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩ -- こうも書ける

-- 式 And.left h は証明 h : p ∧ q から p の証明を作る。同様に、And.right h は証明 h : p ∧ q から q の証明を作る。
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

-- ここまでの知識を使って、次のように p ∧ q → q ∧ p を証明することができる。
example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

end Conjunction

/- Disjunction(選言) -/
section Disjunction

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
  h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq)

end Disjunction

/- Negation and Falsity (否定と恒偽) -/
section NegationAndFalsity

variable (p q : Prop)

example (hpq : p -> q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

end NegationAndFalsity

/-
  Logical Equivalence (論理的同値)
  p ↔ q は、p が真ならば q も真であり、q が真ならば p も真であることを示す。
  \iff と入力すると ↔ が出る。
-/
section LogicalEquivalence

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

-- Iff.introやAnd.introは無名コンストラクタ記法<>を使ってこう書ける
example : p ∧ q ↔ q ∧ p :=
  ⟨
    λ h => ⟨h.right, h.left⟩,
    λ h => ⟨h.right, h.left⟩
  ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

end LogicalEquivalence


section Exercises

variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  ⟨
    λ h => ⟨h.right, h.left⟩,
    λ h => ⟨h.right, h.left⟩
  ⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨
    λ h => h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq),
    λ h => h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq)
  ⟩

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨
    λ h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,
    λ h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  ⟩
-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- -- 分配性
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- -- 他の性質
-- example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
-- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
-- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
-- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
-- example : ¬(p ∧ ¬p) := sorry
-- example : p ∧ ¬q → ¬(p → q) := sorry
-- example : ¬p → (p → q) := sorry
-- example : (¬p ∨ q) → (p → q) := sorry
-- example : p ∨ False ↔ p := sorry
-- example : p ∧ False ↔ False := sorry
-- example : (p → q) → (¬q → ¬p) := sorry

end Exercises
