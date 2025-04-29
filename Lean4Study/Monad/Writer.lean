import Mathlib.Algebra.Group.Defs

-- Writerモナドの型定義
structure Writer (ω : Type) (α : Type) where
  runWriter : α × ω

section ProofMonadLaws

variable [Monoid ω]

instance [Monoid ω] : Monad (Writer ω) where
  pure a := ⟨(a, 1)⟩

  bind m f := ⟨
    let (a, w₁) := m.runWriter
    let (b, w₂) := (f a).runWriter
    (b, w₁ * w₂)
  ⟩

theorem left_identity (a : α) (k : α -> Writer ω β) :
  (pure a >>= k) = k a := by
  simp [pure, bind, mul_one] -- pure,bind,左単位則

theorem right_identity (m : Writer ω α) :
  (m >>= pure) = m := by
  simp [pure, bind, one_mul] -- pure,bind,右単位則

theorem associativity (m : Writer ω α) (k : α -> Writer ω β) (h : β -> Writer ω γ) :
  ((m >>= k) >>= h) = (m >>= (fun a => k a >>= h)) := by
  simp [pure, bind, mul_assoc] -- pure,bind,結合則

end ProofMonadLaws
