import Mathlib.Algebra.Group.Defs

class HasIdentityElement (α : Type) where
  identityElement : α

structure Writer (ω : Type) [Monoid ω] (α : Type) where
  runWriter : α × ω

structure Difference (α : Type) where
  getDifference : α

-- 二項演算だけできる(Semigroupだと色々則を満たす必要があり、ぶっ壊す上で邪魔なので)
instance : Mul (Difference Int) where
  mul a b := ⟨a.getDifference + b.getDifference⟩

instance : HasIdentityElement (Difference Int) where
  identityElement := ⟨0⟩

-- section Ex1

--   variable {ω : Type} [Mul ω] [HasIdentityElement ω]

--   instance : Monad (Writer ω) where
--     pure a := ⟨(a, HasIdentityElement.identityElement)⟩

--     bind m f := ⟨
--       let (a, w1) := m.runWriter
--       let (b, w2) := (f a).runWriter
--       (b, Mul.mul w1 w2)
--     ⟩

-- end Ex1

section Ex2

  variable {ω : Type} [Monoid ω]

  instance : Monad (Writer ω) where
    pure a := ⟨(a, One.one)⟩

    bind m f := ⟨
      let (a, w1) := m.runWriter
      let (b, w2) := (f a).runWriter
      (b, w1 * w2)
    ⟩

  -- theorem left_identity (a : α) (k : α -> Writer ω β) :
  --   (pure a >>= k) = k a := by
  --   _p1

  -- theorem right_identity (m : Writer ω α) :
  --   (m >>= pure) = m := by
  --   rfl

  -- theorem associativity (m : Writer ω α) (k : α -> Writer ω β) (h : β -> Writer ω γ) :
  --   ((m >>= k) >>= h) = (m >>= λa => k a >>= h) := by
  --   rfl

end Ex2

section ProofMonadLaws



end ProofMonadLaws
