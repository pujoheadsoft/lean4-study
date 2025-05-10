import Lean4Study.Monad.Laws

inductive Freer : (_: Type u -> Type v) -> (_ret: Type u) -> Type _ where
| pure : α -> Freer φ α
| bind : φ α -> (α -> Freer φ β) -> Freer φ β

namespace Freer
  variable {φ : Type u -> Type v} {α : Type u} {β : Type u}

  def _map (f : α -> β) (x : Freer φ α) : Freer φ β :=
    match x with
    | pure a => pure (f a)
    | bind m k => bind m (λa => _map f (k a))

  def _bind (x : Freer φ α) (f : α -> Freer φ β) : Freer φ β :=
    match x with
    | pure a => f a
    | bind m k => bind m (λa => _bind (k a) f)

  instance : Functor (Freer φ) where
    map := _map

  instance : Monad (Freer φ) where
    pure := pure
    bind := _bind

section ProofMonadLaws

  variable {φ : Type u -> Type v} {α : Type u} {β : Type u}

  theorem left_identity (a : α) (k : α -> Freer φ β) :
    (pure a >>= k) = k a := by
    rfl

  -- theorem right_identity (m : Freer φ α) :
  --   (m >>= pure) = m := by
  --   cases m with
  --   | pure => rfl
  --   | bind m k => rfl

  -- theorem associativity (m : Freer φ α) (k : α -> Freer φ β) (h : β -> Freer φ γ) :
  --   ((m >>= k) >>= h) = (m >>= λa => k a >>= h) := by
  --     cases m with
  --     | pure => rfl
  --     | bind _ => rfl

end ProofMonadLaws
