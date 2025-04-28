import Lean4Study.Monad.Laws

-- Optionモナドがあるけど、自前でMaybeとして定義してみる。
inductive Maybe (α : Type u) where
| nothing : Maybe α
| just (val : α ) : Maybe α

namespace Maybe
  instance : Functor Maybe where
    map f x := match x with
      | nothing => nothing
      | just a => just (f a)

  instance : Monad Maybe where
    pure x := just x
    bind x f := match x with
      | nothing => nothing
      | just a => f a

end Maybe

section MaybeExample
  open Maybe

  def example1 : Maybe Nat := do
    let x <- pure 5
    let y <- pure 10
    pure (x + y)

  def example2 : Maybe Nat := do
    let x <- just 5
    let y <- nothing
    pure (x + y)

  #eval example1
  #eval example2

end MaybeExample

section ProofMonadLaws

  theorem left_identity (a : α) (k : α -> Maybe β) :
    (pure a >>= k) = k a := by
    rfl

  theorem right_identity (m : Maybe α) :
    (m >>= pure) = m := by
    cases m with
    | nothing => rfl
    | just _ => rfl

  theorem associativity (m : Maybe α) (k : α -> Maybe β) (h : β -> Maybe γ) :
    ((m >>= k) >>= h) = (m >>= λa => k a >>= h) := by
      cases m with
      | nothing => rfl
      | just _ => rfl

end ProofMonadLaws

section ProofMonadLaws2
  open Maybe

  instance : Laws.MonadLaws Maybe where
    left_identity _ _ := rfl

    right_identity ma := by
      cases ma with
      | nothing => rfl
      | just _ => rfl

    associativity ma f g := by
      cases ma with
      | nothing => rfl
      | just _ => rfl

end ProofMonadLaws2
