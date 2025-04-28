
namespace Laws

/- モナド則を抽象化する型クラスの定義 -/
class MonadLaws (m : Type → Type) [Monad m] where
  left_identity {α β} (a : α) (f : α → m β) :
    (pure a >>= f) = f a

  right_identity {α} (ma : m α) :
    (ma >>= pure) = ma

  associativity {α β γ} (ma : m α) (f : α → m β) (g : β → m γ) :
    ((ma >>= f) >>= g) = (ma >>= fun x => f x >>= g)

end Laws

export Laws (MonadLaws)

section LawExample
/- モナド則を満たすモナドの例 -/
def Identity (α : Type) : Type := α

instance : Monad Identity where
  pure x := x
  bind x f := f x

instance : Laws.MonadLaws Identity where
  left_identity _ _ := rfl
  right_identity _ := rfl
  associativity _ _ _ := rfl

end LawExample
