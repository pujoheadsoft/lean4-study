structure Reader (ρ : Type) (α : Type) where
  run : ρ -> α

/-
  Readerモナドの定義
  ⟨...⟩は構造体のコンストラクタ
  \angle と \rangle で出せる。
-/
namespace Reader
  instance : Functor (Reader ρ) where
    map f x := ⟨λe => f (x.run e)⟩

  def pure (a : α) : Reader ρ α :=
    ⟨fun _ => a⟩

  def bind (m : Reader ρ α) (k : α -> Reader ρ β) : Reader ρ β :=
    ⟨λe => (k (m.run e)).run e⟩

  instance : Monad (Reader ρ) where
    pure := pure
    bind := bind

  def runReader (m : Reader ρ α) (e : ρ) : α :=
    m.run e

  def ask : Reader ρ ρ :=
    ⟨λe => e⟩

end Reader

section ReaderExample
  open Reader

  def example1 : Reader String String := do
    let e <- ask
    Reader.pure s!"環境は {e} です。"

  def example2 : Reader String String :=
    ask >>= λe => Reader.pure s!"環境は {e} です。"

end ReaderExample

section ProofMonadLaws

  theorem left_identity (a : α) (k : α -> Reader ρ β) :
    (pure a >>= k) = k a := by
    rfl

  theorem right_identity (m : Reader ρ α) :
    (m >>= pure) = m := by
    rfl

  theorem associativity (m : Reader ρ α) (k : α -> Reader ρ β) (h : β -> Reader ρ γ) :
    ((m >>= k) >>= h) = (m >>= λa => k a >>= h) := by
    rfl

end ProofMonadLaws
