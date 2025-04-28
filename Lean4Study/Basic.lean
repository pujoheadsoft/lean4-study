def hello := "world"

def m : Nat := 3
def b1 : Bool := true
def b2 : Bool := false

#check m
#check b1 && b2

#eval 5 * 4
#eval m + 2

#check List

def F.{u} (α : Type u) : Type u := Prod α α
#check F
#check F Nat

-- 式から関数を作る
#check fun (x : Nat) => x + 5 -- funを使う
#check fun x => x + 5 -- 括弧は省略できる
#check λ (x : Nat) => x + 5 -- funの代わりにλを使う

#eval (λ x : Nat => x + 5) 3 -- 評価

-- 定義
def double (x : Nat) : Nat := x + x
def double2 : Nat -> Nat := λ x => x + x -- こうも書ける

def add (x : Nat) (y : Nat) : Nat := x + y

-- sectionで変数のスコープを制限する
section useful
  -- 変数(このスコープの中でのみ共通で使える)
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  #check α              -- セクション内で変数 `α` は参照可能。

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

end useful

-- 名前空間
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

-- Vectorを定義してみる
inductive Vector2 (α : Type) : Nat -> Type
| nil : Vector2 α 0
| cons : α -> Vector2 α n -> Vector2 α (n + 1)
deriving Repr


