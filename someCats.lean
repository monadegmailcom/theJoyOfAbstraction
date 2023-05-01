import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

namespace FinitToset

-- 0 -> 1 -> 2 -> ... -> n-1
-- only makes morphism if proof for x <= y is given
inductive Mor : Fin n -> Fin n -> Type where
  | fxy x y : (x.val <= y.val) -> Mor x y

instance : Category (Fin n) where
  Hom x y := Mor x y
  id x := Mor.fxy x x (by simp)
  comp f g := match f, g with
    | Mor.fxy _ _ h1, Mor.fxy _ _ h2
      => Mor.fxy _ _ (le_trans h1 h2)

-- some samples
abbrev Obj := Fin 4

def id2 := Mor.fxy (2 : Obj) 2 (by simp)
def f01 := Mor.fxy (0 : Obj) 1 (by simp)
def f12 := Mor.fxy (1 : Obj) 2 (by simp)
def f23 := Mor.fxy (2 : Obj) 3 (by simp)
def f13 := Mor.fxy (1 : Obj) 3 (by simp)

def f : (0: Obj) ⟶ 3 := (f01 ≫ f12) ≫ f23
def g : (0: Obj) ⟶ 3 := f01 ≫ (f12 ≫ f23)
def h : (1: Obj) ⟶ 3 := 𝟙 1 ≫ f13
example : f = g := by rfl
example : f = (f ≫ 𝟙 3) := by rfl
example : f13 = (f12 ≫ f23 : (1 : Obj) ⟶ 3) := by rfl

end FinitToset

namespace InfinitToset

-- 0 -> 1 -> 2 -> ...
inductive Mor : Nat -> Nat -> Type
  | fxy (x y : Nat) : (x <= y) -> Mor x y

instance : Category Nat where
  Hom x y := Mor x y
  id x := Mor.fxy x x (by simp)
  comp f g := match f, g with
    | Mor.fxy _ _ h1, Mor.fxy _ _ h2
        => Mor.fxy _ _ (le_trans h1 h2)

end InfinitToset

namespace Circle

-- 0 -> 1 -> ... -> n-1 -> 0
-- by composition everything pair of objects is
-- connected by exactly one morphism in each direction
inductive Mor : Fin n -> Fin n -> Type where
  | fxy x y : Mor x y

instance : Category (Fin n) where
  Hom x y := Mor x y
  id := fun _ => Mor.fxy _ _
  comp := fun _ _ => Mor.fxy _ _

-- samples
abbrev Obj := Fin 4

def f31 : (3 : Obj) ⟶ 1 := Mor.fxy 3 1
def f13 : (1 : Obj) ⟶ 3 := Mor.fxy 1 3
def id1 : (1 : Obj) ⟶ 1 := Mor.fxy 1 1
def id2 : (2 : Obj) ⟶ 2 := 𝟙 2

example : id1 = f13 ≫ f31 := rfl

end Circle
