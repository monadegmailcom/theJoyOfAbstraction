import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory
open Set

-- a -> b <=> a ⊆ b
structure Obj (S : Set a) where
  val : Set a
  isSubset : val ⊆ S

inductive Mor : Obj S -> Obj S -> Type where
  | mk a b : a.val ⊆ b.val -> Mor a b

instance : Category (Obj S) where
  Hom x y := Mor x y
  id x := Mor.mk x x (refl x.val)
  comp f g := match f, g with
    | Mor.mk _ _ ab, Mor.mk _ _ bc
      => Mor.mk _ _ (_root_.trans ab bc)

-- samples
-- build bounded sets {0, 1, ..., k} ⊆ {0, 1, ..., n}
def bounded_by (k : Nat) := setOf (fun x => x <= k)
def subset (i j : Nat) (h : i <= j) : bounded_by i ⊆ bounded_by j :=
  Iff.mpr Set.setOf_subset_setOf
    (fun _ k => _root_.trans k h)

def n := 10
def S : Set Nat := bounded_by n
def mk_obj i (p : i <= n) : Obj S
  := Obj.mk (bounded_by i) (subset i n (by simp[p]))

def o5 : Obj S := mk_obj 5 (by simp)
def o7 : Obj S := mk_obj 7 (by simp)
def o9 : Obj S := mk_obj 9 (by simp)

def id5 : o5 ⟶ o5 := 𝟙 o5
def f57 : o5 ⟶ o7 := Mor.mk o5 o7 (subset 5 7 (by simp : 5 <= 7))
def f79 : o7 ⟶ o9 := Mor.mk o7 o9 (subset 7 9 (by simp : 7 <= 9))
def f59 := f57 ≫ f79
