import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

inductive Obj where
  | a : Obj
  | b : Obj
  | c : Obj

-- a -> b -> c
inductive Mor : Obj -> Obj -> Type where
  | idx x : Mor x x
  | fab : Mor Obj.a Obj.b
  | fbc : Mor Obj.b Obj.c
  | fac : Mor Obj.a Obj.c

instance : Category Obj where
  Hom := fun x y => Mor x y
  id (x : Obj) := Mor.idx x
  comp f g := match f, g with
    | Mor.idx _, g => g
    | f, Mor.idx _ => f
    | Mor.fab, Mor.fbc => Mor.fac
  comp_id f := by match f with
    | Mor.idx _ => rfl
    | Mor.fab => rfl
    | Mor.fbc => rfl
    | Mor.fac => rfl
  id_comp f := by match f with
    | Mor.idx _ => rfl
    | Mor.fab => rfl
    | Mor.fbc => rfl
    | Mor.fac => rfl
  assoc f g h := by match f, g, h with
    | Mor.idx _, _, _ => simp
    | Mor.fac, Mor.idx _, Mor.idx _ => simp
    | Mor.fbc, Mor.idx _, Mor.idx _ => simp
    | Mor.fab, Mor.idx _, Mor.idx _ => simp
    | Mor.fab, Mor.fbc, Mor.idx _ => simp
    | Mor.fab, Mor.idx _, Mor.fbc => simp
