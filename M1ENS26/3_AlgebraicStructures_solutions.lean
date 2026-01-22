import Mathlib

section Groups

-- ## Bad Ideas
-- variable {G C : Type*} [Group G] [CommGroup C]

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]

example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor
  rintro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  rcases a with ⟨u, v, huv, hvu⟩
  rw [isUnit_iff_exists]
  refine ⟨f v, ?_, ?_⟩
  · simp [← map_mul, huv]
  · simp [← map_mul, hvu]

/- ## Basic facts about groups
1. Def: unit, basic multiplication, `grind/group`
2. Add vs Comm groups
3. Subgroups -/

-- ### Definitions, basic properties and tactics
structure WrongGroup where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one
-- You might want to put one more condition called `mul_inv_cancel`, but we can
-- actually prove it from the others.


lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α.carrier) :
    α.mul x y = α.one → α.inv x = y := by
  intro h
  apply_fun (fun z ↦ α.mul (α.inv x) z) at h
      -- use the `apply_fun` tactic to apply a function to both sides of a hypothesis
  rw [α.mul_one, ← α.mul_assoc, α.inv_mul_cancel, α.one_mul] at h
  exact h.symm

lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

#print Group
-- class Group (G : Type*) extends DivInvMonoid G where
--   protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid
/- Mathlib chose the second solution, because this way we can put a group structure
on an already defined type, such as `ℤ` or `Equiv₁ α α`.
(But when we define the category of groups, its objects are terms of a type resembling
`BundledGroup₁`.) -/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

-- **Make a better one, using commutativity**
example {G : Type*} [CommGroup G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  group

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel

-- @[to_additive]
lemma IHP_mul {G : Type} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two]
  rw [← mul_assoc]
  rw [h]
  group

example (A : Type) [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  rw [two_nsmul, ← add_assoc, h]
  simp

-- ## Classes

-- Before Subgroups use `classes` for 1, 0, *, +; and fix the `α.carrier` above using `SetLike`.

#print SetLike -- a class for types that look like types of sets
-- (`SetLike A G` comes with a coercion `SetLike.coe : A → Set G`,
-- and a condition saying that this coercion is injective)

@[ext] -- creates a theorem saying that subgroups are equal if their carriers are
structure Subgroup₁ where
  /-- The carrier of a subgroup. -/
  carrier : Set G
  /-- The product of two elements of a subgroup belongs to the subgroup. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier
  /-- The unit element belongs to the subgroup. -/
  one_mem : 1 ∈ carrier

#print Subgroup₁ --note that `G` and `Group G` are arguments

/-- Subgroups in `G` can be seen as sets in `G`. -/
instance : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

/- Examples of the coercion to sets un action:-/

example (H : Subgroup₁ G) : 1 ∈ H := H.one_mem   -- elements of a subgroup

example (H : Subgroup₁ G) (α : Type) (f : G → α) := f '' H  -- image by a function

/- Now for the group structure on subgroups.

We have an automatic coercion from sets to types, so we get a coercion
from subgroups to types:
-/

example (H : Subgroup₁ G) (x : H) : 0 = 0 := by
  set x' : G := x.1
  set x'' : G := x.val
  set x''' : G := (x : G)
  have xprop := x.2
  have xprop' := x.property
  rfl

/- Our main tool to prove things about terms of type `↥H` is the
theorem `SetCoe.ext` (also provided by `SetLike`), which says that
the function `↥H → G` sending `x` to `x.val` is injective.-/

#print SetCoe.ext -- If `a, b : ↥H`, then `a = b` (in `↥H`) as soon as
--`a.val = b.val` (in `G`).

instance Subgroup₁Group (H : Subgroup₁ G) : Group H where
  mul x y := ⟨x*y, H.mul_mem x.property y.property⟩
  mul_assoc x y z := by
    apply SetCoe.ext
    exact mul_assoc (x : G) y z
  one := ⟨1, H.one_mem⟩
  one_mul x := SetCoe.ext (one_mul (x : G))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : G))
  inv x := ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul_cancel x := SetCoe.ext (inv_mul_cancel (x : G))

@[ext]
structure MonoidHom₁ (M N : Type*) [Monoid M] [Monoid N] where
-- We use the mathlib classes now.
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)

-- Not the @[ext] tag.
#check MonoidHom₁.ext

def f : MonoidHom₁ (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul p p' := by simp only [Prod.fst_mul, Prod.snd_mul]; ring

/-
#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying
-/

#check f.toFun ⟨2,3⟩
#eval! f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun

instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

#check f ⟨2,3⟩



-- ## Group Homomorphisms



end Groups

section Rings
end Rings

section Exercises

end Exercises
section Later

open Ideal in
-- **FAE** Use later
theorem idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 := by
  set Ia := J.map <| RingHom.fst .. with hIa
  set Ib := J.map <| RingHom.snd .. with hIb
  use ⟨Ia, Ib⟩
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · constructor
    · apply Ideal.mem_map_of_mem
      exact hx
    · apply Ideal.mem_map_of_mem
      exact hx
  · rw [mem_prod, mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective),
        mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective)] at hx
    obtain ⟨⟨y, hy_mem, hyx⟩, ⟨z, hz_mem, hzx⟩⟩ := hx
    have : ⟨x.1, 0⟩ + ⟨0, x.2⟩ = x := Prod.fst_add_snd x
    rw [← this, ← hyx, ← hzx]
    simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk_add_mk, add_zero, zero_add]
    replace hyx : ⟨y.1, y.2⟩ * ⟨1, 0⟩ = (⟨y.1, 0⟩ : A × B) := by
        calc ⟨y.1, y.2⟩ * ⟨1, 0⟩ = ⟨y.1 * 1, y.2 * 0⟩ := by rfl
                               _ = (⟨y.1, 0⟩ : A × B) := by rw [mul_one, mul_zero]
    replace hzx : ⟨z.1, z.2⟩ * ⟨0, 1⟩ = (⟨0, z.2⟩ : A × B) := by
        calc ⟨z.1, z.2⟩ * ⟨0, 1⟩ = ⟨z.1 * 0, z.2 * 1⟩ := by rfl
                                 _ = (⟨0, z.2⟩ : A × B) := by rw [mul_one, mul_zero]
    rw [← zero_add y.1, ← add_zero z.2, ← Prod.mk_add_mk 0 y.1 z.2 0, ← hzx, ← hyx, Prod.mk.eta,
        Prod.mk.eta]
    apply J.add_mem (J.mul_mem_right _ hz_mem) (J.mul_mem_right _ hy_mem)


open Ideal in
-- **FAE** Use later
theorem idealProd' (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 :=
  ⟨⟨J.map <| RingHom.fst .., J.map <| RingHom.snd ..⟩, J.ideal_prod_eq⟩

-- def idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal A × B) : (Ideal A) x (Ideal B) := by

-- @[to_additive]
-- instance [IsCyclic G] (N : Subgroup G) : N.Normal :=
--     @N.normal_of_comm _ IsCyclic.commGroup
--
-- @[to_additive]
-- theorem isCyclic_quotient [IsCyclic G] (N : Subgroup G) : IsCyclic (G ⧸ N) :=
--     isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective _

end Later
