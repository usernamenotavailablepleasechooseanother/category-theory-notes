module

public import Mathlib
public import CommDiag

-- public section

/-
# Category Theory in Lean

Useful resources:
- [A great category theory book](https://raw.githubusercontent.com/BartoszMilewski/DaoFP/refs/heads/master/DaoFP.pdf)
- [Curry-Howard-Lambek correspondence](https://ncatlab.org/nlab/show/computational+trilogy#rosetta_stone)
- [Hask is not a category](https://math.andrej.com/2016/08/06/hask-is-not-a-category/)

## Lean, the category!

Objects: Types
Morphisms: Total functions

In Lean, all functions are defined on all inputs and always terminate (unless we tag them as `partial` or `unsafe`). Haskell doesn't have this nice guarentee.

Let's check that Lean is actually a category.

Tip: You can Ctrl-click on anything to see its definition.
-/

-- Composition of morphisms is just function composition, denoted `∘`
#check Function.comp

-- Identity morphism
#check Id
-- `Id` works for all types, whereas `id` is different and works for all terms.

-- Composition of morphisms is associative
#check Function.comp_assoc

-- Equality of morphisms
#check funext
-- If two functions return the same values for every input, then they're equal. This ignores time complexity though so in practice the two functions might not be interchangeable.


/-
## Bicartesian closed categories

Lean is a bicartesian closed category, which means it has an initial object, terminal object, sums, products, exponentials, sums distribute over products, and products distribute over exponentials.
-/

-- Initial object
#check False
-- Morphism from initial object
#check False.elim
-- The logic interpretation of this is that we can prove anything from `False`
-- Isomorphic to initial object but in higher universes, because Lean universes are not cumulative
#check PEmpty
#check PEmpty.elim

-- Terminal object
#check True
-- Morphism to terminal object
#check fun _ ↦ True.intro
-- Also isomorphic
#check PUnit
#check fun _ ↦ PUnit.unit

-- Sums (coproducts), which correspond to `∨` in logic
#check Sum
-- Morphism from first type
#check Sum.inl
-- Morphism from second type
#check Sum.inr
#html sumDiag

-- Products, which correspond to `∧` in logic
#check Prod
-- Morphism to first type
#check Prod.fst
-- Morphism to second type
#check Prod.snd
#html prodDiag

-- Exponentials
#check (· → ·)
-- Lean is self-enriched because we can view any hom-set between `α` and `β` as the object `α → β`.

/-- Sums distribute over products -/
def sum_distrib_prod : α × (β ⊕ γ) ≃ α × β ⊕ α × γ where
  toFun
    | (a, .inl b) => .inl (a, b)
    | (a, .inr b) => .inr (a, b)
  invFun
    | .inl (a, b) => (a, .inl b)
    | .inr (a, b) => (a, .inr b)
  left_inv := by grind
  right_inv := by grind

/-- Products distribute over exponentials -/
def prod_distrib_exp {α : Type u} : (α → (β × γ)) ≃ (α → β) × (α → γ) where
  toFun f := (Prod.fst ∘ f, Prod.snd ∘ f)
  invFun f := fun x ↦ (f.1 x, f.2 x)
  left_inv := by grind


/-
## Universes

You might have noticed the `Type u` in some of those previous examples. In Lean, `2 : ℕ : Type : Type 1 : Type 2 : Type 3`, and so on, where each level of the hierarchy is called a universe. However, if we had `Type : Type`, then that would cause Girard's paradox (a variant of Russell's paradox).

We can't actually assign `Type` a different type using an axiom, but we can add a bad axiom that says there's an injective function from a sigma (dependent product) type in `Type 1` to some type in `Type`. (Thanks to Aaron Liu and Paul Reichert on the Lean Zulip for this proof.)
-/

namespace Paradox

-- Uncomment these two lines to prove false
-- axiom Bad : Type
-- axiom bad : (α : Type) × α ↪ Bad

/-- An injective function from `Bad` predicates to `Bad` -/
noncomputable def k (P : Bad → Prop) : Bad :=
  bad ⟨Bad → Prop, P⟩

/-- `k` is injective because the sigma constructor and `bad` are injective -/
lemma k_injective : k.Injective :=
  fun _ _ hab ↦ eq_of_heq (Sigma.mk.inj (bad.injective hab)).2

/-- This is kind of like the set of sets that don't contain itself -/
def Q (b : Bad) : Prop :=
  ∃ P, k P = b ∧ ¬P b

/-- If `Q (k Q)`, then there exists `P` with `k P = k Q` and `¬P (k Q)`, but `k` is injective so `P = Q` -/
lemma down (h : Q (k Q)) : ¬Q (k Q) := by
  obtain ⟨P, hP⟩ := h
  exact (k_injective hP.1) ▸ hP.2

/-- If `¬Q (k Q)` then choose `P := Q` so `Q (k Q)` holds by definition -/
lemma up (h : ¬Q (k Q)) : Q (k Q) :=
  ⟨Q, rfl, h⟩

/-- Now use a diagonalization argument (alternatively, we can use the law of excluded middle) -/
private theorem false : False :=
  let f := fun h ↦ down h h
  f (up f)

end Paradox


/-
## Functors

Recall that a functor is a function from one category to another. An endofunctor is a functor from a category to itself. The type class `[LawfulFunctor F]` corresponds to endofunctors in Lean.

`F` maps objects (it's a type constructor)
`Functor.map (f := F)` (denoted `<$>`) maps morphisms

Note the the `<$>`'s type signature, `(α → β) → f α → f β` is the same thing as `(α → β) → (f α → f β)` because of partial application.
-/

-- Type class containing `map`
#check Functor
-- This diagram commutes by definition
#html functorDiag

-- Type class containing functor laws (I'm not sure why it's split like this in Lean)
#check LawfulFunctor
-- `F` preserves composition, so the blue and red arrows on the right should be equal
#html functorCompDiag

-- Examples of functors
#synth Functor List
#synth Functor Tree
#synth Functor Option
#synth Functor (Except String)

-- Using functors
#eval (· * 2) <$> [1, 2, 3]
#eval (· * 2) <$> some 2
#eval (· * 2) <$> none

/-- `List` satisfies the functor laws, yay -/
instance : LawfulFunctor List where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map := by simp

/-- Hom-functor in self-enriched category -/
@[simp]
instance (α : Type u) : Functor (α → ·) where
  map f g := f ∘ g

instance (α : Type u) : LawfulFunctor (α → ·) where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map := by simp [Function.comp_assoc]


/--
## Contravariant functors

If `(α → ·)` is a functor, then what about `(· → α)`? If you try defining `<$>` for `(· → α)`, you'll find out that it doesn't work, because `(· → α)` is actually a contravariant functor.

Normal functors, sometimes called covariant functors, map Lean to Lean. Contravariant functors map Colean to Lean. They're occasionally called "cofunctors", but that's a misnomer because functors are self-dual.
-/

public class Contrafunctor (F : Type u → Type v) where
  contramap : (β → α) → F α → F β
  id_contramap (x : F α) : contramap id x = x
  comp_contramap (g : β → α) (h : γ → β) (x : F α) : contramap (g ∘ h) x = contramap h (contramap g x)

/-- This is not standard notation but just something I made up -/
infixr:100 " <¥> " => Contrafunctor.contramap

-- Intuitively, `<$>` turns a "producer of α" into a "producer of β" while `<¥>` turns a "consumer of α" into a "consumer of β".

/-- Some useful lemmas -/
lemma Contrafunctor.id_contramap' [Contrafunctor f] : Contrafunctor.contramap (F := f) (@id α) = id := by
  ext x
  exact Contrafunctor.id_contramap x

lemma Contrafunctor.contramap_comp_contramap [Contrafunctor F] (g : α → β) (h : β → γ) :
    ((g <¥> ·) ∘ (h <¥> ·) : F γ → F α) = Contrafunctor.contramap (h ∘ g) :=
  funext fun _ ↦ (comp_contramap _ _ _).symm

/-- The other kind of hom-functor is contravariant -/
@[simp]
instance (α : Type u) : Contrafunctor (· → α) where
  contramap f g := g ∘ f
  id_contramap := by simp
  comp_contramap := by simp [Function.comp_assoc]

/-
Contravariant functors are rarely used in Lean, and most examples of them are function object things like the hom-functor.

A function type is covariant if the free parameter is in an even depth and contravariant if at an odd depth.

- `(α → ·)` is covariant
- `(· → α)` is contravariant
- `((· → α) → β)` is covariant
- `(((· → α) → β) → γ)` is contravariant
- And so on
-/


/-
## Composition of functors

Since functors map Lean to Lean, we can compose two functors to get a new functor.s
-/

/-- Composition of two functors of same variance is a functor -/
@[simp]
instance [Functor F] [Functor G] : Functor (F ∘ G) where
  map f x := Functor.map (f := F) (f <$> ·) x

instance [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] : LawfulFunctor (F ∘ G) where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map f g x := by simp; rfl

@[simp]
instance [Contrafunctor F] [Contrafunctor G] : Functor (F ∘ G) where
  map f x := Contrafunctor.contramap (F := F) (Contrafunctor.contramap f) x

instance [Contrafunctor F] [Contrafunctor G] : LawfulFunctor (F ∘ G) where
  map_const := by solve_by_elim
  id_map := by simp [Contrafunctor.id_contramap']
  comp_map f g x := by simp [← Contrafunctor.contramap_comp_contramap]

-- If functors are sort of like "containers" for data, then functor composition is like "nesting" two "containers"/
#synth LawfulFunctor (List ∘ Option)

/-- Composition of functors of opposite variance is a contravariant functor -/
@[simp]
instance [Functor F] [LawfulFunctor F] [Contrafunctor G] : Contrafunctor (F ∘ G) where
  contramap f x := Functor.map (f := F) (f <¥> ·) x
  id_contramap := by simp [Contrafunctor.id_contramap]
  comp_contramap := by simp [Contrafunctor.comp_contramap]

@[simp]
instance [Contrafunctor F] [Functor G] [LawfulFunctor G] : Contrafunctor (F ∘ G) where
  contramap f x := Contrafunctor.contramap (F := F) (f <$> ·) x
  id_contramap := by
    simp only [Function.comp_apply, id_map]
    exact Contrafunctor.id_contramap
  comp_contramap f g x := by simp only [← Functor.map_comp_map g f, Contrafunctor.comp_contramap]


/-
## Other kinds of functors
-/

-- Bifunctors map Lean × Lean to Lean
#check Bifunctor
#check LawfulBifunctor

-- `Sum` and `Prod` are bifunctors
#synth LawfulBifunctor Sum
#synth LawfulBifunctor Prod

-- Multivariate functors
#check MvFunctor
#check LawfulMvFunctor

-- Profunctors are useful for lenses and [optics](https://marcosh.github.io/post/2025/10/07/the-mondrian-introduction-to-functional-optics.html)
class Profunctor (P : Type u → Type v → Type*) where
  dimap : (σ → α) → (β → τ) → P α β → P σ τ
  id_dimap (x : P α β) : dimap id id x = x
  dimap_dimap (f : α₁ → α₀) (f' : α₂ → α₁) (g : β₀ → β₁) (g' : β₁ → β₂) (x : P α₀ β₀) :
    dimap f' g' (dimap f g x) = dimap (f ∘ f') (g' ∘ g) x

/-- Exponentials are profunctors -/
instance : Profunctor (· → ·) where
  dimap f g h := g ∘ h ∘ f
  id_dimap := by simp
  dimap_dimap := by simp [Function.comp_assoc]

/-- We can compose two profunctors -/
inductive Procompose P Q [Profunctor P] [Profunctor Q] a b
  | mk : Q a x → P x b → Procompose P Q a b

instance [Profunctor P] [Profunctor Q] : Profunctor (Procompose P Q) where
  dimap l r
    | ⟨qax, pxb⟩ => ⟨Profunctor.dimap l id qax, Profunctor.dimap id r pxb⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]

-- TODO more commentary, wedge condition
abbrev End P [Profunctor P] := ∀ x, P x x

abbrev Coend P [Profunctor P] := Σ x, P x x

abbrev ProPair Q P [Profunctor P] [Profunctor Q] a b x y :=
  Q a y × P x b

instance [Profunctor P] [Profunctor Q] : Profunctor (ProPair Q P a b) where
  dimap l r
    | ⟨qax, pxb⟩ => ⟨Profunctor.dimap id r qax, Profunctor.dimap l id pxb⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]

abbrev CoendCompose P Q [Profunctor P] [Profunctor Q] a b :=
  Coend (ProPair Q P a b)

instance [Profunctor P] [Profunctor Q] : Profunctor (CoendCompose P Q) where
  dimap l r
    | ⟨x, (qay, pxb)⟩ => ⟨x, (Profunctor.dimap l id qay, Profunctor.dimap id r pxb)⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]


/-
## Natural transformations

A natural transformation is a function between two functors that satisfies a naturality condition. Intuitively, a natural transformation "moves" data from one "container" to another.
-/

-- Type of a natural transformation (without the naturality condition)
abbrev NaturalType.{u} (F : Type u → Type v) (G : Type u → Type w) :=
  {α : Type u} → F α → G α

/-- The naturality condition, which intuitively states that "moving" data is simply just a move and does not meaningfully change it -/
class Natural F [Functor F] [LawfulFunctor F] G [Functor G] [LawfulFunctor G] (η : NaturalType F G) where
  naturality (f : α → β) (x : F α) : f <$> (η x) = η (f <$> x)

-- In Haskell, naturality is automatically guarenteed because all polymorphic functions in Haskell are parametrically polymorphic functions, which intuitively means that the function does "the same thing" for every type. This is classic example of "theorems for free". However, in Lean we're not so lucky, because a polymorphic function in Lean can do something different depending on its input type.

/-- A practical example of a natural transformation -/
instance : Natural List Option List.head? :=
  ⟨by simp⟩

/-- Another example -/
abbrev OptionToList : Option α → List α
  | some a => [a]
  | none => []

instance : Natural Option List OptionToList :=
  ⟨by simp; grind⟩

noncomputable abbrev FunToOption (f : α → β) : Option β := by
  by_cases h : Nonempty α
  · exact some <| f <| Classical.choice h
  · exact none

instance : Natural (α → ·) Option FunToOption :=
  ⟨by by_cases h : Nonempty α <;> simp [h]⟩

/-- Naturality for functions between contravariant functors -/
class Contranatural F [Contrafunctor F] G [Contrafunctor G] (η : NaturalType F G) where
  naturality (f : β → α) (x : F α) : f <¥> (η x) = η (f <¥> x)

-- Vertical composition of natural transformations, which intuitively this is like doing two data moves
instance [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] [Functor H] [LawfulFunctor H] [M : Natural F G η] [N : Natural G H μ] :
    Natural F H (fun {α : Type u} ↦ @μ α ∘ @η α) :=
  ⟨by simp [N.naturality, M.naturality]⟩

-- Horizontal composition of natural transformations, which intuitively is like repackaging data in nested "containers"
instance (η : NaturalType F F') (μ : NaturalType G G') [Functor F] [LawfulFunctor F] [Functor F'] [LawfulFunctor F'] [Functor G] [LawfulFunctor G] [Functor G'] [LawfulFunctor G'] [M : Natural F F' η] [N : Natural G G' μ] :
    Natural (G ∘ F) (G' ∘ F') (μ ∘ (η <$> ·)) :=
  ⟨by simp [N.naturality, M.naturality]⟩

/-- Alternatively we do `μ` first and then the map second -/
instance (η : NaturalType F F') (μ : NaturalType G G') [Functor F] [LawfulFunctor F] [Functor F'] [LawfulFunctor F'] [Functor G] [LawfulFunctor G] [Functor G'] [LawfulFunctor G'] [M : Natural F F' η] [N : Natural G G' μ] :
    Natural (G ∘ F) (G' ∘ F') ((Functor.map (f := G') η ·) ∘ μ) :=
  ⟨by simp [N.naturality, M.naturality]⟩

/-- The two orderings are equivalent, and this lemma only requires the outer transformation to be natural -/
lemma horizontal_comp_equiv (η : NaturalType F F') (μ : NaturalType G G') [Functor F] [LawfulFunctor F] [Functor F'] [LawfulFunctor F'] [Functor G] [LawfulFunctor G] [Functor G'] [LawfulFunctor G'] [N : Natural G G' μ] :
    (μ ∘ (η <$> ·)) x = ((Functor.map (f := G') η ·) ∘ μ) x := by
  simp [N.naturality]


/-
## The Yoneda lemma

TODO: Intuition
-/

def FunToFunctor [Functor F] [LawfulFunctor F] (g : α → β) : F β :=
  sorry

/-- Yoneda forward map (g is not necessarily natural) -/
def yoneda (g : NaturalType (α → ·) F) [Functor F] [LawfulFunctor F] : F α :=
  g id

/-- Yoneda reverse map -/
def yoneda' [Functor F] [LawfulFunctor F] (x : F α) : NaturalType (α → ·) F :=
  (· <$> x)

/-- Reverse map always produces a natural transformation -/
instance [Functor F] [LawfulFunctor F] : Natural (α → ·) F (yoneda' y) :=
  ⟨fun f x ↦ by simp [yoneda']; rfl⟩

/--
Mapping and unmapping a natural transformation returns the itself

Note that this does not work for an arbitrary function between the hom-functor and `f` because we use the naturality condition.
-/
theorem yoneda_lemma (g : NaturalType (α → ·) F) [Functor F] [LawfulFunctor F] [N : Natural (α → ·) F g] : yoneda' (yoneda g) x = g x := by
  simp [yoneda, yoneda', N.naturality]

/-- Mapping and unmapping an element `f α` returns itself -/
theorem yoneda_lemma' (x : F α) [Functor F] [LawfulFunctor F] : yoneda (yoneda' x) = x := by
  simp [yoneda, yoneda']

/-- Coyoneda forward map -/
def coyoneda (g : NaturalType (· → α) F) [Contrafunctor F] : F α :=
  g id

/-- Coyoneda reverse map -/
def coyoneda' [Contrafunctor F] (x : F α) : NaturalType (· → α) F :=
  (· <¥> x)

/-- Reverse map always produces a natural transformation -/
instance [Contrafunctor F] : Contranatural (· → α) F (coyoneda' y) :=
  ⟨fun f x ↦ by simp [coyoneda', Contrafunctor.comp_contramap]⟩

/-- Same but for Coyoneda -/
theorem coyoneda_lemma (g : NaturalType (· → α) F) [Contrafunctor F] [N : Contranatural (· → α) F g] : coyoneda' (coyoneda g) x = g x := by
  simp [coyoneda, coyoneda', N.naturality]

/-- Same but for Coyoneda -/
theorem coyoneda_lemma' (x : F α) [Contrafunctor F] : coyoneda (coyoneda' x) = x := by
  simp [coyoneda, coyoneda', Contrafunctor.id_contramap]

-- `yoneda (F := Id)` is just continuation-passing style
#simp [NaturalType] fun (α : Type*) ↦ NaturalType (α → ·) Id

-- We can also formulate the Yoneda lemma using profunctors, ends, and coends
-- TODO explanation
def Yo F [Functor F] [LawfulFunctor F] (α x y : Type u) := (α → x) → F y

instance [Functor F] [LawfulFunctor F] : Profunctor (Yo F α) where
  dimap g h i j := h <$> (i (g ∘ j))
  id_dimap := by simp
  dimap_dimap f f' g g' x := by simp; rfl

def yonedaEnd [Functor F] [LawfulFunctor F] (g : End (Yo F α)) : F α :=
  g α id

def yonedaEnd' [Functor F] [LawfulFunctor F] (x : F α) : End (Yo F α) :=
  fun _ f ↦ f <$> x

def Coyo F [Functor F] [LawfulFunctor F] (α x y : Type u) := (x → α) × F y

instance [Functor F] [LawfulFunctor F] : Profunctor (Coyo F α) where
  dimap g h i := (i.1 ∘ g, h <$> i.2)
  id_dimap := by simp
  dimap_dimap f f' g g' x := by simp; rfl

def coyonedaCoend [Functor F] [LawfulFunctor F] (g : Coend (Coyo F α)) : F α :=
  g.2.1 <$> g.2.2

def coyonedaCoend' [Functor F] [LawfulFunctor F] (x : F α) : Coend (Coyo F α) :=
  ⟨α, (id, x)⟩


/-
## Applicative functors and monads

Lean is a purely functional programming language, so functions must only depend on their arguments and have no access to the outside world. Then how can we do IO or have mutable state? The solution is to encode a function's side effects into the return type of the function.

TODO write more
-/

-- Motivation: mapping multi-arg functions
#simp (some 3).map (· * ·)

#eval (· * ·) <$> (some 3) <*> (some 4)

-- Applicative functors
#check Applicative
#check LawfulApplicative

/-- Composition of two applicatives is an applicative -/
@[simp]
instance [Applicative F] [Applicative G] : Applicative (F ∘ G) where
  pure x := pure (f := F) (pure x)
  seq f x := Seq.seq (f := F) ((· <*> ·) <$> f) x

instance [Applicative F] [LawfulApplicative F] [Applicative G] [LawfulApplicative G] : LawfulApplicative (F ∘ G) where
  seqLeft_eq := by simp
  seqRight_eq := by simp
  pure_seq := by simp [pure_seq]
  map_pure := by simp
  seq_pure := by simp
  seq_assoc x f g := by
    simp [seq_assoc, seq_map_assoc, map_seq]
    congr
    ext
    simp [seq_assoc]

-- TODO: Lax monoidal functors


-- Monads, "warm fuzzy things"
#check Monad
#check LawfulMonad

/-
- Functors let us apply `α → β` to `f α`
- Applicatives let us apply `f (a → β)` to `f α`
- But what about applying an "effectful" function `α → f β` to `f α`, or composing two effectful functions `α → f β` and `β → f γ`?

Kleisli category: Any monad `m` creates a category where the objects are still types but the morphisms are `α → β` for every `α → f β` in Lean. Then composition of effectful functions becomes composition of morphisms.

This construction also motivates the monad laws.

In fact, using `>>=` and `pure` we can implement `<$>` and `<*>` so every monad is also a functor and applicative.

Exercise: Find an example of a functor which is not applicative and an applicative which is not a monad.
-/

-- Some examples
#synth Monad List
#synth Monad Option
#synth Monad IO
#synth Monad (StateM ℕ)
#synth Monad (Writer ℕ)
#synth Monad (ST ℕ)
#synth Monad (Except String)
#synth Monad (Sum ℕ)

instance : LawfulMonad Option :=
  LawfulMonad.mk' Option
    (id_map := by simp)
    (pure_bind := by simp [Option.bind])
    (bind_assoc := by simp; grind)
    (bind_pure_comp := by simp [Option.map]; grind)

#synth LawfulMonad List


/--
This function looks ugly, but we can simplify it with `do` notation, which is syntactic sugar that lets us unwrap monadic values and automatically inserts `>>=` when we use the unwrapped values

https://slightknack.dev/blog/do-notation/
-/
def option_div (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ :=
  y_wrapped >>= fun y ↦
    if y = 0 then
      none
    else
      x_wrapped >>= fun x ↦ some <| x / y

#eval option_div (some 3) (some 0)

def option_div' (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ := do
  let x ← x_wrapped
  let y ← y_wrapped
  if y = 0 then none else some <| x / y

/-- Even the identity monad is powerful! -/
def Array.insSort [LinearOrder α] (A : Array α) := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:i] do
      have := Membership.get_elem_helper hi rfl
      if A[i - j] < A[i - j - 1] then
        A := A.swap (i - j - 1) (i - j)
      else
        break
  return A.toArray

/-- List monad demo -/
def UpToN (xs : List ℕ) : List ℕ := do
  let x ← xs
  let y ← List.range x
  return y

#eval UpToN [1, 2, 3]

/-
Sadly, in general monads do not compose 😿

https://carlo-hamalainen.net/2014/01/02/applicatives-compose-monads-do-not/

However, in some cases we can use monad transformers to compose them.

TODO: More about monad transformers
-/


-- Equivalent definition using "fish"
#check Bind.kleisliRight
-- Equivalent definition using "join"
#check joinM
-- Exercise: Implement bind using fish

/-
"A monad is just a monoid in the category of endofunctors"

In fact, there is a bijection between the two!

https://old.reddit.com/r/math/comments/ap25mr/a_monad_is_a_monoid_in_the_category_of/

The category of Lean endofunctors
Objects: Endofunctors
Morphisms: Natural transformations (we showed earlier that vertical composition produces another natural transformation)
-/

/-- Every object has an identity morphism -/
instance [Functor F] [LawfulFunctor F] : Natural F F id :=
  ⟨by simp⟩

/-- Vertical composition is associative -/
lemma nat_trans_comp_assoc (η : NaturalType f g) (μ : NaturalType g h) (ν : NaturalType h i) [Functor f] [LawfulFunctor f] [Functor g] [LawfulFunctor g] [Functor h] [LawfulFunctor h] [Functor i] [LawfulFunctor i] :
    ((ν ∘ μ) ∘ η) x = (ν ∘ μ ∘ η) x := by
  simp only [Function.comp_assoc]

-- Note that monoids from set theory are not the same thing as monoids in category theory!
#check Monoid

/-
A monoidal category is a category C equipped with a tensor product ⨂ from C × C to C and an identity object I with certain properties.

For the category of Lean endofunctors, let ⨂ be functor composition and I be the identity functor `Id`.
-/

/-- ⨂ is obviously associative -/
lemma functor_comp_assoc [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] [Functor H] [LawfulFunctor H] : (F ∘ G) ∘ H = F ∘ G ∘ H := by
  apply Function.comp_assoc

/-- `Id` is an identity for ⨂ -/
lemma functor_left_id [Functor F] [LawfulFunctor F] : id ∘ F = F := by
  simp

/-- `Id` is an identity for ⨂ -/
lemma functor_right_id [Functor F] [LawfulFunctor F] : F ∘ id = F := by
  simp

-- The coherence conditions (insert scary pentagon diagram here) are automatically satisfied because here the associator and unitor natural isomorphisms are equalities.

/-
A monoidal object is an object M in (C, ⨂, I) with an arrow μ from M ⨂ M to M and η from I to M such that μ is associative and η is an identity with respect to μ.

A monoidal object in the category of Lean endofunctors is a functor with natural transformations `join` (corresponding to μ) and `pure` (η) with the following properties:
-/

class EndofunctorMonoid M extends Functor M, LawfulFunctor M where
  join : NaturalType (M ∘ M) M
  pure : NaturalType Id M
  join_pure : (join ∘ pure) x = x
  -- When using <$>, Lean synthesizes the wrong type class instance for some weird reason
  join_map_pure : (join ∘ (map pure ·)) x = x
  join_join : (join ∘ (map join ·)) x = (join ∘ join) x

@[simp]
def bindFromJoin [EndofunctorMonoid M] (join : NaturalType (M ∘ M) M) (x : M α) (f : α → M β) :=
  join (Functor.map (f := M) f x)

@[simp]
instance [EndofunctorMonoid M] : Monad M where
  pure := EndofunctorMonoid.pure
  bind := bindFromJoin EndofunctorMonoid.join

-- TODO: This only works for `m` from `Type u → Type u`, but monads can be `Type u → Type v` in Lean
/-- A monoid in the category of endofunctors is a monad -/
instance [EndofunctorMonoid M] [J : Natural (M ∘ M) M EndofunctorMonoid.join] [P : Natural Id M EndofunctorMonoid.pure] : LawfulMonad M :=
  LawfulMonad.mk' M id_map
    (pure_bind := fun x f ↦ by
      simpa [P.naturality, Functor.map] using EndofunctorMonoid.join_pure)
    (bind_assoc := fun x f g ↦ by
      have := EndofunctorMonoid.join_join (x := (fun a ↦ Functor.map (f := M) g (f a)) <$> x)
      simp at this
      simp [J.naturality, ← this])
    (map_const := by simp [map_const])
    (bind_pure_comp := fun f x ↦ by
      simpa using EndofunctorMonoid.join_map_pure (x := f <$> x))

@[simp]
def joinFromBind [Monad M] (bind : {α β : Type u} → M α → (α → M β) → M β) (x : M (M α)) :=
  bind x id

/-- A monad is a monoid in the category of endofunctors -/
@[simp]
instance [Monad M] [LawfulMonad M] : EndofunctorMonoid M where
  pure := pure
  join := joinFromBind bind
  join_pure := by simp
  join_map_pure := by simp
  join_join := by simp

instance [Monad M] [LawfulMonad M] : Natural (M ∘ M) M EndofunctorMonoid.join :=
  ⟨by simp⟩

instance [Monad M] [LawfulMonad M] : Natural Id M EndofunctorMonoid.pure :=
  ⟨by simp [Functor.map]⟩

/-- `bindFromJoin` and `joinFromBind` form a bijection -/
theorem bind_join_equiv [Monad M] [LawfulMonad M] : (bindFromJoin (M := M) (joinFromBind bind)) x f = bind x f := by
  simp

theorem bind_join_equiv' [E : EndofunctorMonoid M] : joinFromBind (bindFromJoin E.join) x = E.join x := by
  simp


-- TODO: Monads and adjunctions

-- TODO: String diagrams


-- Unlike Haskell, Lean is powerful enough that we can also use it for doing category theory in any category, not just the category Lean
#check CategoryTheory.Category

#check CategoryTheory.Functor

#check CategoryTheory.yoneda

#check CategoryTheory.Monad

#check CategoryTheory.Monad.monadMonEquiv
