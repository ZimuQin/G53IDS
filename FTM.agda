module FTM where

open import Data.Nat
open import Relation.Binary.PropositionalEquality


record IsMonoid {A : Set} (∅ : A) (_⊕_ : A → A → A) : Set where
  field
    id1 : (x : A) → x ≡ x ⊕ ∅
    id2 : (x : A) → x ≡ ∅ ⊕ x
    assoc : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

record Monoid (A : Set) : Set where
  field
    ∅ : A
    _⊕_ : A → A → A
    isMonoid : IsMonoid ∅ _⊕_


open Monoid {{...}} public

record ∃ (a : Set) (P : a -> Set) : Set where
  field
    witness : a
    proof   : P witness


data Node {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  Node2 : {v1 v2 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A (v1 ⊕ v2) (suc n)
  Node3 : {v1 v2 v3 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → Node A ((v1 ⊕ v2) ⊕ v3) (suc n)
  Leaf : A → Node A ∅ zero

data Digit (A : Set) : Set where
  One : A → Digit A
  Two : A → A → Digit A
  Three : A → A → A → Digit A
  Four : A → A → A → A → Digit A

data FingerTree {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  Empty : {v : V} {n : ℕ} → FingerTree A v n
  Single : {v : V} {n : ℕ} → Node A v n → FingerTree A v n
  Deep : {v1 v2 v3 : V} {n : ℕ} → Digit (Node A v1 n) → FingerTree A v2 (suc n) → Digit (Node A v3 n) → FingerTree A ((v1 ⊕ v2) ⊕ v3) n

infixr 5 _◁_
_◁_ : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v1 v2 : V} → Node A v1 n → FingerTree A v2 n → _
a ◁ Empty = Single a
a ◁ Single b = Deep (One a) Empty (One b)
a ◁ Deep (One b) m sf = Deep (Two a b) m sf
a ◁ Deep (Two b c) m sf = Deep (Three a b c) m sf
a ◁ Deep (Three b c d) m sf = Deep (Four a b c d) m sf
a ◁ Deep (Four b c d e) m sf = Deep (Two a b) (Node3 c d e ◁ m) sf


infixl 5 _▷_
_▷_ : {A : Set} {n : ℕ} → FingerTree A n → Node A n → FingerTree A n
Empty ▷ a = Single a
Single b ▷ a = Deep (One b) Empty (One a)
Deep pr m (One b) ▷ a = Deep pr m (Two b a)
Deep pr m (Two c b) ▷ a = Deep pr m (Three c b a)
Deep pr m (Three d c b) ▷ a = Deep pr m (Four d c b a)
Deep pr m (Four e d c b) ▷ a = Deep pr (m ▷ Node3 e d c) (Two b a)

open import Data.List
open import Function using (_∘_)

toFingerTree : {A : Set} → List A → FingerTree A zero
toFingerTree = foldl _▷_ Empty ∘ map Leaf

digits : {A : Set} → Digit A → List A
digits (One a) = a ∷ []
digits (Two a b) = a ∷ b ∷ []
digits (Three a b c) = a ∷ b ∷ c ∷ []
digits (Four a b c d) = a ∷ b ∷ c ∷ d ∷ []

nodes : {A : Set} {n : ℕ} → Node A n → List A
nodes (Node2 a b) = nodes a ++ nodes b
nodes (Node3 a b c) = nodes a ++ nodes b ++ nodes c
nodes (Leaf x) = x ∷ []

flatten : {A : Set} {n : ℕ} → FingerTree A n → List A
flatten Empty = []
flatten (Single a) = nodes a
flatten (Deep pr m sf) = concatMap nodes (digits pr) ++ flatten m ++ concatMap nodes (digits sf)
{-
test : {A : Set} → (a : List A) → a ≡ flatten (toFingerTree a)
test [] = refl
test (x ∷ xs) = {!cong (_∷_ x) (test xs) !}
-}
makeList : (n : ℕ) → List ℕ
makeList zero = []
makeList (suc n) = makeList n ++ (suc n) ∷ []

reducerNode : {A : Set} {B : Set} {n : ℕ} → (A → B → B) → Node A n → B → B
reducerNode _⤙_ (Node2 a b) z = reducerNode _⤙_ a (reducerNode _⤙_ b z)
reducerNode _⤙_ (Node3 a b c) z = reducerNode _⤙_ a (reducerNode _⤙_ b (reducerNode _⤙_ c z))
reducerNode _⤙_ (Leaf x) z = x ⤙ z

reducelNode : {A : Set} {B : Set} {n : ℕ} → (B → A → B) → B → Node A n → B
reducelNode _⤚_ z (Node2 b a) = reducelNode _⤚_ (reducelNode _⤚_ z b) a
reducelNode _⤚_ z (Node3 c b a) = reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ z c) b) a
reducelNode _⤚_ z (Leaf x) = z ⤚ x

reducerDigit : {A : Set} {B : Set} → (A → B → B) → Digit A → B → B
reducerDigit _⤙_ (One a) z = a ⤙ z
reducerDigit _⤙_ (Two a b) z = a ⤙ (b ⤙ z)
reducerDigit _⤙_ (Three a b c) z = a ⤙ (b ⤙ (c ⤙ z))
reducerDigit _⤙_ (Four a b c d) z = a ⤙ (b ⤙ (c ⤙ (d ⤙ z)))

reducelDigit : {A : Set} {B : Set} → (B → A → B) → B → Digit A → B
reducelDigit _⤚_ z (One a) = z ⤚ a
reducelDigit _⤚_ z (Two b a) = (z ⤚ b) ⤚ a
reducelDigit _⤚_ z (Three c b a) = ((z ⤚ b) ⤚ c) ⤚ a
reducelDigit _⤚_ z (Four d b c a) = (((z ⤚ d) ⤚ c) ⤚ b) ⤚ a

reducerFingerTree : {A : Set} {B : Set} {n : ℕ} → (A → B → B) → FingerTree A n → B → B
reducerFingerTree _⤙_ Empty z = z
reducerFingerTree _⤙_ (Single x) z = reducerNode _⤙_ x z
reducerFingerTree _⤙_ (Deep pr m sf) z = (reducerDigit ∘ reducerNode) _⤙_ pr
                                                       (reducerFingerTree _⤙_ m ((reducerDigit ∘ reducerNode) _⤙_ sf z))

reducelFingerTree : {A : Set} {B : Set} {n : ℕ} → (B → A → B) → B → FingerTree A n → B
reducelFingerTree _⤚_ z Empty = z
reducelFingerTree _⤚_ z (Single x) = reducelNode _⤚_ z x
reducelFingerTree _⤚_ z (Deep pr m sf) = (reducelDigit ∘ reducelNode) _⤚_
                                           (reducelFingerTree _⤚_ ((reducelDigit ∘ reducelNode) _⤚_ z pr) m)
                                           sf
    

monoidInstance : Monoid ℕ
monoidInstance = record { ∅ = zero ; _⊕_ = _+_ ;
                          isMonoid = record { id1 = id1 ; id2 = λ x → refl ; assoc = assoc }}
                                      where
                                              id1 : (x : ℕ) → x ≡ x + zero
                                              id1 zero = refl
                                              id1 (suc x) = cong suc (id1 x)
                                              
                                              assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
                                              assoc zero y z = refl
                                              assoc (suc x) y z = cong suc (assoc x y z)

                                           

record Reduce (F : Set → Set) : Set₁ where
  field
    reducer : {A : Set} {B : Set} → (A → B → B) → F A → B → B
    reducel : {A : Set} {B : Set} → (B → A → B) → B → F A → B

open Reduce {{...}} public

reduceDigit : Reduce Digit
reduceDigit = record { reducer = reducerDigit ; reducel = reducelDigit }

reduceNode : {A : Set} {n : ℕ} → Reduce (λ A → Node A n) --Reduce (λ Node A n → Node A (suc n))
reduceNode = record { reducer = reducerNode ; reducel = reducelNode }

reduceFingerTree : {A : Set} {n : ℕ} → Reduce (λ A → FingerTree A n)
reduceFingerTree = record { reducer = reducerFingerTree ; reducel = reducelFingerTree }

reduceList : Reduce List
reduceList = record { reducer = λ f xs z → foldr f z xs ; reducel = foldl }

_◁′_ : {F : Set → Set} {{r : Reduce F}} {A : Set} {n : ℕ} → F (Node A n) → FingerTree A n → FingerTree A n
_◁′_ = reducer _◁_

_▷′_ : {F : Set → Set} {{r : Reduce F}} {A : Set} {n : ℕ} → FingerTree A n → F (Node A n) → FingerTree A n
_▷′_ = reducel _▷_

