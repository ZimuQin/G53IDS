module FT where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List using (List; []; _∷_; foldr; foldl; length; _++_)
open import Function using (_∘_; flip)
open import Data.Bool


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

record Reduce (F : Set → Set) : Set₁ where
  field
    reducer : {A : Set} {B : Set} → (A → B → B) → F A → B → B
    reducel : {A : Set} {B : Set} → (B → A → B) → B → F A → B

open Reduce {{...}} public

toList : {F : Set → Set} {{r : Reduce F}} {A : Set} → F A → List A
toList s = reducer _∷_ s []

reduceList : Reduce List
reduceList = record { reducer = λ f xs z → foldr f z xs ; reducel = foldl }

monoidNat1 : Monoid ℕ
monoidNat1 = record { ∅ = zero ; _⊕_ = _+_ ;
                          isMonoid = record { id1 = id1 ; id2 = λ x → refl ; assoc = assoc }}
                                      where
                                              id1 : (x : ℕ) → x ≡ x + zero
                                              id1 zero = refl
                                              id1 (suc x) = cong suc (id1 x)
                                              
                                              assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
                                              assoc zero y z = refl
                                              assoc (suc x) y z = cong suc (assoc x y z)

monoidList : {A : Set} → Monoid (List A)
monoidList = record { ∅ = [] ; _⊕_ = _++_ ;
                          isMonoid = record { id1 = id1 ; id2 = λ x → refl ; assoc = assoc }}
                                      where
                                              id1 : {A : Set} → (x : List A) → x ≡ x ++ []
                                              id1 [] = refl
                                              id1 (x ∷ xs) = cong (_∷_ x) (id1 xs)
                                              
                                              assoc : {A : Set} → (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
                                              assoc [] y z = refl
                                              assoc (x ∷ xs) y z = cong (_∷_ x) (assoc xs y z)



data Node (A : Set) : ℕ → Set where
  Node2 : {n : ℕ} → Node A n → Node A n → Node A (suc n)
  Node3 : {n : ℕ} → Node A n → Node A n → Node A n → Node A (suc n)
  Leaf : A → Node A zero

data Digit (A : Set) : Set where
  One : A → Digit A
  Two : A → A → Digit A
  Three : A → A → A → Digit A
  Four : A → A → A → A → Digit A

data FingerTree (A : Set) (n : ℕ) : Set where
  Empty : FingerTree A n
  Single : Node A n → FingerTree A n
  Deep : Digit (Node A n) → FingerTree A (suc n) → Digit (Node A n) → FingerTree A n

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

reduceDigit : Reduce Digit
reduceDigit = record { reducer = reducerDigit ; reducel = reducelDigit }

reducerNode : {A : Set} {B : Set} {n : ℕ} → (A → B → B) → Node A n → B → B
reducerNode _⤙_ (Node2 a b) z = reducerNode _⤙_ a
                                  (reducerNode _⤙_ b z)
reducerNode _⤙_ (Node3 a b c) z = reducerNode _⤙_ a
                                    (reducerNode _⤙_ b
                                       (reducerNode _⤙_ c z))
reducerNode _⤙_ (Leaf x) z = x ⤙ z

reducelNode : {A : Set} {B : Set} {n : ℕ} → (B → A → B) → B → Node A n → B
reducelNode _⤚_ z (Node2 b a) = reducelNode _⤚_ (reducelNode _⤚_ z b) a
reducelNode _⤚_ z (Node3 c b a) = reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ z c) b) a
reducelNode _⤚_ z (Leaf x) = z ⤚ x

reduceNode : {n : ℕ} → Reduce (λ A → Node A n)
reduceNode = record { reducer = reducerNode ; reducel = reducelNode }

reducerFingerTree : {A : Set} {B : Set} {n : ℕ} → (A → B → B)
                                                → FingerTree A n → B → B
reducerFingerTree _⤙_ Empty z = z
reducerFingerTree _⤙_ (Single x) z = reducerNode _⤙_ x z
reducerFingerTree _⤙_ (Deep pr m sf) z = (reducerDigit ∘ reducerNode) _⤙_ pr
                                            (reducerFingerTree _⤙_ m
                                               ((reducerDigit ∘ reducerNode) _⤙_ sf z))

reducelFingerTree : {A : Set} {B : Set} {n : ℕ} → (B → A → B) → B → FingerTree A n → B
reducelFingerTree _⤚_ z Empty = z
reducelFingerTree _⤚_ z (Single x) = reducelNode _⤚_ z x
reducelFingerTree _⤚_ z (Deep pr m sf) = (reducelDigit ∘ reducelNode) _⤚_
                                           (reducelFingerTree _⤚_ ((reducelDigit ∘ reducelNode) _⤚_ z pr) m)
                                           sf

reduceFingerTree : {n : ℕ} → Reduce (λ A → FingerTree A n)
reduceFingerTree = record { reducer = reducerFingerTree ; reducel = reducelFingerTree }

lemmaDigit : {A B : Set}
            (d : Digit A) (op : A → B → B) (z : B) →
            reducer {{reduceDigit}} op d z ≡
            reducer {{reduceList}} op (toList {{reduceDigit}} d) z
lemmaDigit (One a) op z = refl
lemmaDigit (Two a b) op z = refl
lemmaDigit (Three a b c) op z = refl
lemmaDigit (Four a b c d) op z = refl

listAssoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
listAssoc [] ys zs = refl
listAssoc (x ∷ xs) ys zs = cong (_∷_ x) (listAssoc xs ys zs)

lemmaList : {A B : Set} (xs : List A) (ys : List A) (op : A → B → B) (z : B) →  reducer {{reduceList}} op xs
                                     (reducer {{reduceList}} op ys z) ≡ reducer {{reduceList}} op (xs ++ ys) z
lemmaList [] ys op z = refl
lemmaList (x ∷ xs) ys op z = cong (op x) (lemmaList xs ys op z)

lemmaNode1 : {A : Set} {n : ℕ} (a : Node A n) (xs : List A) → reducerNode _∷_ a xs ≡ reducerNode _∷_ a [] ++ xs
lemmaNode1 (Node2 a b) xs = begin
                             reducerNode _∷_ a (reducerNode _∷_ b xs) ≡⟨
                             cong (reducerNode _∷_ a) (lemmaNode1 b xs) ⟩
                             reducerNode _∷_ a (reducerNode _∷_ b [] ++ xs) ≡⟨
                             lemmaNode1 a (reducerNode _∷_ b [] ++ xs) ⟩
                             reducerNode _∷_ a [] ++ reducerNode _∷_ b [] ++ xs ≡⟨
                             sym (listAssoc (reducerNode _∷_ a []) (reducerNode _∷_ b []) xs) ⟩
                             (reducerNode _∷_ a [] ++ reducerNode _∷_ b []) ++ xs ≡⟨
                             cong (flip _++_ xs) (sym (lemmaNode1 a (reducerNode _∷_ b []))) ⟩
                             reducerNode _∷_ a (reducerNode _∷_ b []) ++ xs ∎
lemmaNode1 (Node3 a b c) xs = begin
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c xs)) ≡⟨
                               cong (λ x → reducerNode _∷_ a (reducerNode _∷_ b x))
                               (lemmaNode1 c xs)
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c [] ++ xs))
                               ≡⟨
                               cong (reducerNode _∷_ a) (lemmaNode1 b (reducerNode _∷_ c [] ++ xs))
                               ⟩
                               reducerNode _∷_ a
                               (reducerNode _∷_ b [] ++ reducerNode _∷_ c [] ++ xs)
                               ≡⟨ lemmaNode1 a (reducerNode _∷_ b [] ++ reducerNode _∷_ c [] ++ xs)
                               ⟩
                               reducerNode _∷_ a [] ++
                               reducerNode _∷_ b [] ++ reducerNode _∷_ c [] ++ xs
                               ≡⟨
                               cong (_++_ (reducerNode _∷_ a []))
                               (sym (listAssoc (reducerNode _∷_ b []) (reducerNode _∷_ c []) xs))
                               ⟩
                               reducerNode _∷_ a [] ++
                               (reducerNode _∷_ b [] ++ reducerNode _∷_ c []) ++ xs
                               ≡⟨
                               sym
                               (listAssoc (reducerNode _∷_ a [])
                                (reducerNode _∷_ b [] ++ reducerNode _∷_ c []) xs)
                               ⟩
                               (reducerNode _∷_ a [] ++
                                reducerNode _∷_ b [] ++ reducerNode _∷_ c [])
                               ++ xs
                               ≡⟨
                               cong (flip _++_ xs)
                               (sym (lemmaNode1 a (reducerNode _∷_ b [] ++ reducerNode _∷_ c [])))
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b [] ++ reducerNode _∷_ c []) ++
                               xs
                               ≡⟨
                               cong (λ x → reducerNode _∷_ a x ++ xs)
                               (sym (lemmaNode1 b (reducerNode _∷_ c [])))
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c [])) ++ xs
                               ∎
lemmaNode1 (Leaf x) xs = refl

lemmaNode2 : {n : ℕ} {A B : Set}
            (node : Node A n) (op : A → B → B) (z : B) →
            reducer {{reduceNode}} op node z ≡
            reducer {{reduceList}} op (toList {{reduceNode}} node) z
lemmaNode2 (Node2 a b) op z =
  begin
    reducerNode op a (reducerNode op b z) ≡⟨
    lemmaNode2 a op (reducerNode op b z) ⟩
    reducer {{reduceList}} op (toList {{reduceNode}} a)
    (reducerNode op b z)
    ≡⟨
    cong (reducer {{reduceList}} op (toList {{reduceNode}} a))
    (lemmaNode2 b op z)
    ⟩
    reducer {{reduceList}} op (toList {{reduceNode}} a)
    (reducer {{reduceList}} op (toList {{reduceNode}} b) z)
    ≡⟨
    lemmaList (toList {{reduceNode}} a) (toList {{reduceNode}} b) op z
    ⟩
    reducer {{reduceList}} op
    (reducerNode _∷_ a [] ++ reducerNode _∷_ b []) z
    ≡⟨
    cong (λ x → reducer {{reduceList}} op x z)
    (sym (lemmaNode1 a (reducerNode _∷_ b [])))
    ⟩ reducer {{reduceList}} op (toList {{reduceNode}} (Node2 a b)) z ∎
lemmaNode2 (Node3 a b c) op z = begin
                               reducerNode op a (reducerNode op b (reducerNode op c z)) ≡⟨
                               lemmaNode2 a op (reducerNode op b (reducerNode op c z)) ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducerNode op b (reducerNode op c z))
                               ≡⟨
                               cong (reducer {{reduceList}} op (toList {{reduceNode}} a))
                               (lemmaNode2 b op (reducerNode op c z))
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducer {{reduceList}} op (toList {{reduceNode}} b)
                                (reducerNode op c z))
                               ≡⟨
                               cong
                               (λ x →
                                  reducer {{reduceList}} op (toList {{reduceNode}} a)
                                  (reducer {{reduceList}} op (toList {{reduceNode}} b) x))
                               (lemmaNode2 c op z)
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducer {{reduceList}} op (toList {{reduceNode}} b)
                                (reducer {{reduceList}} op (toList {{reduceNode}} c) z))
                               ≡⟨
                               cong (reducer {{reduceList}} op (toList {{reduceNode}} a))
                               (lemmaList (toList {{reduceNode}} b) (toList {{reduceNode}} c) op
                                z)
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducer {{reduceList}} op
                                (toList {{reduceNode}} b ++ toList {{reduceNode}} c) z)
                               ≡⟨
                               cong
                               (λ x →
                                  reducer {{reduceList}} op (toList {{reduceNode}} a)
                                  (reducer {{reduceList}} op x z))
                               (sym (lemmaNode1 b (reducerNode _∷_ c [])))
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducer {{reduceList}} op
                                (reducerNode _∷_ b (reducerNode _∷_ c [])) z)
                               ≡⟨
                               lemmaList (toList {{reduceNode}} a)
                               (reducerNode _∷_ b (reducerNode _∷_ c [])) op z
                               ⟩
                               reducer {{reduceList}} op
                               (toList {{reduceNode}} a ++
                                reducerNode _∷_ b (reducerNode _∷_ c []))
                               z
                               ≡⟨
                               cong (λ x → reducer {{reduceList}} op x z)
                               (sym (lemmaNode1 a (reducerNode _∷_ b (reducerNode _∷_ c []))))
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} (Node3 a b c)) z ∎
lemmaNode2 (Leaf x) op z = refl

lemmaDigitNode : {A : Set} {n : ℕ} (d : Digit (Node A n)) (xs : List A) → (reducerDigit ∘ reducerNode) _∷_ d xs ≡ (reducerDigit ∘ reducerNode) _∷_ d [] ++ xs
lemmaDigitNode (One a) xs = lemmaNode1 a xs
lemmaDigitNode (Two a b) xs = lemmaNode1 (Node2 a b) xs
lemmaDigitNode (Three a b c) xs = lemmaNode1 (Node3 a b c) xs
lemmaDigitNode (Four a b c d) xs = lemmaNode1 (Node2 (Node2 a b) (Node2 c d)) xs

lemmaDigitNode2 : {n : ℕ} {A B : Set}
            (d : Digit (Node A n)) (op : A → B → B) (z : B) →
            (reducerDigit ∘ reducerNode) op d z ≡
            reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ d []) z
lemmaDigitNode2 (One a) op z = lemmaNode2 a op z
lemmaDigitNode2 (Two a b) op z = lemmaNode2 (Node2 a b) op z
lemmaDigitNode2 (Three a b c) op z = lemmaNode2 (Node3 a b c) op z
lemmaDigitNode2 (Four a b c d) op z = lemmaNode2 (Node2 (Node2 a b) (Node2 c d)) op z

lemmaFingerTree1 : {A : Set} {n : ℕ} (ft : FingerTree A n) (xs : List A) → reducerFingerTree _∷_ ft xs ≡ reducerFingerTree _∷_ ft [] ++ xs
lemmaFingerTree1 Empty xs = refl
lemmaFingerTree1 (Single x) xs = lemmaNode1 x xs
lemmaFingerTree1 (Deep pr m sf) xs = begin
                                      (reducerDigit ∘ reducerNode) _∷_ pr
                                      (reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf xs))
                                      ≡⟨ lemmaDigitNode pr (reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf xs))
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                      reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf xs)
                                      ≡⟨
                                      cong (_++_ ((reducerDigit ∘ reducerNode) _∷_ pr []))
                                      (lemmaFingerTree1 m ((reducerDigit ∘ reducerNode) _∷_ sf xs))
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                      reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf xs
                                      ≡⟨
                                      cong
                                      (λ x → (reducerDigit ∘ reducerNode) _∷_ pr [] ++ reducerFingerTree _∷_ m [] ++ x)
                                      (lemmaDigitNode sf xs)
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                      reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf [] ++ xs
                                      ≡⟨
                                      cong (_++_ ((reducerDigit ∘ reducerNode) _∷_ pr []))
                                      (sym
                                       (listAssoc (reducerFingerTree _∷_ m []) ((reducerDigit ∘ reducerNode) _∷_ sf [])
                                        xs))
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                      (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf []) ++ xs
                                      ≡⟨
                                      sym
                                      (listAssoc ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                       (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf []) xs)
                                      ⟩
                                      ((reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                       reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf [])
                                      ++ xs
                                      ≡⟨
                                      cong (flip _++_ xs)
                                      (sym
                                       (lemmaDigitNode pr
                                        (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf [])))
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr
                                      (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf [])
                                      ++ xs
                                      ≡⟨
                                      cong (λ x → (reducerDigit ∘ reducerNode) _∷_ pr x ++ xs)
                                      (sym (lemmaFingerTree1 m ((reducerDigit ∘ reducerNode) _∷_ sf [])))
                                      ⟩
                                      (reducerDigit ∘ reducerNode) _∷_ pr
                                      (reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf []))
                                      ++ xs
                                      ∎
                                      
lemmaFingerTree2 : {A : Set} {n : ℕ} (pr : Digit (Node A n)) (m : FingerTree A (suc n)) (sf : Digit (Node A n)) → toList {{reduceFingerTree}} (Deep pr m sf) ≡ (reducerDigit ∘ reducerNode) _∷_ pr [] ++ toList {{reduceFingerTree}} m ++ (reducerDigit ∘ reducerNode) _∷_ sf []
lemmaFingerTree2 pr m sf = begin
                    (reducerDigit ∘ reducerNode) _∷_ pr
                    (reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf []))
                    ≡⟨ lemmaDigitNode pr (reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf []))
                    ⟩
                    (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                    reducerFingerTree _∷_ m ((reducerDigit ∘ reducerNode) _∷_ sf [])
                    ≡⟨
                    cong (_++_ ((reducerDigit ∘ reducerNode) _∷_ pr []))
                    (lemmaFingerTree1 m ((reducerDigit ∘ reducerNode) _∷_ sf []))
                    ⟩
                    (reducerDigit ∘ reducerNode) _∷_ pr [] ++
                    reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf []
                    ∎

lemmaFingerTree3 : {n : ℕ} {A B : Set}
            (ft : FingerTree A n) (op : A → B → B) (z : B) →
            reducer {{reduceFingerTree}} op ft z ≡
            reducer {{reduceList}} op (toList {{reduceFingerTree}} ft) z
lemmaFingerTree3 Empty op z = refl
lemmaFingerTree3 (Single x) op z = lemmaNode2 x op z
lemmaFingerTree3 (Deep pr m sf) op z = begin
                                (reducerDigit ∘ reducerNode) op pr (reducerFingerTree op m ((reducerDigit ∘ reducerNode) op sf z))
                                ≡⟨ lemmaDigitNode2 pr op (reducerFingerTree op m ((reducerDigit ∘ reducerNode) op sf z)) ⟩
                                reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                (reducerFingerTree op m ((reducerDigit ∘ reducerNode) op sf z))
                                ≡⟨
                                cong (reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr []))
                                (lemmaFingerTree3 m op ((reducerDigit ∘ reducerNode) op sf z))
                                ⟩
                                reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                (reducer {{reduceList}} op (toList {{reduceFingerTree}} m)
                                 ((reducerDigit ∘ reducerNode) op sf z))
                                ≡⟨
                                cong
                                (λ x →
                                   reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                   (reducer {{reduceList}} op (toList {{reduceFingerTree}} m) x))
                                (lemmaDigitNode2 sf op z)
                                ⟩
                                reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                (reducer {{reduceList}} op (reducerFingerTree _∷_ m [])
                                 (reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ sf []) z))
                                ≡⟨
                                cong (reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr []))
                                (lemmaList (reducerFingerTree _∷_ m []) ((reducerDigit ∘ reducerNode) _∷_ sf []) op
                                 z)
                                ⟩
                                reducer {{reduceList}} op ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                (reducer {{reduceList}} op
                                 (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf []) z)
                                ≡⟨
                                lemmaList ((reducerDigit ∘ reducerNode) _∷_ pr [])
                                (reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf []) op z
                                ⟩
                                reducer {{reduceList}} op
                                ((reducerDigit ∘ reducerNode) _∷_ pr [] ++
                                 reducerFingerTree _∷_ m [] ++ (reducerDigit ∘ reducerNode) _∷_ sf [])
                                z
                                ≡⟨
                                cong (λ x → reducer {{reduceList}} op x z) (sym (lemmaFingerTree2 pr m sf))
                                ⟩
                                reducer {{reduceList}} op
                                (toList {{reduceFingerTree}} (Deep pr m sf)) z
                                ∎

infixr 5 _◁_
_◁_ : {A : Set} {n : ℕ} → Node A n → FingerTree A n → FingerTree A n
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

makeList : (n : ℕ) → List ℕ
makeList zero = []
makeList (suc n) = makeList n ++ (suc n) ∷ []

_◁′_ : {F : Set → Set} {{r : Reduce F}} {A : Set} {n : ℕ} → F (Node A n) → FingerTree A n → FingerTree A n
_◁′_ = reducer _◁_

_▷′_ : {F : Set → Set} {{r : Reduce F}} {A : Set} {n : ℕ} → FingerTree A n → F (Node A n) → FingerTree A n
_▷′_ = reducel _▷_

toTree : {F : Set → Set} {{r : Reduce F}} {A : Set} → F A → FingerTree A zero
toTree s = reducer (_◁_ ∘ Leaf) s Empty

digitToTree : {A : Set} {n : ℕ} → Digit (Node A n) → FingerTree A n
digitToTree d = _◁′_ {{reduceDigit}} d Empty

data ViewL (S : Set → Set) (A : Set) : Set where
  NilL : ViewL S A
  ConsL : A → S A → ViewL S A


headDigit : {A : Set} → Digit A → A
headDigit (One a) = a
headDigit (Two a b) = a
headDigit (Three a b c) = a
headDigit (Four a b c d) = a

data NDigit (A : Set) : Set where
  Zero : NDigit A
  One : A → NDigit A
  Two : A → A → NDigit A
  Three : A → A → A → NDigit A
  Four : A → A → A → A → NDigit A

tailDigit : {A : Set} → Digit A → NDigit A
tailDigit (One a) = Zero
tailDigit (Two a b) = One b
tailDigit (Three a b c) = Two b c
tailDigit (Four a b c d) = Three b c d

nodeToDigit : {A : Set} {n : ℕ} → Node A (suc n) → Digit (Node A n)
nodeToDigit (Node2 a b) = Two a b
nodeToDigit (Node3 a b c) = Three a b c

mutual
  viewL : {A : Set} {n : ℕ} → FingerTree A n → ViewL (λ _ → FingerTree A n) (Node A n)
  viewL Empty = NilL
  viewL (Single x) = ConsL x Empty
  viewL (Deep pr m sf) = ConsL (headDigit pr) (deepL (tailDigit pr) m sf)
  
  deepL : {A : Set} {n : ℕ} → NDigit (Node A n) → FingerTree A (suc n) → Digit (Node A n) → FingerTree A n
  deepL Zero m sf with viewL m
  ... | NilL = digitToTree sf
  ... | ConsL a m′ = Deep (nodeToDigit a) m′ sf
  deepL (One a) m sf = Deep (One a) m sf
  deepL (Two a b) m sf = Deep (Two a b) m sf
  deepL (Three a b c) m sf = Deep (Three a b c) m sf
  deepL (Four a b c d) m sf = Deep (Four a b c d) m sf

isEmpty : {A : Set} {n : ℕ} → FingerTree A n → Bool
isEmpty t with viewL t
... | NilL = true
... | ConsL _ _ = false

headL : {A : Set} {n : ℕ} (t : FingerTree A n) {lemma : isEmpty t ≡ false} → Node A n
headL t {_} with viewL t
headL t {}  | NilL
headL t {_} | ConsL a _ = a

tailL : {A : Set} {n : ℕ} (t : FingerTree A n) → FingerTree A n
tailL t with viewL t
... | NilL = Empty
... | ConsL _ x′ = x′

data ViewR (S : Set → Set) (A : Set) : Set where
  NilR : ViewR S A
  ConsR : A → S A → ViewR S A


lastDigit : {A : Set} → Digit A → A
lastDigit (One a) = a
lastDigit (Two a b) = b
lastDigit (Three a b c) = c
lastDigit (Four a b c d) = d

initDigit : {A : Set} → Digit A → NDigit A
initDigit (One a) = Zero
initDigit (Two a b) = One a
initDigit (Three a b c) = Two a b
initDigit (Four a b c d) = Three a b c

mutual
  viewR : {A : Set} {n : ℕ} → FingerTree A n → ViewR (λ _ → FingerTree A n) (Node A n)
  viewR Empty = NilR
  viewR (Single x) = ConsR x Empty
  viewR (Deep pr m sf) = ConsR (lastDigit sf) (deepR pr m (initDigit sf))
  
  deepR : {A : Set} {n : ℕ} → Digit (Node A n) → FingerTree A (suc n) → NDigit (Node A n) → FingerTree A n
  deepR pr m Zero with viewR m
  ... | NilR = digitToTree pr
  ... | ConsR a m′ = Deep pr m′ (nodeToDigit a)
  deepR pr m (One a) = Deep pr m (One a)
  deepR pr m (Two a b) = Deep pr m (Two a b)
  deepR pr m (Three a b c) = Deep pr m (Three a b c)
  deepR pr m (Four a b c d) = Deep pr m (Four a b c d)

headR : {A : Set} {n : ℕ} (t : FingerTree A n) {lemma : isEmpty t ≡ false} → Node A n
headR t {_} with viewR t | inspect viewR t
headR Empty {}       | NilR | _
headR (Single x)     | NilR | [ () ]
headR (Deep pr m sf) | NilR | [ () ]
headR t {_}          | ConsR a _ | _ = a

tailR : {A : Set} {n : ℕ} (t : FingerTree A n) → FingerTree A n
tailR t with viewR t
... | NilR = Empty
... | ConsR _ x′ = x′

infixr 5 _∷_
data List⁺ (A : Set) : Set where
  [_] : (x : A) → List⁺ A
  _∷_ : (x : A) (xs : List⁺ A) → List⁺ A

_⁺++_ : {A : Set} → List⁺ A → List A → List⁺ A
[ x ] ⁺++ [] = [ x ]
[ x ] ⁺++ (y ∷ ys) = x ∷ ([ y ] ⁺++ ys)
(x ∷ xs) ⁺++ ys = x ∷ (xs ⁺++ ys)

data List⁺⁺ (A : Set) : Set where
  [_,_] : (x y : A) → List⁺⁺ A
  _∷_ : (x : A) (xs : List⁺⁺ A) → List⁺⁺ A

_⁺++⁺_ : {A : Set} → List⁺ A → List⁺ A → List⁺⁺ A
[ x ] ⁺++⁺ [ y ] = [ x , y ]
[ x ] ⁺++⁺ (y ∷ ys) = x ∷ ([ y ] ⁺++⁺ ys)
(x ∷ xs) ⁺++⁺ ys = x ∷ (xs ⁺++⁺ ys)

toList⁺ : ∀ {A : Set} → Digit A → List⁺ A
toList⁺ (One a)        = [ a ]
toList⁺ (Two a b)      = a ∷ [ b ]
toList⁺ (Three a b c)  = a ∷ b ∷ [ c ]
toList⁺ (Four a b c d) = a ∷ b ∷ c ∷ [ d ]

nodes : {A : Set} {n : ℕ} → List⁺⁺ (Node A n) → List (Node A (suc n))
nodes [ a , b ]           = (Node2 a b) ∷ []
nodes (a ∷ [ b , c ])     = (Node3 a b c) ∷ []
nodes (a ∷ b ∷ [ c , d ]) = (Node2 a b) ∷ (Node2 c d) ∷ []
nodes (a ∷ b ∷ c ∷ xs)    = (Node3 a b c) ∷ (nodes xs)

app3 : {A : Set} {n : ℕ} → FingerTree A n → List (Node A n) → FingerTree A n → FingerTree A n
app3 Empty ts xs = _◁′_ {{reduceList}} ts xs
app3 xs ts Empty = _▷′_ {{reduceList}} xs ts
app3 (Single x) ts xs = x ◁ _◁′_ {{reduceList}} ts xs
app3 xs ts (Single x) = _▷′_ {{reduceList}} xs ts ▷ x
app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) = Deep pr1 (app3 m1 (nodes ((toList⁺ sf1 ⁺++ ts) ⁺++⁺ toList⁺ pr2)) m2) sf2

_⋈_ : {A : Set} {n : ℕ} → FingerTree A n → FingerTree A n → FingerTree A n
xs ⋈ ys = app3 xs [] ys

lemmax1 : {A B : Set} {n : ℕ}
            (ft : FingerTree A n) (node : Node A n) (op : A → B → B)
            (z : B) →
            reducerFingerTree op (node ◁ ft) z ≡
            reducerNode op node (reducerFingerTree op ft z)
lemmax1 Empty a op z = refl
lemmax1 (Single x) a op z = refl
lemmax1 (Deep (One b) m sf) a op z = refl
lemmax1 (Deep (Two b c) m sf) a op z = refl
lemmax1 (Deep (Three b c d) m sf) a op z = refl
lemmax1 (Deep (Four b c d e) m sf) a op z =
  cong (λ x → reducerNode op a (reducerNode op b x))
    (lemmax1 m (Node3 c d e) op ((reducerDigit ∘ reducerNode) op sf z))

lemmax2 : {A B : Set}
            (xs : List A) (op : A → B → B) (z : B) →
            reducer {{reduceFingerTree}} op (toTree {{reduceList}} xs) z ≡
            reducer {{reduceList}} op xs z
lemmax2 [] op z = refl
lemmax2 (x ∷ xs) op z = trans (lemmax1 (toTree {{reduceList}} xs) (Leaf x) op z)
                          (cong (op x) (lemmax2 xs op z))


lemmax : {A : Set}
           (xs : List A) →
           toList {{reduceFingerTree}} (toTree {{reduceList}} xs) ≡ xs
lemmax xs = trans (lemmax2 xs _∷_ []) (lemma xs)
  where lemma : {A : Set} (xs : List A) → reducer {{reduceList}} _∷_ xs [] ≡ xs
        lemma [] = refl
        lemma (x ∷ xs) = cong (_∷_ x) (lemma xs)
