open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List using (List; []; _∷_; foldr; foldl; length; _++_)
open import Function using (_∘_; flip)
open import Data.Bool
open import Data.Maybe
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; ≡-to-≅; _≇_)

open import Monoid
open import Measured

{- Basic structures -}

data Node {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  Node2 : {v1 v2 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A (v1 ⊕ v2) (suc n)
  Node3 : {v1 v2 v3 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → Node A ((v1 ⊕ v2) ⊕ v3) (suc n)
  Leaf : {v : V} → A → Node A v zero

data Digit {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  One : {v : V} {n : ℕ} → Node A v n → Digit A v n
  Two : {v1 v2 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Digit A (v1 ⊕ v2) n
  Three : {v1 v2 v3 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → Digit A ((v1 ⊕ v2) ⊕ v3) n
  Four : {v1 v2 v3 v4 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → Node A v4 n → Digit A (((v1 ⊕ v2) ⊕ v3) ⊕ v4) n

data FingerTree {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  Empty : {n : ℕ} → FingerTree A ∅ n
  Single : {v : V} {n : ℕ} → Node A v n → FingerTree A v n
  Deep : {v1 v2 v3 : V} {n : ℕ} → Digit A v1 n → FingerTree A v2 (suc n) → Digit A v3 n → FingerTree A ((v1 ⊕ v2) ⊕ v3) n

getNodeV : {A : Set} {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → Node A v n → V
getNodeV {v = v} _ = v

getDigitV : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} → Digit A v n → V
getDigitV {v = v} _ = v

getV : {A : Set} {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → FingerTree A v n → V
getV {v = v} _ = v


{- Subsitute values in the structures -}

substFingerTree : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 : V} → v1 ≡ v2 → FingerTree A v1 n → FingerTree A v2 n
substFingerTree {A} {n} = subst (λ v → FingerTree A v n)

substDigit : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 : V} → v1 ≡ v2 → 
              Digit A v1 n → Digit A v2 n
substDigit {A} {n} = subst (λ v → Digit A v n)

substNode : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 : V} → v1 ≡ v2 → Node A v1 n → Node A v2 n
substNode {A} {n} = subst (λ v → Node A v n)

{- Deque operations -}

infixr 5 _◁_
_◁_ : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v1 v2 : V} → Node A v1 n → FingerTree A v2 n → FingerTree A (v1 ⊕ v2) n
a ◁ Empty = substFingerTree (id1 _) (Single a)
a ◁ Single b = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One a) Empty (One b))
a ◁ Deep (One b) m sf = substFingerTree Monoid.lemma1 (Deep (Two a b) m sf)
a ◁ Deep (Two b c) m sf  = substFingerTree Monoid.lemma2 (Deep (Three a b c) m sf)
a ◁ Deep (Three b c d) m sf = substFingerTree Monoid.lemma3 (Deep (Four a b c d) m sf)
a ◁ Deep (Four b c d e) m sf = substFingerTree Monoid.lemma4 (Deep (Two a b) (Node3 c d e ◁ m) sf)


infixl 5 _▷_
_▷_ :  {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v1 v2 : V} → FingerTree A v1 n → Node A v2 n → FingerTree A (v1 ⊕ v2) n
Empty ▷ a = substFingerTree (id2 _) (Single a)
Single b ▷ a = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One b) Empty (One a))
Deep pr m (One b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Two b a))
Deep pr m (Two c b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Three c b a))
Deep pr m (Three d c b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Four d c b a))
Deep pr m (Four e d c b) ▷ a = substFingerTree Monoid.lemma5 (Deep pr (m ▷ Node3 e d c) (Two b a))


{- Reduce on structures -}

reducerNode : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (A → B → B) → Node A v n → B → B
reducerNode _⤙_ (Node2 a b) z = reducerNode _⤙_ a (reducerNode _⤙_ b z)
reducerNode _⤙_ (Node3 a b c) z = reducerNode _⤙_ a (reducerNode _⤙_ b (reducerNode _⤙_ c z))
reducerNode _⤙_ (Leaf x) z = x ⤙ z

reducelNode : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (B → A → B) → B → Node A v n → B
reducelNode _⤚_ z (Node2 b a) = reducelNode _⤚_ (reducelNode _⤚_ z b) a
reducelNode _⤚_ z (Node3 c b a) = reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ z c) b) a
reducelNode _⤚_ z (Leaf x) = z ⤚ x

reducerDigit : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (A → B → B) → Digit A v n → B → B
reducerDigit _⤙_ (One a) z = reducerNode _⤙_ a z
reducerDigit _⤙_ (Two a b) z = reducerNode _⤙_ a (reducerNode _⤙_ b z)
reducerDigit _⤙_ (Three a b c) z = reducerNode _⤙_ a (reducerNode _⤙_ b (reducerNode _⤙_ c z))
reducerDigit _⤙_ (Four a b c d) z = reducerNode _⤙_ a (reducerNode _⤙_ b (reducerNode _⤙_ c (reducerNode _⤙_ d z)))

reducelDigit : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (B → A → B) → B → Digit A v n → B
reducelDigit _⤚_ z (One a) = reducelNode _⤚_ z a
reducelDigit _⤚_ z (Two b a) = reducelNode _⤚_ (reducelNode _⤚_ z b) a
reducelDigit _⤚_ z (Three c b a) = reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ z c) b) a
reducelDigit _⤚_ z (Four d b c a) = reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ (reducelNode _⤚_ z d) c) b) a

reducerFingerTree : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (A → B → B) → FingerTree A v n → B → B
reducerFingerTree _⤙_ Empty z = z
reducerFingerTree _⤙_ (Single x) z = reducerNode _⤙_ x z
reducerFingerTree _⤙_ (Deep pr m sf) z = reducerDigit _⤙_ pr
                                                       (reducerFingerTree _⤙_ m (reducerDigit _⤙_ sf z))

reducelFingerTree : {A : Set} {B : Set} {n : ℕ} {V : Set} {v : V} {{m : Monoid V}} → (B → A → B) → B → FingerTree A v n → B
reducelFingerTree _⤚_ z Empty = z
reducelFingerTree _⤚_ z (Single x) = reducelNode _⤚_ z x
reducelFingerTree _⤚_ z (Deep pr m sf) = reducelDigit _⤚_
                                           (reducelFingerTree _⤚_ (reducelDigit _⤚_ z pr) m)
                                           sf

listToTree : {V : Set} {{m : Monoid V}} {A : Set} {{mea : Measured A V}} → (xs : List A) → FingerTree A (foldr (_⊕_ ∘ measure) ∅ xs) zero
listToTree [] = Empty
listToTree (x ∷ xs) = Leaf x ◁ listToTree xs

record Reduce (F : Set → Set) : Set₁ where
  field
    reducer : {A : Set} {B : Set} → (A → B → B) → F A → B → B
    reducel : {A : Set} {B : Set} → (B → A → B) → B → F A → B
  toList : {A : Set} → F A → List A
  toList s = reducer _∷_ s []
  toTree : {A : Set} {V : Set} {{m : Monoid V}} {{mea : Measured A V}} (xs : F A) → FingerTree A _ zero
  toTree = listToTree ∘ toList

open Reduce {{...}} public

reduceDigit : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → Reduce (λ A → Digit A v n)
reduceDigit = record { reducer = reducerDigit ; reducel = reducelDigit }


reduceNode : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → Reduce (λ A → Node A v n)
reduceNode = record { reducer = reducerNode ; reducel = reducelNode }

reduceFingerTree : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → Reduce (λ A → FingerTree A v n)
reduceFingerTree = record { reducer = reducerFingerTree ; reducel = reducelFingerTree }

reduceList : Reduce List
reduceList = record { reducer = λ f xs z → foldr f z xs ; reducel = foldl }

digitToTree : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Digit A v n → FingerTree A v n
digitToTree (One x) = Single x
digitToTree (Two a b) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One a) Empty (One b))
digitToTree (Three a b c) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (Two a b) Empty (One c))
digitToTree (Four a b c d) = substFingerTree lemma (Deep (Two a b) Empty (Two c d))
            where lemma : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} → _⊕_ (_⊕_ (_⊕_ v1 v2) ∅) (_⊕_ v3 v4) ≡ _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4
                  lemma {_} {v1} {v2} {v3} {v4} = begin
                                                    _⊕_ (_⊕_ (_⊕_ v1 v2) ∅) (_⊕_ v3 v4) ≡⟨
                                                    cong (flip _⊕_ (_⊕_ v3 v4)) (sym (id1 (_⊕_ v1 v2))) ⟩
                                                    _⊕_ (_⊕_ v1 v2) (_⊕_ v3 v4) ≡⟨ sym (assoc (_⊕_ v1 v2) v3 v4) ⟩
                                                    _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ∎

nodeToTree : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Node A v (suc n) → FingerTree A v n
nodeToTree (Node2 a b) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One a) Empty (One b))
nodeToTree (Node3 a b c) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (Two a b) Empty (One c))

{- Proving lemmas on Reductions -}

cong′ : {I : Set} {i j : I}
       -> (A : I -> Set) {B : {k : I} -> A k -> Set} {x : A i} {y : A j}
       -> i ≡ j
       -> (f : {k : I} -> (x : A k) -> B x)
       -> x ≅ y
       -> f x ≅ f y
cong′ _ refl _ H.refl = H.refl

lemmax1 : {V : Set} {{m : Monoid V}} {A : Set} {v1 v2 : V} {n : ℕ}
            (ft : FingerTree A v1 n) (eq : v1 ≡ v2) →
            substFingerTree eq ft ≅ ft
lemmax1 ft refl = H.refl

lemmax2 : {V : Set} {{m : Monoid V}} {A B : Set} {v1 v2 : V} {n : ℕ}
            (ft : FingerTree A v1 n) (eq : v1 ≡ v2) (op : A → B → B) (z : B) →
            reducerFingerTree op (substFingerTree eq ft) z ≡
            reducerFingerTree op ft z
lemmax2 {A = A} ft eq op z = H.≅-to-≡
                               (cong′ (λ v → FingerTree A v _) (sym eq)
                                (λ t → reducerFingerTree op t z) (lemmax1 ft eq))

lemmax3 : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A B : Set} {n : ℕ}
            (ft : FingerTree A v1 n) (node : Node A v2 n) (op : A → B → B)
            (z : B) →
            reducerFingerTree op (node ◁ ft) z ≡
            reducerNode op node (reducerFingerTree op ft z)
lemmax3 Empty a op z = lemmax2 (Single a) (id1 _) op z
lemmax3 (Single b) a op z = lemmax2 (Deep (One a) Empty (One b))
                              (cong (flip _⊕_ _) (sym (id1 _))) op z
lemmax3 (Deep (One b) m sf) a op z = lemmax2 (Deep (Two a b) m sf) lemma1 op z
lemmax3 (Deep (Two b c) m sf) a op z = lemmax2 (Deep (Three a b c) m sf) lemma2 op z
lemmax3 (Deep (Three b c d) m sf) a op z = lemmax2 (Deep (Four a b c d) m sf) lemma3 op z
lemmax3 (Deep (Four b c d e) m sf) a op z = trans (lemmax2 (Deep (Two a b) (Node3 c d e ◁ m) sf) lemma4 op z)
                                              (cong (λ x → reducerNode op a (reducerNode op b x))
                                               (lemmax3 m (Node3 c d e) op (reducerDigit op sf z)))


lemmax4 : {V : Set} {{m : Monoid V}} {A B : Set} {{mea : Measured A V}}
            (xs : List A) (op : A → B → B) (z : B) →
            reducer {{reduceFingerTree}} op (listToTree xs) z ≡
            reducer {{reduceList}} op xs z
lemmax4 [] op z = refl
lemmax4 (x ∷ xs) op z = trans (lemmax3 (listToTree xs) (Leaf x) op z)
                          (cong (op x) (lemmax4 xs op z))

lemmaList : {A B : Set} (xs : List A) (ys : List A) (op : A → B → B) (z : B) →  reducer {{reduceList}} op xs
                                     (reducer {{reduceList}} op ys z) ≡ reducer {{reduceList}} op (xs ++ ys) z
lemmaList [] ys op z = refl
lemmaList (x ∷ xs) ys op z = cong (op x) (lemmaList xs ys op z)

listAssoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
listAssoc [] ys zs = refl
listAssoc (x ∷ xs) ys zs = cong (_∷_ x) (listAssoc xs ys zs)

lemmaNode : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (a : Node A v n) (xs : List A) → reducerNode _∷_ a xs ≡ reducerNode _∷_ a [] ++ xs
lemmaNode (Node2 a b) xs = begin
                             reducerNode _∷_ a (reducerNode _∷_ b xs) ≡⟨
                             cong (reducerNode _∷_ a) (lemmaNode b xs) ⟩
                             reducerNode _∷_ a (reducerNode _∷_ b [] ++ xs) ≡⟨
                             lemmaNode a (reducerNode _∷_ b [] ++ xs) ⟩
                             reducerNode _∷_ a [] ++ reducerNode _∷_ b [] ++ xs ≡⟨
                             sym (listAssoc (reducerNode _∷_ a []) (reducerNode _∷_ b []) xs) ⟩
                             (reducerNode _∷_ a [] ++ reducerNode _∷_ b []) ++ xs ≡⟨
                             cong (flip _++_ xs) (sym (lemmaNode a (reducerNode _∷_ b []))) ⟩
                             reducerNode _∷_ a (reducerNode _∷_ b []) ++ xs ∎
lemmaNode (Node3 a b c) xs = begin
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c xs)) ≡⟨
                               cong (λ x → reducerNode _∷_ a (reducerNode _∷_ b x))
                               (lemmaNode c xs)
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c [] ++ xs))
                               ≡⟨
                               cong (reducerNode _∷_ a) (lemmaNode b (reducerNode _∷_ c [] ++ xs))
                               ⟩
                               reducerNode _∷_ a
                               (reducerNode _∷_ b [] ++ reducerNode _∷_ c [] ++ xs)
                               ≡⟨ lemmaNode a (reducerNode _∷_ b [] ++ reducerNode _∷_ c [] ++ xs)
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
                               (sym (lemmaNode a (reducerNode _∷_ b [] ++ reducerNode _∷_ c [])))
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b [] ++ reducerNode _∷_ c []) ++
                               xs
                               ≡⟨
                               cong (λ x → reducerNode _∷_ a x ++ xs)
                               (sym (lemmaNode b (reducerNode _∷_ c [])))
                               ⟩
                               reducerNode _∷_ a (reducerNode _∷_ b (reducerNode _∷_ c [])) ++ xs
                               ∎
lemmaNode (Leaf x) xs = refl

lemmax5 : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} {A B : Set}
            (node : Node A v n) (op : A → B → B) (z : B) →
            reducer {{reduceNode}} op node z ≡
            reducer {{reduceList}} op (toList {{reduceNode}} node) z
lemmax5 (Node2 a b) op z = begin
                             reducerNode op a (reducerNode op b z) ≡⟨
                             lemmax5 a op (reducerNode op b z) ⟩
                             reducer {{reduceList}} op (toList {{reduceNode}} a)
                             (reducerNode op b z)
                             ≡⟨
                             cong (reducer {{reduceList}} op (toList {{reduceNode}} a))
                             (lemmax5 b op z)
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
                             (sym (lemmaNode a (reducerNode _∷_ b [])))
                             ⟩ reducer {{reduceList}} op (toList {{reduceNode}} (Node2 a b)) z ∎
lemmax5 (Node3 a b c) op z = begin
                               reducerNode op a (reducerNode op b (reducerNode op c z)) ≡⟨
                               lemmax5 a op (reducerNode op b (reducerNode op c z)) ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducerNode op b (reducerNode op c z))
                               ≡⟨
                               cong (reducer {{reduceList}} op (toList {{reduceNode}} a))
                               (lemmax5 b op (reducerNode op c z))
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} a)
                               (reducer {{reduceList}} op (toList {{reduceNode}} b)
                                (reducerNode op c z))
                               ≡⟨
                               cong
                               (λ x →
                                  reducer {{reduceList}} op (toList {{reduceNode}} a)
                                  (reducer {{reduceList}} op (toList {{reduceNode}} b) x))
                               (lemmax5 c op z)
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
                               (sym (lemmaNode b (reducerNode _∷_ c [])))
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
                               (sym (lemmaNode a (reducerNode _∷_ b (reducerNode _∷_ c []))))
                               ⟩
                               reducer {{reduceList}} op (toList {{reduceNode}} (Node3 a b c)) z ∎
lemmax5 (Leaf x) op z = refl

lemmax6 : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} {A B : Set}
            (d : Digit A v n) (op : A → B → B) (z : B) →
            reducer {{reduceDigit}} op d z ≡
            reducer {{reduceList}} op (toList {{reduceDigit}} d) z
lemmax6 (One a) = lemmax5 a
lemmax6 (Two a b) = lemmax5 (Node2 a b)
lemmax6 (Three a b c) = lemmax5 (Node3 a b c)
lemmax6 (Four a b c d) = lemmax5 (Node2 (Node2 a b) (Node2 c d))

lemmaDigit : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (d : Digit A v n) (xs : List A) → reducerDigit _∷_ d xs ≡ reducerDigit _∷_ d [] ++ xs
lemmaDigit (One x) xs = lemmaNode x xs
lemmaDigit (Two a b) xs = lemmaNode (Node2 a b) xs
lemmaDigit (Three a b c) xs = lemmaNode (Node3 a b c) xs
lemmaDigit (Four a b c d) xs = lemmaNode (Node2 (Node2 a b) (Node2 c d)) xs

lemmaFingerTree : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) (xs : List A) → reducerFingerTree _∷_ ft xs ≡ reducerFingerTree _∷_ ft [] ++ xs
lemmaFingerTree Empty xs = refl
lemmaFingerTree (Single x) xs = lemmaNode x xs
lemmaFingerTree (Deep pr m sf) xs = begin
                                      reducerDigit _∷_ pr
                                      (reducerFingerTree _∷_ m (reducerDigit _∷_ sf xs))
                                      ≡⟨ lemmaDigit pr (reducerFingerTree _∷_ m (reducerDigit _∷_ sf xs))
                                      ⟩
                                      reducerDigit _∷_ pr [] ++
                                      reducerFingerTree _∷_ m (reducerDigit _∷_ sf xs)
                                      ≡⟨
                                      cong (_++_ (reducerDigit _∷_ pr []))
                                      (lemmaFingerTree m (reducerDigit _∷_ sf xs))
                                      ⟩
                                      reducerDigit _∷_ pr [] ++
                                      reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf xs
                                      ≡⟨
                                      cong
                                      (λ x → reducerDigit _∷_ pr [] ++ reducerFingerTree _∷_ m [] ++ x)
                                      (lemmaDigit sf xs)
                                      ⟩
                                      reducerDigit _∷_ pr [] ++
                                      reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf [] ++ xs
                                      ≡⟨
                                      cong (_++_ (reducerDigit _∷_ pr []))
                                      (sym
                                       (listAssoc (reducerFingerTree _∷_ m []) (reducerDigit _∷_ sf [])
                                        xs))
                                      ⟩
                                      reducerDigit _∷_ pr [] ++
                                      (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf []) ++ xs
                                      ≡⟨
                                      sym
                                      (listAssoc (reducerDigit _∷_ pr [])
                                       (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf []) xs)
                                      ⟩
                                      (reducerDigit _∷_ pr [] ++
                                       reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf [])
                                      ++ xs
                                      ≡⟨
                                      cong (flip _++_ xs)
                                      (sym
                                       (lemmaDigit pr
                                        (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf [])))
                                      ⟩
                                      reducerDigit _∷_ pr
                                      (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf [])
                                      ++ xs
                                      ≡⟨
                                      cong (λ x → reducerDigit _∷_ pr x ++ xs)
                                      (sym (lemmaFingerTree m (reducerDigit _∷_ sf [])))
                                      ⟩
                                      reducerDigit _∷_ pr
                                      (reducerFingerTree _∷_ m (reducerDigit _∷_ sf []))
                                      ++ xs
                                      ∎

lemmax7 : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 v3 : V} (pr : Digit A v1 n) (m : FingerTree A v2 (suc n)) (sf : Digit A v3 n) → toList {{reduceFingerTree}} (Deep pr m sf) ≡ toList {{reduceDigit}} pr ++ toList {{reduceFingerTree}} m ++ toList {{reduceDigit}} sf
lemmax7 pr m sf = begin
                    reducerDigit _∷_ pr
                    (reducerFingerTree _∷_ m (reducerDigit _∷_ sf []))
                    ≡⟨ lemmaDigit pr (reducerFingerTree _∷_ m (reducerDigit _∷_ sf []))
                    ⟩
                    reducerDigit _∷_ pr [] ++
                    reducerFingerTree _∷_ m (reducerDigit _∷_ sf [])
                    ≡⟨
                    cong (_++_ (reducerDigit _∷_ pr []))
                    (lemmaFingerTree m (reducerDigit _∷_ sf []))
                    ⟩
                    reducerDigit _∷_ pr [] ++
                    reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf []
                    ∎

lemmax8 : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} {A B : Set}
            (ft : FingerTree A v n) (op : A → B → B) (z : B) →
            reducer {{reduceFingerTree}} op ft z ≡
            reducer {{reduceList}} op (toList {{reduceFingerTree}} ft) z
lemmax8 Empty op z = refl
lemmax8 (Single x) op z = lemmax5 x op z
lemmax8 (Deep pr m sf) op z = begin
                                reducerDigit op pr (reducerFingerTree op m (reducerDigit op sf z))
                                ≡⟨ lemmax6 pr op (reducerFingerTree op m (reducerDigit op sf z)) ⟩
                                reducer {{reduceList}} op (reducerDigit _∷_ pr [])
                                (reducerFingerTree op m (reducerDigit op sf z))
                                ≡⟨
                                cong (reducer {{reduceList}} op (reducerDigit _∷_ pr []))
                                (lemmax8 m op (reducerDigit op sf z))
                                ⟩
                                reducer {{reduceList}} op (reducerDigit _∷_ pr [])
                                (reducer {{reduceList}} op (toList {{reduceFingerTree}} m)
                                 (reducerDigit op sf z))
                                ≡⟨
                                cong
                                (λ x →
                                   reducer {{reduceList}} op (reducerDigit _∷_ pr [])
                                   (reducer {{reduceList}} op (toList {{reduceFingerTree}} m) x))
                                (lemmax6 sf op z)
                                ⟩
                                reducer {{reduceList}} op (reducerDigit _∷_ pr [])
                                (reducer {{reduceList}} op (reducerFingerTree _∷_ m [])
                                 (reducer {{reduceList}} op (reducerDigit _∷_ sf []) z))
                                ≡⟨
                                cong (reducer {{reduceList}} op (reducerDigit _∷_ pr []))
                                (lemmaList (reducerFingerTree _∷_ m []) (reducerDigit _∷_ sf []) op
                                 z)
                                ⟩
                                reducer {{reduceList}} op (reducerDigit _∷_ pr [])
                                (reducer {{reduceList}} op
                                 (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf []) z)
                                ≡⟨
                                lemmaList (reducerDigit _∷_ pr [])
                                (reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf []) op z
                                ⟩
                                reducer {{reduceList}} op
                                (reducerDigit _∷_ pr [] ++
                                 reducerFingerTree _∷_ m [] ++ reducerDigit _∷_ sf [])
                                z
                                ≡⟨
                                cong (λ x → reducer {{reduceList}} op x z) (sym (lemmax7 pr m sf))
                                ⟩
                                reducer {{reduceList}} op
                                (toList {{reduceFingerTree}} (Deep pr m sf)) z
                                ∎

{- ∀ (xs : List A), toList (toTree xs) ≡ xs  -}

lemmax : {V : Set} {{m : Monoid V}} {A : Set} {{mea : Measured A V}}
           (xs : List A) →
           toList {{reduceFingerTree}} (listToTree xs) ≡ xs
lemmax xs = trans (lemmax4 xs _∷_ []) (lemma xs)
  where lemma : {A : Set} (xs : List A) → reducer {{reduceList}} _∷_ xs [] ≡ xs
        lemma [] = refl
        lemma (x ∷ xs) = cong (_∷_ x) (lemma xs)

{- Viewing from left and right -}

data ViewL (S : Set → Set) (A : Set) : Set where
  NilL : ViewL S A
  ConsL : A → S A → ViewL S A

data ViewR (S : Set → Set) (A : Set) : Set where
  NilR : ViewR S A
  ConsR : A → S A → ViewR S A

headDigitV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Digit A v n → V
headDigitV (One {v} a) = v
headDigitV (Two {v} a b) = v
headDigitV (Three {v} a b c) = v
headDigitV (Four {v} a b c d) = v

headDigit : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → Node A (headDigitV d) n
headDigit (One a) = a
headDigit (Two a b) = a
headDigit (Three a b c) = a
headDigit (Four a b c d) = a

headV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → FingerTree A v n → V
headV Empty = ∅
headV (Single {v} x) = v
headV (Deep pr m sf) = headDigitV pr

tailDigitV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Digit A v n → V
tailDigitV (One a) = ∅
tailDigitV (Two {_} {v} a b) = v
tailDigitV (Three {_} {v1} {v2} a b c) = _⊕_ v1 v2
tailDigitV (Four {_} {v1} {v2} {v3} a b c d) = _⊕_ (_⊕_ v1 v2) v3

tailDigit : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → Maybe (Digit A (tailDigitV d) n)
tailDigit (One a) = nothing
tailDigit (Two a b) = just (One b)
tailDigit (Three a b c) = just (Two b c)
tailDigit (Four a b c d) = just (Three b c d)

tailV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → FingerTree A v n → V
tailV Empty = ∅
tailV (Single x) = ∅
tailV (Deep {_} {v1} {v2} pr m sf) = _⊕_ (_⊕_ (tailDigitV pr) v1) v2

initDigitV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Digit A v n → V
initDigitV (One a) = ∅
initDigitV (Two {v} {_} a b) = v
initDigitV (Three {v1} {v2} {_} a b c) = _⊕_ v1 v2
initDigitV (Four {v1} {v2} {v3} {_} a b c d) = _⊕_ (_⊕_ v1 v2) v3

initDigit : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → Maybe (Digit A (initDigitV d) n)
initDigit (One a) = nothing
initDigit (Two a b) = just (One a)
initDigit (Three a b c) = just (Two a b)
initDigit (Four a b c d) = just (Three a b c)

initV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → FingerTree A v n → V
initV Empty = ∅
initV (Single x) = ∅
initV (Deep {v1} {v2} pr m sf) = _⊕_ (_⊕_ v1 v2) (initDigitV sf)

lastDigitV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Digit A v n → V
lastDigitV (One {v} a) = v
lastDigitV (Two {v2 = v} a b) = v
lastDigitV (Three {v3 = v} a b c) = v
lastDigitV (Four {v4 = v} a b c d) = v

lastDigit : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → Node A (lastDigitV d) n
lastDigit (One a) = a
lastDigit (Two a b) = b
lastDigit (Three a b c) = c
lastDigit (Four a b c d) = d

lastV : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → FingerTree A v n → V
lastV Empty = ∅
lastV (Single {v} x) = v
lastV (Deep pr m sf) = lastDigitV sf

nodeToDigit : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → Node A v (suc n) → Digit A v n
nodeToDigit (Node2 a b) = Two a b
nodeToDigit (Node3 a b c) = Three a b c

lemma6 : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → headDigitV d ⊕ tailDigitV d ≡ v
lemma6 (One _) = sym (id1 _)
lemma6 (Two _ _) = refl
lemma6 (Three _ _ _) = sym (assoc _ _ _)
lemma6 (Four _ _ _ _) = sym lemma1

lemma7 : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} (d : Digit A v n) → initDigitV d ⊕ lastDigitV d ≡ v
lemma7 (One _) = sym (id2 _)
lemma7 (Two _ _) = refl
lemma7 (Three _ _ _) = refl
lemma7 (Four _ _ _ _) = refl

headL : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → Maybe (Node A (headV ft) n)
headL Empty = nothing
headL (Single x) = just x
headL (Deep pr _ _) = just (headDigit pr)

tailL : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → FingerTree A (tailV ft) n
tailL Empty = Empty
tailL (Single x) = Empty
tailL (Deep (One a) Empty sf) = substFingerTree lemma (digitToTree sf)
      where lemma : {V : Set} {{m : Monoid V}} {v : V} → v ≡ _⊕_ (_⊕_ ∅ ∅) v
            lemma {_} {v} = begin
                      v ≡⟨ id2 v ⟩
                      _⊕_ ∅ v ≡⟨ cong (flip _⊕_ v) (id1 ∅) ⟩ _⊕_ (_⊕_ ∅ ∅) v ∎
tailL (Deep (One a) (Single x) sf) = substFingerTree lemma (Deep (nodeToDigit x) Empty sf)
      where lemma : {V : Set} {{m : Monoid V}} {v1 v2 : V} → _⊕_ (_⊕_ v1 ∅) v2 ≡ _⊕_ (_⊕_ ∅ v1) v2
            lemma {_} {v1} {v2} = begin
                                    _⊕_ (_⊕_ v1 ∅) v2 ≡⟨ cong (flip _⊕_ v2) (sym (id1 v1)) ⟩
                                    _⊕_ v1 v2 ≡⟨ cong (flip _⊕_ v2) (id2 v1) ⟩ _⊕_ (_⊕_ ∅ v1) v2 ∎
tailL (Deep (One a) (Deep pr m sf) sf2) with headL (Deep pr m sf) | inspect headL (Deep pr m sf)
... | nothing | [ () ]
... | just x  | _ = substFingerTree (lemma {pr = pr})
                     (Deep (nodeToDigit x) (tailL (Deep pr m sf)) sf2)
      where lemma : {A : Set} {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} {pr : Digit A v1 _} →
                    _⊕_ (_⊕_ (headDigitV pr) (_⊕_ (_⊕_ (tailDigitV pr) v2) v3)) v4 ≡ _⊕_ (_⊕_ ∅ (_⊕_ (_⊕_ v1 v2) v3)) v4
            lemma {v1 = v1} {v2} {v3} {v4} {pr} = begin
                      _⊕_ (_⊕_ (headDigitV pr) (_⊕_ (_⊕_ (tailDigitV pr) v2) v3)) v4 ≡⟨
                      cong (flip _⊕_ v4)
                      (sym (assoc (headDigitV pr) (_⊕_ (tailDigitV pr) v2) v3))
                      ⟩
                      _⊕_ (_⊕_ (_⊕_ (headDigitV pr) (_⊕_ (tailDigitV pr) v2)) v3) v4 ≡⟨
                      cong (λ v → _⊕_ (_⊕_ v v3) v4)
                      (sym (assoc (headDigitV pr) (tailDigitV pr) v2))
                      ⟩
                      _⊕_ (_⊕_ (_⊕_ (_⊕_ (headDigitV pr) (tailDigitV pr)) v2) v3) v4 ≡⟨
                      cong (λ v → _⊕_ (_⊕_ (_⊕_ v v2) v3) v4) (lemma6 pr) ⟩
                      _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡⟨
                      cong (flip _⊕_ v4) (id2 (_⊕_ (_⊕_ v1 v2) v3)) ⟩
                      _⊕_ (_⊕_ ∅ (_⊕_ (_⊕_ v1 v2) v3)) v4 ∎
tailL (Deep (Two a b) m sf) = Deep (One b) m sf
tailL (Deep (Three a b c) m sf) = Deep (Two b c) m sf
tailL (Deep (Four a b c d) m sf) = Deep (Three b c d) m sf

headR : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → Maybe (Node A (lastV ft) n)
headR Empty = nothing
headR (Single x) = just x
headR (Deep _ _ sf) = just (lastDigit sf)

tailR : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → FingerTree A (initV ft) n
tailR Empty = Empty
tailR (Single x) = Empty
tailR (Deep pr Empty (One a)) = substFingerTree lemma (digitToTree pr)
      where lemma : {V : Set} {{m : Monoid V}} {v : V} → v ≡ _⊕_ (_⊕_ v ∅) ∅
            lemma {_} {v} = begin
                      v ≡⟨ id1 v ⟩
                      _⊕_ v ∅ ≡⟨ id1 (_⊕_ v ∅) ⟩ _⊕_ (_⊕_ v ∅) ∅ ∎
tailR (Deep pr (Single x) (One a)) = substFingerTree lemma (Deep pr Empty (nodeToDigit x))
      where lemma : {V : Set} {{m : Monoid V}} {v1 v2 : V} → _⊕_ (_⊕_ v1 ∅) v2 ≡ _⊕_ (_⊕_ v1 v2) ∅
            lemma {_} {v1} {v2} = begin
                                    _⊕_ (_⊕_ v1 ∅) v2 ≡⟨ cong (flip _⊕_ v2) (sym (id1 v1)) ⟩
                                    _⊕_ v1 v2 ≡⟨ id1 (_⊕_ v1 v2) ⟩ _⊕_ (_⊕_ v1 v2) ∅ ∎
tailR (Deep pr2 (Deep pr m sf) (One a)) with headR (Deep pr m sf) | inspect headR (Deep pr m sf)
... | nothing | [ () ]
... | just x  | _ = substFingerTree (lemma {sf = sf}) (Deep pr2 (tailR (Deep pr m sf)) (nodeToDigit x))
      where lemma : {A : Set} {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} {sf : Digit A v4 _} →
                    _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf))) (lastDigitV sf) ≡ _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)) ∅
            lemma {v1 = v1} {v2} {v3} {v4} {sf} = begin _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf))) (lastDigitV sf) ≡⟨
                                                        assoc v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf)) (lastDigitV sf)
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) (initDigitV sf)) (lastDigitV sf)) ≡⟨
                                                        cong (_⊕_ v1) (assoc (_⊕_ v2 v3) (initDigitV sf) (lastDigitV sf))
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ v2 v3) (_⊕_ (initDigitV sf) (lastDigitV sf))) ≡⟨
                                                        cong (λ vx → _⊕_ v1 (_⊕_ (_⊕_ v2 v3) vx)) (lemma7 sf)
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4) ≡⟨ id1 (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4))
                                                        ⟩ _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)) ∅ ∎
tailR (Deep pr m (Two b a)) = Deep pr m (One b)
tailR (Deep pr m (Three c b a)) = Deep pr m (Two c b)
tailR (Deep pr m (Four d c b a)) = Deep pr m (Three d c b)

viewL : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → ViewL (λ _ → FingerTree A (tailV ft) n) (Node A (headV ft) n)
viewL t with headL t
... | nothing = NilL
... | just x  = ConsL x (tailL t)

viewLNilL : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → viewL ft ≡ NilL → v ≡ ∅
viewLNilL Empty _ = refl
viewLNilL (Single _) ()
viewLNilL (Deep _ _ _) ()

viewLConsL : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) {head : Node A (headV ft) n} {tail : FingerTree A (tailV ft) n} → .(viewL ft ≡ ConsL head tail) → v ≡ headV ft ⊕ tailV ft
viewLConsL Empty ()
viewLConsL (Single {v} x) lemma = id1 v
viewLConsL (Deep {v1} {v2} {v3} pr m sf) lemma = begin _⊕_ (_⊕_ v1 v2) v3 ≡⟨ cong (λ x → _⊕_ (_⊕_ x v2) v3) (sym (lemma6 pr)) ⟩
                                                       _⊕_ (_⊕_ (_⊕_ (headDigitV pr) (tailDigitV pr)) v2) v3 ≡⟨ cong (λ x → _⊕_ x v3) (assoc (headDigitV pr) (tailDigitV pr) v2) ⟩
                                                       _⊕_ (_⊕_ (headDigitV pr) (_⊕_ (tailDigitV pr) v2)) v3 ≡⟨ assoc (headDigitV pr) (_⊕_ (tailDigitV pr) v2) v3 ⟩
                                                       _⊕_ (headDigitV pr) (_⊕_ (_⊕_ (tailDigitV pr) v2) v3) ∎

viewR : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → ViewR (λ _ → FingerTree A (initV ft) n) (Node A (lastV ft) n)
viewR t with headR t
... | nothing = NilR
... | just x  = ConsR x (tailR t)

viewRNilR : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → viewR ft ≡ NilR → v ≡ ∅
viewRNilR Empty _ = refl
viewRNilR (Single _) ()
viewRNilR (Deep _ _ _) ()

isEmpty : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} → FingerTree A v n → Bool
isEmpty x with viewL x
... | NilL = true
... | ConsL _ _ = false

empty : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} → FingerTree A v n → Bool
empty Empty = true
empty _ = false

emptyLemma : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → isEmpty ft ≡ empty ft
emptyLemma Empty = refl
emptyLemma (Single x) = refl
emptyLemma (Deep x ft x₁) = refl

emptyLemma1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → isEmpty ft ≡ true → ft ≅ Empty {V} {m} {A} {n}
emptyLemma1 Empty lemma = H.refl
emptyLemma1 (Single x) ()
emptyLemma1 (Deep pr m sf) ()

emptyLemma2 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → isEmpty ft ≡ false → ft ≇ Empty {V} {m} {A} {n}
emptyLemma2 Empty ()
emptyLemma2 (Single x) _ ()
emptyLemma2 (Deep pr m sf) _ ()

{- Concatenation -}
infixr 5 _∷_ _⁺++_ _⁺++⁺_

data NodeList {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  [] : {n : ℕ} → NodeList A ∅ n
  _∷_ : {v1 v2 : V} {n : ℕ} (x : Node A v1 n) (xs : NodeList A v2 n) → NodeList A (v1 ⊕ v2) n

data NodeList⁺ {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  [_] : {v : V}{n : ℕ} (x : Node A v n)→ NodeList⁺ A v n
  _∷_ : {v1 v2 : V} {n : ℕ} (x : Node A v1 n) (xs : NodeList⁺ A v2 n) → NodeList⁺ A (v1 ⊕ v2) n

data NodeList⁺⁺ {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  [_,_] : {v1 v2 : V} {n : ℕ} (x : Node A v1 n) (y : Node A v2 n) → NodeList⁺⁺ A (v1 ⊕ v2) n
  _∷_   : {v1 v2 : V} {n : ℕ} (x : Node A v1 n) (xs : NodeList⁺⁺ A v2 n) → NodeList⁺⁺ A (v1 ⊕ v2) n

digitToNodeList⁺ : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} → Digit A v n → NodeList⁺ A v n
digitToNodeList⁺ (One a) = [ a ]
digitToNodeList⁺ (Two a b) = a ∷ [ b ]
digitToNodeList⁺ (Three a b c) = subst (λ Vx → NodeList⁺ _ Vx _) (sym (assoc _ _ _)) (a ∷ b ∷ [ c ])
digitToNodeList⁺ (Four a b c d) = subst (λ Vx → NodeList⁺ _ Vx _) (trans (sym (assoc _ _ _)) (sym (assoc _ _ _))) (a ∷ b ∷ c ∷ [ d ])

_⁺++_ : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → NodeList⁺ A v1 n → NodeList A v2 n → NodeList⁺ A (v1 ⊕ v2) n
[ x ] ⁺++ [] = subst (λ Vx → NodeList⁺ _ Vx _) (id1 _) [ x ]
[ x ] ⁺++ (y ∷ ys) = x ∷ [ y ] ⁺++ ys
(x ∷ xs) ⁺++ ys = subst (λ Vx → NodeList⁺ _ Vx _) (sym (assoc _ _ _)) (x ∷ xs ⁺++ ys)

_⁺++⁺_ : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → NodeList⁺ A v1 n → NodeList⁺ A v2 n → NodeList⁺⁺ A (v1 ⊕ v2) n
[ x ] ⁺++⁺ [ y ] = [ x , y ]
[ x ] ⁺++⁺ (y ∷ ys) = x ∷ [ y ] ⁺++⁺ ys
(x ∷ xs) ⁺++⁺ ys = subst (λ Vx → NodeList⁺⁺ _ Vx _) (sym (assoc _ _ _)) (x ∷ xs ⁺++⁺ ys)

substNodeList : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 : V} → v1 ≡ v2 → NodeList A v1 n → NodeList A v2 n
substNodeList {A} {n} = subst (λ Vx → NodeList A Vx n)

nodes : {V : Set} {{m : Monoid V}} {A : Set} {v : V} {n : ℕ} (xs : NodeList⁺⁺ A v n) → NodeList A v (suc n)
nodes [ a , b ] = substNodeList (sym (id1 _)) (Node2 a b ∷ [])
nodes (a ∷ [ b , c ]) = substNodeList lemma (Node3 a b c ∷ [])
  where
        lemma : {V : Set} {{m : Monoid V}} {v1 v2 v3 : V} →
                    _⊕_ (_⊕_ (_⊕_ v1 v2) v3) ∅ ≡ _⊕_ v1 (_⊕_ v2 v3)
        lemma {_} {v1} {v2} {v3}  = begin
                                        _⊕_ (_⊕_ (_⊕_ v1 v2) v3) ∅ ≡⟨ sym (id1 (_⊕_ (_⊕_ v1 v2) v3)) ⟩
                                        _⊕_ (_⊕_ v1 v2) v3 ≡⟨ assoc v1 v2 v3 ⟩ _⊕_ v1 (_⊕_ v2 v3) ∎
nodes (a ∷ b ∷ [ c , d ]) = substNodeList lemma (Node2 a b ∷ Node2 c d ∷ [])
  where
        lemma : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} →
                    _⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ v3 v4) ∅) ≡ _⊕_ v1 (_⊕_ v2 (_⊕_ v3 v4))
        lemma {_} {v1} {v2} {v3} {v4}  = begin
                                             _⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ v3 v4) ∅) ≡⟨
                                             cong (_⊕_ (_⊕_ v1 v2)) (sym (id1 (_⊕_ v3 v4))) ⟩
                                             _⊕_ (_⊕_ v1 v2) (_⊕_ v3 v4) ≡⟨ assoc v1 v2 (_⊕_ v3 v4) ⟩
                                             _⊕_ v1 (_⊕_ v2 (_⊕_ v3 v4)) ∎
nodes (a ∷ b ∷ c ∷ xs) = substNodeList lemma (Node3 a b c ∷ nodes xs)
  where
        lemma : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} →
                    _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡ _⊕_ v1 (_⊕_ v2 (_⊕_ v3 v4))
        lemma {_} {v1} {v2} {v3} {v4}  = begin
                                             _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡⟨ assoc (_⊕_ v1 v2) v3 v4 ⟩
                                             _⊕_ (_⊕_ v1 v2) (_⊕_ v3 v4) ≡⟨ assoc v1 v2 (_⊕_ v3 v4) ⟩
                                             _⊕_ v1 (_⊕_ v2 (_⊕_ v3 v4)) ∎

_◁′_ : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → NodeList A v1 n → FingerTree A v2 n → FingerTree A (v1 ⊕ v2) n
[] ◁′ t = substFingerTree (id2 _) t
(x ∷ xs) ◁′ t = substFingerTree (sym (assoc _ _ _)) (x ◁ xs ◁′ t)

_▷′_ : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → FingerTree A v1 n → NodeList A v2 n → FingerTree A (v1 ⊕ v2) n
t ▷′ [] = substFingerTree (id1 _) t
t ▷′ (x ∷ xs) = substFingerTree (assoc _ _ _) ((t ▷ x) ▷′ xs)


lemma8 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 v5 v6 v7 : V} → _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 (_⊕_ (_⊕_ v3 v4) v5)) v6)) v7 ≡ _⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) (_⊕_ (_⊕_ v5 v6) v7)
lemma8 {_} {v1} {v2} {v3} {v4} {v5} {v6} {v7} = begin
                                                  _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 (_⊕_ (_⊕_ v3 v4) v5)) v6)) v7 ≡⟨
                                                  cong (λ v → _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v) v6)) v7)
                                                  (assoc v3 v4 v5) ⟩
                                                  _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 v5))) v6)) v7 ≡⟨
                                                  cong (flip _⊕_ v7)
                                                  (sym (assoc v1 (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 v5))) v6))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ v1 (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 v5)))) v6) v7 ≡⟨
                                                  cong (λ v → _⊕_ (_⊕_ v v6) v7)
                                                  (sym (assoc v1 v2 (_⊕_ v3 (_⊕_ v4 v5))))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ v3 (_⊕_ v4 v5))) v6) v7 ≡⟨
                                                  cong (λ v → _⊕_ (_⊕_ v v6) v7)
                                                  (sym (assoc (_⊕_ v1 v2) v3 (_⊕_ v4 v5)))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) (_⊕_ v4 v5)) v6) v7 ≡⟨
                                                  cong (λ v → _⊕_ (_⊕_ v v6) v7)
                                                  (sym (assoc (_⊕_ (_⊕_ v1 v2) v3) v4 v5))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5) v6) v7 ≡⟨
                                                  cong (flip _⊕_ v7) (assoc (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5 v6) ⟩
                                                  _⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) (_⊕_ v5 v6)) v7 ≡⟨
                                                  assoc (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) (_⊕_ v5 v6) v7 ⟩
                                                  _⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) (_⊕_ (_⊕_ v5 v6) v7) ∎

app3 : {V : Set} {v1 v2 v3 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → FingerTree A v1 n → NodeList A v2 n → FingerTree A v3 n → FingerTree A ((v1 ⊕ v2) ⊕ v3) n
app3 Empty ts xs = substFingerTree (cong (flip _⊕_ _) (id2 _)) (ts ◁′ xs)
app3 xs ts Empty = substFingerTree (id1 _) (xs ▷′ ts)
app3 (Single x) ts xs = substFingerTree (sym (assoc _ _ _)) (x ◁ ts ◁′ xs)
app3 xs ts (Single x) = xs ▷′ ts ▷ x
app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) = substFingerTree lemma8 (Deep pr1 (app3 m1 (nodes ((digitToNodeList⁺ sf1 ⁺++ ts) ⁺++⁺ digitToNodeList⁺ pr2)) m2) sf2)

_⋈_ : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} → FingerTree A v1 n → FingerTree A v2 n → FingerTree A (v1 ⊕ v2) n
xs ⋈ ys = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (app3 xs [] ys)

{- Splitting -}

data Split (F1 : Set → Set) (A : Set) (F2 : Set → Set) : Set where
  split : F1 A → A → F2 A → Split F1 A F2

splitV1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → V
splitV1 p i (One a) = ∅
splitV1 p i (Two {v1} a b) with p (i ⊕ v1)
... | true = ∅
... | false = v1
splitV1 p i (Three {v1} {v2} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = ∅
... | false | true = v1
... | false | false = v1 ⊕ v2
splitV1 p i (Four {v1} {v2} {v3} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = ∅
... | false | true | _ = v1
... | false | false | true = v1 ⊕ v2
... | false | false | false = (v1 ⊕ v2) ⊕ v3

splitV2 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → V
splitV2 p i (One {v} a) = v
splitV2 p i (Two {v1} {v2} a b) with p (i ⊕ v1)
... | true = v1
... | false = v2
splitV2 p i (Three {v1} {v2} {v3} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = v1
... | false | true = v2
... | false | false = v3
splitV2 p i (Four {v1} {v2} {v3} {v4} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = v1
... | false | true | _ = v2
... | false | false | true = v3
... | false | false | false = v4

splitV3 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → V
splitV3 p i (One a) = ∅
splitV3 p i (Two {v1} {v2} a b) with p (i ⊕ v1)
... | true = v2
... | false = ∅
splitV3 p i (Three {v1} {v2} {v3} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = v2 ⊕ v3
... | _ | true = v3
... | _ | _ = ∅
splitV3 p i (Four {v1} {v2} {v3} {v4} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = (v2 ⊕ v3) ⊕ v4
... | _ | true | _ = v3 ⊕ v4
... | _ | _ | true = v4
... | _ | _ | _ = ∅

data NDigit {V : Set} {{m : Monoid V}} (A : Set) : V → ℕ → Set where
  Zero : {n : ℕ} → NDigit A ∅ n
  One : {v : V} {n : ℕ} → Node A v n → NDigit A v n
  Two : {v1 v2 : V} {n : ℕ} → Node A v1 n → Node A v2 n → NDigit A (v1 ⊕ v2) n
  Three : {v1 v2 v3 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → NDigit A ((v1 ⊕ v2) ⊕ v3) n
  Four : {v1 v2 v3 v4 : V} {n : ℕ} → Node A v1 n → Node A v2 n → Node A v3 n → Node A v4 n → NDigit A (((v1 ⊕ v2) ⊕ v3) ⊕ v4) n

deepL : {V : Set} {{m : Monoid V}} {A : Set} {v1 v2 v3 : V} {n : ℕ} → NDigit A v1 n → FingerTree A v2 (suc n) → Digit A v3 n → FingerTree A ((v1 ⊕ v2) ⊕ v3) n
deepL Zero Empty sf = substFingerTree lemma (digitToTree sf)
      where lemma : {V : Set} {{m : Monoid V}} {v : V} → v ≡ _⊕_ (_⊕_ ∅ ∅) v
            lemma {_} {v} = begin
                      v ≡⟨ id2 v ⟩
                      _⊕_ ∅ v ≡⟨ cong (flip _⊕_ v) (id1 ∅) ⟩ _⊕_ (_⊕_ ∅ ∅) v ∎
deepL Zero (Single x) sf = substFingerTree lemma (Deep (nodeToDigit x) Empty sf)
      where lemma : {V : Set} {{m : Monoid V}} {v1 v2 : V} → _⊕_ (_⊕_ v1 ∅) v2 ≡ _⊕_ (_⊕_ ∅ v1) v2
            lemma {_} {v1} {v2} = begin
                                    _⊕_ (_⊕_ v1 ∅) v2 ≡⟨ cong (flip _⊕_ v2) (sym (id1 v1)) ⟩
                                    _⊕_ v1 v2 ≡⟨ cong (flip _⊕_ v2) (id2 v1) ⟩ _⊕_ (_⊕_ ∅ v1) v2 ∎
deepL Zero (Deep pr m sf) sf2 with headL (Deep pr m sf) | inspect headL (Deep pr m sf)
... | nothing | [ () ]
... | just x  | _ = substFingerTree (lemma {pr = pr})
                     (Deep (nodeToDigit x) (tailL (Deep pr m sf)) sf2)
      where lemma : {A : Set} {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} {pr : Digit A v1 _} →
                    _⊕_ (_⊕_ (headDigitV pr) (_⊕_ (_⊕_ (tailDigitV pr) v2) v3)) v4 ≡ _⊕_ (_⊕_ ∅ (_⊕_ (_⊕_ v1 v2) v3)) v4
            lemma {v1 = v1} {v2} {v3} {v4} {pr} = begin
                      _⊕_ (_⊕_ (headDigitV pr) (_⊕_ (_⊕_ (tailDigitV pr) v2) v3)) v4 ≡⟨
                      cong (flip _⊕_ v4)
                      (sym (assoc (headDigitV pr) (_⊕_ (tailDigitV pr) v2) v3))
                      ⟩
                      _⊕_ (_⊕_ (_⊕_ (headDigitV pr) (_⊕_ (tailDigitV pr) v2)) v3) v4 ≡⟨
                      cong (λ v → _⊕_ (_⊕_ v v3) v4)
                      (sym (assoc (headDigitV pr) (tailDigitV pr) v2))
                      ⟩
                      _⊕_ (_⊕_ (_⊕_ (_⊕_ (headDigitV pr) (tailDigitV pr)) v2) v3) v4 ≡⟨
                      cong (λ v → _⊕_ (_⊕_ (_⊕_ v v2) v3) v4) (lemma6 pr) ⟩
                      _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡⟨
                      cong (flip _⊕_ v4) (id2 (_⊕_ (_⊕_ v1 v2) v3)) ⟩
                      _⊕_ (_⊕_ ∅ (_⊕_ (_⊕_ v1 v2) v3)) v4 ∎
deepL (One a) m sf = Deep (One a) m sf
deepL (Two a b) m sf = Deep (Two a b) m sf
deepL (Three a b c) m sf = Deep (Three a b c) m sf
deepL (Four a b c d) m sf = Deep (Four a b c d) m sf
  

deepR : {V : Set} {{m : Monoid V}} {A : Set} {v1 v2 v3 : V} {n : ℕ} → Digit A v1 n → FingerTree A v2 (suc n) → NDigit A v3 n → FingerTree A ((v1 ⊕ v2) ⊕ v3) n
deepR pr Empty Zero = substFingerTree lemma (digitToTree pr)
      where lemma : {V : Set} {{m : Monoid V}} {v : V} → v ≡ _⊕_ (_⊕_ v ∅) ∅
            lemma {_} {v} = begin
                      v ≡⟨ id1 v ⟩
                      _⊕_ v ∅ ≡⟨ id1 (_⊕_ v ∅) ⟩ _⊕_ (_⊕_ v ∅) ∅ ∎
deepR pr (Single x) Zero = substFingerTree lemma (Deep pr Empty (nodeToDigit x))
      where lemma : {V : Set} {{m : Monoid V}} {v1 v2 : V} → _⊕_ (_⊕_ v1 ∅) v2 ≡ _⊕_ (_⊕_ v1 v2) ∅
            lemma {_} {v1} {v2} = begin
                                    _⊕_ (_⊕_ v1 ∅) v2 ≡⟨ cong (flip _⊕_ v2) (sym (id1 v1)) ⟩
                                    _⊕_ v1 v2 ≡⟨ id1 (_⊕_ v1 v2) ⟩ _⊕_ (_⊕_ v1 v2) ∅ ∎
deepR pr2 (Deep pr m sf) Zero with headR (Deep pr m sf) | inspect headR (Deep pr m sf)
... | nothing | [ () ]
... | just x  | _ = substFingerTree (lemma {sf = sf}) (Deep pr2 (tailR (Deep pr m sf)) (nodeToDigit x))
      where lemma : {A : Set} {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} {sf : Digit A v4 _} →
                    _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf))) (lastDigitV sf) ≡ _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)) ∅
            lemma {v1 = v1} {v2} {v3} {v4} {sf} = begin _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf))) (lastDigitV sf) ≡⟨
                                                        assoc v1 (_⊕_ (_⊕_ v2 v3) (initDigitV sf)) (lastDigitV sf)
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) (initDigitV sf)) (lastDigitV sf)) ≡⟨
                                                        cong (_⊕_ v1) (assoc (_⊕_ v2 v3) (initDigitV sf) (lastDigitV sf))
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ v2 v3) (_⊕_ (initDigitV sf) (lastDigitV sf))) ≡⟨
                                                        cong (λ vx → _⊕_ v1 (_⊕_ (_⊕_ v2 v3) vx)) (lemma7 sf)
                                                        ⟩ _⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4) ≡⟨ id1 (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4))
                                                        ⟩ _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)) ∅ ∎
deepR pr m (One a) = Deep pr m (One a)
deepR pr m (Two a b) = Deep pr m (Two a b)
deepR pr m (Three a b c) = Deep pr m (Three a b c)
deepR pr m (Four a b c d) = Deep pr m (Four a b c d)

nDigitToTree : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v : V} → NDigit A v n → FingerTree A v n
nDigitToTree Zero = Empty
nDigitToTree (One x) = Single x
nDigitToTree (Two a b) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One a) Empty (One b))
nDigitToTree (Three a b c) = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (Two a b) Empty (One c))
nDigitToTree (Four a b c d) = substFingerTree lemma (Deep (Two a b) Empty (Two c d))
            where lemma : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} → _⊕_ (_⊕_ (_⊕_ v1 v2) ∅) (_⊕_ v3 v4) ≡ _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4
                  lemma {_} {v1} {v2} {v3} {v4} = begin
                                                    _⊕_ (_⊕_ (_⊕_ v1 v2) ∅) (_⊕_ v3 v4) ≡⟨
                                                    cong (flip _⊕_ (_⊕_ v3 v4)) (sym (id1 (_⊕_ v1 v2))) ⟩
                                                    _⊕_ (_⊕_ v1 v2) (_⊕_ v3 v4) ≡⟨ sym (assoc (_⊕_ v1 v2) v3 v4) ⟩
                                                    _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ∎

splitDigit : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → Split (λ _ → NDigit A (splitV1 p i as) n) (Node A (splitV2 p i as) n) (λ _ → NDigit A (splitV3 p i as) n)
splitDigit p i (One a) = split Zero a Zero
splitDigit p i (Two {v1} a b) with p (i ⊕ v1)
... | true = split Zero a (One b)
... | false = split (One a) b Zero
splitDigit p i (Three {v1} {v2} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = split Zero a (Two b c)
... | false | true = split (One a) b (One c)
... | false | false = split (Two a b) c Zero
splitDigit p i (Four {v1} {v2} {v3} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = split Zero a (Three b c d)
... | false | true | _ = split (One a) b (Two c d)
... | false | false | true = split (Two a b) c (One d)
... | false | false | false = split (Three a b c) d Zero

splitDigitLemma1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → (splitV1 p i as ⊕ splitV2 p i as) ⊕ (splitV3 p i as) ≡ v
splitDigitLemma1 p i (One {v} _) = trans (sym (id1 (_⊕_ ∅ v))) (sym (id2 v))
splitDigitLemma1 p i (Two {v1} {v2} _ _) with p (i ⊕ v1)
... | true = cong (λ x → _⊕_ x v2) (sym (id2 v1))
... | false = sym (id1 (_⊕_ v1 v2))
splitDigitLemma1 p i (Three {v1} {v2} {v3} _ _ _) with p (i ⊕ v1)
... | true = trans (cong (λ x → _⊕_ x (_⊕_ v2 v3)) (sym (id2 v1))) (sym (assoc v1 v2 v3))
... | false with p ((i ⊕ v1) ⊕ v2)
...  | true = refl
...  | false = sym (id1 (_⊕_ (_⊕_ v1 v2) v3))
splitDigitLemma1 p i (Four {v1} {v2} {v3} {v4} _ _ _ _) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = begin _⊕_ (_⊕_ ∅ v1)
                             (_⊕_ (_⊕_ v2 v3) v4)
                             ≡⟨ cong (λ x → _⊕_ x (_⊕_ (_⊕_ v2 v3) v4)) (sym (id2 v1)) ⟩
                           _⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4) ≡⟨ sym (assoc v1 (_⊕_ v2 v3) v4) ⟩
                           _⊕_ (_⊕_ v1 (_⊕_ v2 v3)) v4 ≡⟨ cong (λ x → _⊕_ x v4) (sym (assoc v1 v2 v3)) ⟩
                           _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ∎
... | false | true | _ = sym (assoc (_⊕_ v1 v2) v3 v4)
... | false | false | true = refl
... | false | false | false = sym (id1 (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4))




mutual
  splitTreeV1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) → V
  splitTreeV1 p i Empty = ∅
  splitTreeV1 p i (Single x) = ∅
  splitTreeV1 p i (Deep {v1} pr Empty sf) with p (i ⊕ v1)
  ... | true = splitV1 p i pr
  ... | false = _⊕_ v1 (splitV1 p (_⊕_ i v1) sf)
  splitTreeV1 p i (Deep {v1} {v2} {v3} pr (Single x) sf) with p (i ⊕ v1)
  ... | true = splitV1 p i pr
  ... | false with p ((i ⊕ v1) ⊕ v2)
  ...  | true = _⊕_ v1 (splitV1 p (_⊕_ i v1) (nodeToDigit x))
  ...  | false = _⊕_ (_⊕_ v1 v2) (splitV1 p (_⊕_ (_⊕_ i v1) v2) sf) 
  splitTreeV1 p i (Deep {v1} pr (Deep pr2 m sf2) sf) with p (i ⊕ v1)
  ... | true = splitV1 p i pr
  ... | false with p ((i ⊕ v1) ⊕ getV (Deep pr2 m sf2))
  ...  | true with splitTree p (i ⊕ v1) (Deep pr2 m sf2) {refl}
  ...   | split l xs r = _⊕_ (_⊕_ v1 (getV l)) (splitV1 p (_⊕_ (_⊕_ i v1) (getV l)) (nodeToDigit xs))
  splitTreeV1 p i (Deep {v1} pr (Deep pr2 m sf2) sf) | false | false = _⊕_ (_⊕_ v1 (getV (Deep pr2 m sf2))) (splitV1 p (_⊕_ (_⊕_ i v1) (getV (Deep pr2 m sf2))) sf)

  splitTreeV2 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) → V
  splitTreeV2 p i Empty = ∅
  splitTreeV2 p i (Single {v} x) = v
  splitTreeV2 p i (Deep {v1} pr Empty sf) with p (i ⊕ v1)
  ... | true = splitV2 p i pr
  ... | false = splitV2 p (_⊕_ i v1) sf
  splitTreeV2 p i (Deep {v1} {v2} pr (Single x) sf) with p (i ⊕ v1)
  ... | true = splitV2 p i pr
  ... | false with p ((i ⊕ v1) ⊕ v2)
  ...  | true = splitV2 p (_⊕_ i v1) (nodeToDigit x)
  ...  | false = splitV2 p (_⊕_ (_⊕_ i v1) v2) sf 
  splitTreeV2 p i (Deep {v1} pr (Deep pr2 m sf2) sf) with p (i ⊕ v1)
  ... | true = splitV2 p i pr
  ... | false with p ((i ⊕ v1) ⊕ getV (Deep pr2 m sf2))
  ...  | true with splitTree p (i ⊕ v1) (Deep pr2 m sf2) {refl}
  ...   | split l xs r = splitV2 p (_⊕_ (_⊕_ i v1) (getV l)) (nodeToDigit xs)
  splitTreeV2 p i (Deep {v1} pr (Deep pr2 m sf2) sf) | false | false = splitV2 p (_⊕_ (_⊕_ i v1) (getV (Deep pr2 m sf2))) sf

  splitTreeV3 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) → V
  splitTreeV3 p i Empty = ∅
  splitTreeV3 p i (Single x) = ∅
  splitTreeV3 p i (Deep {v1} {_} {v3} pr Empty sf) with p (i ⊕ v1)
  ... | true = _⊕_ (splitV3 p i pr) v3
  ... | false = splitV3 p (_⊕_ i v1) sf
  splitTreeV3 p i (Deep {v1} {v2} {v3} pr (Single x) sf) with p (i ⊕ v1)
  ... | true = _⊕_ (_⊕_ (splitV3 p i pr) v2) v3
  ... | false with p ((i ⊕ v1) ⊕ v2)
  ...  | true = _⊕_ (splitV3 p (_⊕_ i v1) (nodeToDigit x)) v3
  ...  | false = splitV3 p (_⊕_ (_⊕_ i v1) v2) sf 
  splitTreeV3 p i (Deep {v1} {_} {v3} pr (Deep pr2 m sf2) sf) with p (i ⊕ v1)
  ... | true = _⊕_ (_⊕_ (splitV3 p i pr) (getV (Deep pr2 m sf2))) v3
  ... | false with p ((i ⊕ v1) ⊕ (getV (Deep pr2 m sf2)))
  ...  | true with splitTree p (i ⊕ v1) (Deep pr2 m sf2) {refl}
  ...   | split l xs r = _⊕_
                         (_⊕_ (splitV3 p (_⊕_ (_⊕_ i v1) (getV l)) (nodeToDigit xs))
                          (getV r))
                         v3
  splitTreeV3 p i (Deep {v1} pr (Deep pr2 m sf2) sf) | false | false = splitV3 p (_⊕_ (_⊕_ i v1) (getV (Deep pr2 m sf2))) sf

  splitTree : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) {le : isEmpty ft ≡ false} → Split (λ _ → FingerTree A (splitTreeV1 p i ft) n) (Node A (splitTreeV2 p i ft) n) (λ _ → FingerTree A (splitTreeV3 p i ft) n)
  splitTree p i Empty {}
  splitTree p i (Single x) = split Empty x Empty
  splitTree p i (Deep {v1} pr Empty sf) with p (i ⊕ v1)
  ... | true with splitDigit p i pr
  ...  | split l x r = split (nDigitToTree l) x (substFingerTree (cong (λ x₁ → _⊕_ x₁ _) (sym (id1 _))) (deepL r Empty sf))
  splitTree p i (Deep {v1} pr Empty sf) | false with splitDigit p (_⊕_ i v1) sf
  ...  | split l x r = split (substFingerTree (cong (λ x₁ → _⊕_ x₁ (splitV1 p (_⊕_ i v1) sf)) (sym (id1 v1))) (deepR pr Empty l)) x (nDigitToTree r)
  splitTree p i (Deep {v1} {v2} pr (Single a) sf) with p (i ⊕ v1)
  ... | true with splitDigit p i pr
  ...  | split l x r = split (nDigitToTree l) x (deepL r (Single a) sf)
  splitTree p i (Deep {v1} {v2} pr (Single a) sf) | false with p ((i ⊕ v1) ⊕ v2)
  ... | true with splitDigit p (_⊕_ i v1) (nodeToDigit a)
  ...  | split l x r = split (substFingerTree (cong (λ x₁ → _⊕_ x₁ (splitV1 p (_⊕_ i v1) (nodeToDigit a)))
                                               (sym (id1 v1))) (deepR pr Empty l)) x (substFingerTree (cong (λ x₁ → _⊕_ x₁ _) (sym (id1 _))) (deepL r Empty sf))
  splitTree p i (Deep {v1} {v2} pr (Single a) sf) | false | false with splitDigit p ((i ⊕ v1) ⊕ v2) sf
  ...  | split l x r = split (deepR pr (Single a) l) x (nDigitToTree r)
  splitTree p i (Deep {v1} pr (Deep pr2 m sf2) sf) with p (i ⊕ v1)
  ... | true with splitDigit p i pr
  ...  | split l x r = split (nDigitToTree l) x (deepL r (Deep pr2 m sf2) sf)
  splitTree p i (Deep {v1} pr (Deep pr2 m sf2) sf) | false with p ((i ⊕ v1) ⊕ (getV (Deep pr2 m sf2)))
  ...  | true with splitTree p (i ⊕ v1) (Deep pr2 m sf2) {refl}
  ...   | split ml xs mr with splitDigit p (_⊕_ (_⊕_ i v1) (getV ml)) (nodeToDigit xs)
  ...     | split l x r = split (deepR pr ml l) x (deepL r mr sf)
  splitTree p i (Deep {v1} pr (Deep pr2 m sf2) sf) | false | false with splitDigit p (_⊕_ (_⊕_ i v1) (getV (Deep pr2 m sf2))) sf
  ... | split l x r = split (deepR pr (Deep pr2 m sf2) l) x (nDigitToTree r)


open import Data.Product

split′V1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (ft : FingerTree A v n) → V
split′V1 p Empty = ∅
split′V1 {_} {v} p t with p v
... | true = splitTreeV1 p ∅ t
... | false = v

split′V2 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (ft : FingerTree A v n) → V
split′V2 p Empty = ∅
split′V2 {_} {v} p t with p v
... | true = splitTreeV2 p ∅ t ⊕ splitTreeV3 p ∅ t
... | false = ∅

split′ : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (ft : FingerTree A v n) → FingerTree A (split′V1 p ft) n × FingerTree A (split′V2 p ft) n
split′ p Empty = Empty , Empty
split′ p (Single {v} x) with p v
... | true = Empty , substFingerTree (id1 v) (Single x)
... | false = Single x , Empty
split′ p (Deep pr m sf) with splitTree p ∅ (Deep pr m sf) {refl}
... | split l x r with p (getV (Deep pr m sf))
...  | true = l , x ◁ r
...  | false = Deep pr m sf , Empty

takeUntil : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (ft : FingerTree A v n) → FingerTree A (split′V1 p ft) n
takeUntil p t = proj₁ (split′ p t)

dropUntil : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (ft : FingerTree A v n) → FingerTree A (split′V2 p ft) n
dropUntil p t = proj₂ (split′ p t)

{-
-- An unfinished implementation of ordered sequences
data Key (A : Set) : Set where
  noKey : Key A
  key : (a : A) → Key A

monoidKey : {A : Set} → Monoid (Key A)
monoidKey {A} = record { ∅ = noKey ; _⊕_ = _⊕′_ ;
                          isMonoid = record { id1 = λ _ → refl ; id2 = id2′ ; assoc = assoc′ }}
                                      where
                                        _⊕′_ : Key A → Key A → Key A
                                        k ⊕′ noKey = k
                                        _ ⊕′ k = k
                                        id2′ : (x : Key A) → x ≡ noKey ⊕′ x
                                        id2′ noKey = refl
                                        id2′ (key _) = refl
                                        assoc′ : (x y z : Key A) → (x ⊕′ y) ⊕′ z ≡ x ⊕′ (y ⊕′ z)
                                        assoc′ x y noKey = refl
                                        assoc′ x y (key z) = refl

measuredKey : Measured ℕ (Key ℕ)
measuredKey = record { measure = λ x → key x }

_<==′_ : Key ℕ → Key ℕ → Bool
noKey <==′ _ = true
key _ <==′ noKey = false
key a <==′ key b = a <= b

_<<′_ : Key ℕ → Key ℕ → Bool
_ <<′ noKey = false
noKey <<′ key a = true
key a <<′ key b = a << b


partition : {v : Key ℕ} (k : ℕ) (ft : FingerTree {{monoidKey}} ℕ v zero) → FingerTree {{monoidKey}} ℕ (split′V1 {{monoidKey}} (_<==′_ (key k)) ft) zero × FingerTree {{monoidKey}} ℕ (split′V2 {{monoidKey}} (_<==′_ (key k)) ft) zero
partition k t = split′ {{monoidKey}} (_<==′_ (key k)) t

insert :  {v : Key ℕ} (x : ℕ) (ft : FingerTree {{monoidKey}} ℕ v zero) → FingerTree {{monoidKey}} ℕ (_⊕_ {{monoidKey}} (split′V1 {{monoidKey}} (_<==′_ (key x)) ft)
                                                                                                       (_⊕_ {{monoidKey}} (measure {{measuredKey}} x)
                                                                                                        (split′V2 {{monoidKey}} (_<==′_ (key x)) ft))) zero
insert x t with split′ {{monoidKey}} (_<==′_ (key x)) t
... | l , r = l ⋈ _◁_ {{monoidKey}} {v1 = measure {{measuredKey}} x} (Leaf x) r

deleteAll : {v : Key ℕ} (x : ℕ) (ft : FingerTree {{monoidKey}} ℕ v zero) → FingerTree {{monoidKey}} ℕ
                                                                           (_⊕_ {{monoidKey}} (split′V1 {{monoidKey}} (_<==′_ (key x)) ft)
                                                                             (split′V2 {{monoidKey}} (_<<′_ (key x)) (dropUntil {{monoidKey}} (_<==′_ (key x)) ft))) zero
deleteAll x t with split′ {{monoidKey}} (_<==′_ (key x)) t
... | l , r with split′ {{monoidKey}} (_<<′_ (key x)) r
... | _ , r′ = l ⋈ r′

{-# NO_TERMINATION_CHECK #-}
merge : {v1 v2 : Key ℕ} (ft : FingerTree {{monoidKey}} ℕ v1 zero) (ft2 : FingerTree {{monoidKey}} ℕ v2 zero) → FingerTree {{monoidKey}} ℕ (_⊕_ {{monoidKey}} v1 v2) zero
merge {v1} {v2} as bs with viewL bs | inspect (viewL {{monoidKey}}) bs
... | NilL | [ eq ] = substFingerTree {!trans (id1 {{monoidKey}} v2) (viewLNilL bs eq)!} as
... | ConsL a bs′ | _ with split′ {{monoidKey}} (_<<′_ (getNodeV a)) as
...  | l , r = substFingerTree {{monoidKey}} {!!} (l ⋈ (a ◁ merge bs′ r))
-}
