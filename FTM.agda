

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List using (List; []; _∷_; foldr; foldl; length; _++_)
open import Function using (_∘_; flip)
open import Data.Bool
open import Data.Maybe


open import Relation.Binary.HeterogeneousEquality as H using (_≅_; ≡-to-≅)

open import Monoid
open import Measured

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

substFingerTree : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 : V} → v1 ≡ v2 → FingerTree A v1 n → FingerTree A v2 n
substFingerTree {A} {n} = subst (λ Vx → FingerTree A Vx n)

infixr 5 _◁_
_◁_ : {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v1 v2 : V} → Node A v1 n → FingerTree A v2 n → FingerTree A (v1 ⊕ v2) n
a ◁ Empty = substFingerTree (id1 _) (Single a)
a ◁ Single b = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One a) Empty (One b))
a ◁ Deep (One b) m sf = substFingerTree Monoid.lemma1 (Deep (Two a b) m sf)
a ◁ Deep (Two b c) m sf  = substFingerTree Monoid.lemma2 (Deep (Three a b c) m sf)
a ◁ Deep (Three b c d) m sf = substFingerTree Monoid.lemma3 (Deep (Four a b c d) m sf)
a ◁ Deep (Four b c d e) m sf = substFingerTree Monoid.lemma4 (Deep (Two a b) (Node3 c d e ◁ m) sf)


infixl 5 _▷_
_▷_ :  {V : Set} {{m : Monoid V}} {A : Set} {n : ℕ} {v2 v1 : V} → FingerTree A v1 n → Node A v2 n → FingerTree A (v1 ⊕ v2) n
Empty ▷ a = substFingerTree (id2 _) (Single a)
Single b ▷ a = substFingerTree (cong (flip _⊕_ _) (sym (id1 _))) (Deep (One b) Empty (One a))
Deep pr m (One b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Two b a))
Deep pr m (Two c b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Three c b a))
Deep pr m (Three d c b) ▷ a = substFingerTree (sym (assoc _ _ _)) (Deep pr m (Four d c b a))
Deep pr m (Four e d c b) ▷ a = substFingerTree Monoid.lemma5 (Deep pr (m ▷ Node3 e d c) (Two b a))

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
                                           
record Reduce (F : Set → Set) : Set₁ where
  field
    reducer : {A : Set} {B : Set} → (A → B → B) → F A → B → B
    reducel : {A : Set} {B : Set} → (B → A → B) → B → F A → B
  toList : {A : Set} → F A → List A
  toList s = reducer _∷_ s []
    
open Reduce {{...}} public

reduceDigit : {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → Reduce (λ A → Digit A v n)
reduceDigit = record { reducer = reducerDigit ; reducel = reducelDigit }


reduceNode : {V : Set} {{m : Monoid V}} {v : V} {A : Set} {n : ℕ} → Reduce (λ A → Node A v n)
reduceNode = record { reducer = reducerNode ; reducel = reducelNode }

reduceFingerTree : {V : Set} {{m : Monoid V}} {v : V} {A : Set} {n : ℕ} → Reduce (λ A → FingerTree A v n)
reduceFingerTree = record { reducer = reducerFingerTree ; reducel = reducelFingerTree }

reduceList : Reduce List
reduceList = record { reducer = λ f xs z → foldr f z xs ; reducel = foldl }

listToTree : {V : Set} {{m : Monoid V}} {A : Set} {{mea : Measured A V}} → (xs : List A) → FingerTree A (foldr (_⊕_ ∘ measure) ∅ xs) zero
listToTree [] = Empty
listToTree (x ∷ xs) = Leaf x ◁ listToTree xs

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


makeList : (n : ℕ) → List ℕ
makeList zero = []
makeList (suc n) = makeList n ++ (suc n) ∷ []

monoidSize : Monoid ℕ
monoidSize = record { ∅ = zero ; _⊕_ = _+_ ;
                          isMonoid = record { id1 = id1′ ; id2 = λ _ → refl ; assoc = assoc′ }}
                                      where
                                              id1′ : (x : ℕ) → x ≡ x + zero
                                              id1′ zero = refl
                                              id1′ (suc x) = cong suc (id1′ x)
                                              
                                              assoc′ : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
                                              assoc′ zero y z = refl
                                              assoc′ (suc x) y z = cong suc (assoc′ x y z)

measuredSize : {A : Set} → Measured A ℕ
measuredSize = record { measure = λ _ → 1 }

listToSeq : {A : Set} (xs : List A) → FingerTree {{monoidSize}} A (length xs) zero
listToSeq = listToTree {{monoidSize}} {{measuredSize}}

concatSeq : {v1 v2 : ℕ} {A : Set} {n : ℕ} → FingerTree {{monoidSize}} A v1 n → FingerTree {{monoidSize}} A v2 n → FingerTree {{monoidSize}} A (v1 + v2) n
concatSeq = _⋈_

getV : {A : Set} {V : Set} {{m : Monoid V}} {v : V} {n : ℕ} → FingerTree A v n → V
getV {v = v} _ = v

produceSeq : (_ : ℕ) → FingerTree {{monoidSize}} ℕ _ zero -- (foldr (λ _ → _+_ 1) zero (makeList v))
produceSeq = listToSeq ∘ makeList

open import Level using (Level)

hcong' : {I : Set} {i j : I}
       -> (A : I -> Set) {B : {k : I} -> A k -> Set} {x : A i} {y : A j}
       -> i ≡ j
       -> (f : {k : I} -> (x : A k) -> B x)
       -> x ≅ y
       -> f x ≅ f y
hcong' _ refl _ H.refl = H.refl

{-lemmax : (p : v1 ≡ v2) → substFingerTree p (x ∷ []) ≡ x ∷ []-}


lemmax1 : {V : Set} {{m : Monoid V}} {A : Set} {v1 v2 : V} {n : ℕ} (ft : FingerTree A v1 n) (eq : v1 ≡ v2) → substFingerTree eq ft ≅ ft
lemmax1 ft refl = H.refl

lemmax2 : {V : Set} {{m : Monoid V}} {A : Set} {v1 v2 : V} {n : ℕ} (ft : FingerTree A v1 n) (eq : v1 ≡ v2) → toList {{reduceFingerTree {A = A}}} (substFingerTree eq ft) ≡ toList {{reduceFingerTree {A = A}}} ft
lemmax2 {A = A} ft eq = H.≅-to-≡ (hcong' (λ v → FingerTree A v _) (sym eq) (toList {{reduceFingerTree {A = A}}}) (lemmax1 ft eq))

listId1 :  {A : Set} (x : List A) → x ≡ x ++ []
listId1 [] = refl
listId1 (x ∷ xs) = cong (_∷_ x) (listId1 xs)

listAssoc : {A : Set} (x y z : List A) → (x ++ y) ++ z ≡ x ++ y ++ z
listAssoc [] y z = refl
listAssoc (x ∷ xs) y z = cong (_∷_ x) (listAssoc xs y z)

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

lemmax3 : {A : Set} {n : ℕ} {V : Set} {{m : Monoid V}} {v1 v2 v3 : V} (pr : Digit A v1 n) (m : FingerTree A v2 (suc n)) (sf : Digit A v3 n) → toList {{reduceFingerTree {A = A}}} (Deep pr m sf) ≡ toList {{reduceDigit}} pr ++ toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
lemmax3 pr m sf = begin
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

lemmax4 : {V : Set} {v1 v2 : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v1 n) (node : Node A v2 n) → toList {{reduceFingerTree {A = A}}} (node ◁ ft) ≡ toList {{reduceNode {A = A}}} node ++ toList {{reduceFingerTree {A = A}}} ft
lemmax4 {A = A} {n = n} Empty a = begin
                                    toList {{reduceFingerTree {A = A}}} (a ◁ Empty) ≡⟨
                                    lemmax2 (Single a) (id1 _) ⟩
                                    toList {{reduceFingerTree {A = A}}} (Single a) ≡⟨
                                    listId1 (toList {{reduceFingerTree {A = A}}} (Single a)) ⟩
                                    toList {{reduceFingerTree {A = A}}} (Single a) ++ [] ≡⟨
                                    cong (flip _++_ []) lemma ⟩
                                    toList {{reduceNode {A = A}}} a ++ []
                                    ∎
                               where lemma : toList {{reduceFingerTree {A = A}}} (Single a) ≡ toList {{reduceNode {A = A}}} a
                                     lemma = refl
lemmax4 {A = A} (Single b) a = begin
                                 toList {{reduceFingerTree {A = A}}} (a ◁ Single b) ≡⟨
                                 lemmax2 (Deep (One a) Empty (One b))
                                 (cong (flip _⊕_ _) (sym (id1 _)))
                                 ⟩
                                 toList {{reduceFingerTree {A = A}}} (Deep (One a) Empty (One b)) ≡⟨
                                 lemmax3 (One a) Empty (One b) ⟩
                                 toList {{reduceNode {A = A}}} a ++
                                 toList {{reduceFingerTree {A = A}}} (Single b)
                                 ∎
lemmax4 {A = A} (Deep (One b) m sf) a = begin
                                          toList {{reduceFingerTree {A = A}}} (a ◁ Deep (One b) m sf) ≡⟨
                                          lemmax2 (Deep (Two a b) m sf) lemma1 ⟩
                                          toList {{reduceFingerTree {A = A}}} (Deep (Two a b) m sf) ≡⟨
                                          lemmax3 (Two a b) m sf ⟩
                                          toList {{reduceDigit}} (Two a b) ++
                                          toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                          ≡⟨
                                          cong
                                          (λ x →
                                             x ++
                                             toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf)
                                          (lemmaNode a (reducerNode _∷_ b []))
                                          ⟩
                                          (reducerNode _∷_ a [] ++ reducerNode _∷_ b []) ++
                                          toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                          ≡⟨
                                          listAssoc (reducerNode _∷_ a []) (reducerNode _∷_ b [])
                                          (toList {{reduceFingerTree {A = A}}} m ++
                                           toList {{reduceDigit}} sf)
                                          ⟩
                                          reducerNode _∷_ a [] ++
                                          reducerNode _∷_ b [] ++
                                          toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                          ≡⟨ cong (_++_ (reducerNode _∷_ a [])) (sym (lemmax3 (One b) m sf))
                                          ⟩
                                          reducerNode _∷_ a [] ++
                                          toList {{reduceFingerTree {A = A}}} (Deep (One b) m sf)
                                          ∎
lemmax4 {A = A} (Deep (Two b c) m sf) a = begin
                                            toList {{reduceFingerTree {A = A}}} (a ◁ Deep (Two b c) m sf) ≡⟨
                                            lemmax2 (Deep (Three a b c) m sf) lemma2 ⟩
                                            toList {{reduceFingerTree {A = A}}} (Deep (Three a b c) m sf) ≡⟨
                                            lemmax3 (Three a b c) m sf ⟩
                                            toList {{reduceDigit}} (Three a b c) ++
                                            toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                            ≡⟨
                                            cong
                                            (λ x →
                                               x ++
                                               toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf)
                                            (lemmaNode a (toList {{reduceDigit}} (Two b c)))
                                            ⟩
                                            (reducerNode _∷_ a [] ++ toList {{reduceDigit}} (Two b c)) ++
                                            toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                            ≡⟨
                                            listAssoc (reducerNode _∷_ a []) (toList {{reduceDigit}} (Two b c))
                                            (toList {{reduceFingerTree {A = A}}} m ++
                                             toList {{reduceDigit}} sf)
                                            ⟩
                                            reducerNode _∷_ a [] ++
                                            toList {{reduceDigit}} (Two b c) ++
                                            toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                            ≡⟨
                                            cong (_++_ (reducerNode _∷_ a [])) (sym (lemmax3 (Two b c) m sf)) ⟩
                                            reducerNode _∷_ a [] ++
                                            toList {{reduceFingerTree {A = A}}} (Deep (Two b c) m sf)
                                            ∎
lemmax4 {A = A} (Deep (Three b c d) m sf) a = begin
                                                toList {{reduceFingerTree {A = A}}} (a ◁ Deep (Three b c d) m sf)
                                                ≡⟨ lemmax2 (Deep (Four a b c d) m sf) lemma3 ⟩
                                                toList {{reduceFingerTree {A = A}}} (Deep (Four a b c d) m sf) ≡⟨
                                                lemmax3 (Four a b c d) m sf ⟩
                                                toList {{reduceDigit}} (Four a b c d) ++
                                                toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                ≡⟨
                                                cong
                                                (λ x →
                                                   x ++
                                                   toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf)
                                                (lemmaNode a (toList {{reduceDigit}} (Three b c d)))
                                                ⟩
                                                (reducerNode _∷_ a [] ++ toList {{reduceDigit}} (Three b c d)) ++
                                                toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                ≡⟨
                                                listAssoc (reducerNode _∷_ a [])
                                                (toList {{reduceDigit}} (Three b c d))
                                                (toList {{reduceFingerTree {A = A}}} m ++
                                                 toList {{reduceDigit}} sf)
                                                ⟩
                                                reducerNode _∷_ a [] ++
                                                toList {{reduceDigit}} (Three b c d) ++
                                                toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                ≡⟨
                                                cong (_++_ (reducerNode _∷_ a []))
                                                (sym (lemmax3 (Three b c d) m sf))
                                                ⟩
                                                reducerNode _∷_ a [] ++
                                                toList {{reduceFingerTree {A = A}}} (Deep (Three b c d) m sf)
                                                ∎
lemmax4 {A = A} (Deep (Four b c d e) m sf) a = begin
                                                 toList {{reduceFingerTree {A = A}}} (a ◁ Deep (Four b c d e) m sf)
                                                 ≡⟨ lemmax2 (Deep (Two a b) (Node3 c d e ◁ m) sf) lemma4 ⟩
                                                 toList {{reduceFingerTree {A = A}}}
                                                 (Deep (Two a b) (Node3 c d e ◁ m) sf)
                                                 ≡⟨ lemmax3 (Two a b) (Node3 c d e ◁ m) sf ⟩
                                                 toList {{reduceDigit}} (Two a b) ++
                                                 toList {{reduceFingerTree {A = A}}} (Node3 c d e ◁ m) ++
                                                 toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong
                                                 (λ xs →
                                                    toList {{reduceDigit}} (Two a b) ++
                                                    xs ++ toList {{reduceDigit}} sf)
                                                 (lemmax4 m (Node3 c d e))
                                                 ⟩
                                                 toList {{reduceDigit}} (Two a b) ++
                                                 (toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                  toList {{reduceFingerTree {A = A}}} m)
                                                 ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong
                                                 (λ x →
                                                    x ++
                                                    (toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                     toList {{reduceFingerTree {A = A}}} m)
                                                    ++ toList {{reduceDigit}} sf)
                                                 (lemmaNode a (reducerNode _∷_ b []))
                                                 ⟩
                                                 (toList {{reduceNode {A = A}}} a ++
                                                  toList {{reduceNode {A = A}}} b)
                                                 ++
                                                 (toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                  toList {{reduceFingerTree {A = A}}} m)
                                                 ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong
                                                 (_++_
                                                  (toList {{reduceNode {A = A}}} a ++
                                                   toList {{reduceNode {A = A}}} b))
                                                 (listAssoc (toList {{reduceNode {A = A}}} (Node3 c d e))
                                                  (toList {{reduceFingerTree {A = A}}} m)
                                                  (toList {{reduceDigit}} sf))
                                                 ⟩
                                                 (toList {{reduceNode {A = A}}} a ++
                                                  toList {{reduceNode {A = A}}} b)
                                                 ++
                                                 toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                 toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 listAssoc (toList {{reduceNode {A = A}}} a)
                                                 (toList {{reduceNode {A = A}}} b)
                                                 (toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                  toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf)
                                                 ⟩
                                                 toList {{reduceNode {A = A}}} a ++
                                                 toList {{reduceNode {A = A}}} b ++
                                                 toList {{reduceNode {A = A}}} (Node3 c d e) ++
                                                 toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong (_++_ (toList {{reduceNode {A = A}}} a))
                                                 (sym
                                                  (listAssoc (toList {{reduceNode {A = A}}} b)
                                                   (toList {{reduceNode {A = A}}} (Node3 c d e))
                                                   (toList {{reduceFingerTree {A = A}}} m ++
                                                    toList {{reduceDigit}} sf)))
                                                 ⟩
                                                 toList {{reduceNode {A = A}}} a ++
                                                 (toList {{reduceNode {A = A}}} b ++
                                                  toList {{reduceNode {A = A}}} (Node3 c d e))
                                                 ++
                                                 toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong
                                                 (λ x →
                                                    toList {{reduceNode {A = A}}} a ++
                                                    x ++
                                                    toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf)
                                                 (sym (lemmaNode b (toList {{reduceNode {A = A}}} (Node3 c d e))))
                                                 ⟩
                                                 toList {{reduceNode {A = A}}} a ++
                                                 toList {{reduceDigit}} (Four b c d e) ++
                                                 toList {{reduceFingerTree {A = A}}} m ++ toList {{reduceDigit}} sf
                                                 ≡⟨
                                                 cong (_++_ (toList {{reduceNode {A = A}}} a))
                                                 (sym (lemmax3 (Four b c d e) m sf))
                                                 ⟩
                                                 toList {{reduceNode {A = A}}} a ++
                                                 toList {{reduceFingerTree {A = A}}} (Deep (Four b c d e) m sf)
                                                 ∎

lemmax : {V : Set} {{m : Monoid V}} {A : Set} {{mea : Measured A V}} (xs : List A) → toList {{reduceFingerTree {A = A}}} (listToTree xs) ≡ xs
lemmax [] = refl
lemmax {A = A} (x ∷ xs) = begin
                           toList {{reduceFingerTree {A = A}}} (Leaf x ◁ listToTree xs) ≡⟨
                           lemmax4 (listToTree xs) (Leaf x) ⟩
                           x ∷ toList {{reduceFingerTree {A = A}}} (listToTree xs) ≡⟨
                           cong (_∷_ x) (lemmax xs) ⟩ x ∷ xs ∎

data Split (F1 : Set → Set) (A : Set) (F2 : Set → Set) : Set where
  split : F1 A → A → F2 A → Split F1 A F2

splitTree : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {{mea : Measured A V}} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) {le : isEmpty ft ≡ false} → Split (λ _ → FingerTree A _ n) (Node A _ n) (λ _ → FingerTree A _ n)
splitTree p i Empty {}
splitTree p i (Single x) = split Empty x Empty
splitTree p i (Deep {v1} {v2} {v3} pr m sf) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
splitTree p i (Deep (One x) m₁ sf) | true | w = {!!}
splitTree p i (Deep (Two x x₁) m₁ sf) | true | w = {!!}
splitTree p i (Deep (Three x x₁ x₂) m₁ sf) | true | w = {!!}
splitTree p i (Deep (Four x x₁ x₂ x₃) m₁ sf) | true | w  = {!!}
... | _ | true = {!!}
... | _ | _ = {!!}


{-
splitV1 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → V
splitV1 p i (One a) = ∅
splitV1 p i (Two {v1} a b) = splitV1 {!!} {!!} (One b)
splitV1 p i (Three {v1} {v2} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = ∅
... | _ | true = v1
... | _ | _ = v1 ⊕ v2
splitV1 p i (Four {v1} {v2} {v3} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = ∅
... | _ | true | _ = v1
... | _ | _ | true = v1 ⊕ v2
... | _ | _ | _ = (v1 ⊕ v2) ⊕ v3
-}
{-
splitV2 : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → V
splitV2 p i (One {v} a) = v
splitV2 p i (Two {v1} {v2} a b) with p (i ⊕ v1)
... | true = v1
... | false = v2
splitV2 p i (Three {v1} {v2} {v3} a b c) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = v1
... | _ | true = v1 ⊕ v2
... | _ | _ = v3
splitV2 p i (Four {v1} {v2} {v3} {v4} a b c d) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2) | p (((i ⊕ v1) ⊕ v2) ⊕ v3)
... | true | _ | _ = v1
... | _ | true | _ = v1 ⊕ v2
... | _ | _ | true = (v1 ⊕ v2) ⊕ v3
... | _ | _ | _ = v4

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
... | true | _ | _ = v2 ⊕ (v3 ⊕ v4)
... | _ | true | _ = v3 ⊕ v4
... | _ | _ | true = v4
... | _ | _ | _ = ∅
-}
{-
splitDigit : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (p : V → Bool) (i : V) (as : Digit A v n) → Split (λ _ → NodeList A (splitV1 p i as) n) (Node A (splitV2 p i as) n) (λ _ → NodeList A (splitV3 p i as) n)
splitDigit p i (One a) = split [] a []
splitDigit p i (Two {v1} a b) with p (i ⊕ v1)
... | true = split [] a (b ∷ [])
... | false = (λ {split l x r → split (a ∷ l) x r}) splitDigit p (_⊕_ i v1) (One b)
splitDigit p i (Three {v1} a b c) with p (i ⊕ v1)
... | true = split [] a (b ∷ c ∷ [])
... | false = (λ {split l x r → split (a ∷ l) x r}) splitDigit p (_⊕_ i v1) (Two b c)
splitDigit p i (Four {v1} a b c d) with p (i ⊕ v1)
... | true = split [] a (b ∷ c ∷ d ∷ [])
... | false = (λ {split l x r → split (a ∷ l) x r}) splitDigit p (_⊕_ i v1) (Three b c d)



splitTree : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {{mea : Measured A V}} {n : ℕ} (p : V → Bool) (i : V) (ft : FingerTree A v n) → Split (λ A → FingerTree A _ n) (Node A _ n) (λ A → FingerTree A _ n)
splitTree p i Empty = {!!}
splitTree p i (Single x) = split Empty x Empty
splitTree p i (Deep {v1} {v2} pr m sf) with p (i ⊕ v1) | p ((i ⊕ v1) ⊕ v2)
... | true | _ = (λ { split l x r → split {!(digitToTree l)!} x {!r!} }) splitDigit p i pr
... | _ | true = {!(λ { split l x r → split (digitToTree l) x {!!} }) splitDigit p i pr!}
... | _ | _ = {!!}
-}
