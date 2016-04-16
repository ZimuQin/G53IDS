open import FTM
open import Data.Nat hiding (_<_; _≤_; _≤′_)
open import Data.List using (List; []; _∷_; foldr; foldl; length; _++_)
open import Monoid
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function using (_∘_; flip)
open import Measured
open import Data.Product
open import Data.Bool
open import Data.Empty
open import Data.Maybe

data Prio (A : Set) : Set where
  mInfty : Prio A
  prio   : (a : A) → Prio A
  
_<_ : ℕ → ℕ → Bool
zero  < zero  = false
zero  < suc n = true
suc m < zero  = false
suc m < suc n = m < n

trans1_< : (x y z : ℕ) → (x < y ≡ true) → (y < z ≡ true) → (x < z ≡ true)
trans1_< zero zero _ ()
trans1_< (suc x) zero _ ()
trans1_< _ (suc y) zero _ ()
trans1_< zero (suc y) (suc z) refl le2 = refl
trans1_< (suc x) (suc y) (suc z) le1 le2 = trans1_< x y z le1 le2

trans2_< : (x y z : ℕ) → (x < y ≡ false) → (y < z ≡ false) → (x < z ≡ false)
trans2_< zero zero zero _ _ = refl
trans2_< zero zero (suc _) _ ()
trans2_< zero (suc _) _ ()
trans2_< (suc x) zero zero eq eq2 = refl
trans2_< (suc x) zero (suc z) eq ()
trans2_< (suc x) (suc y) zero eq eq2 = refl
trans2_< (suc x) (suc y) (suc z) eq eq2 = trans2_< x y z eq eq2

_≤_ : ℕ → ℕ → Bool
zero ≤ b = true
suc a ≤ zero = false
suc a ≤ suc b = a ≤ b

_≤′_ : Prio ℕ → Prio ℕ → Bool
mInfty ≤′ _ = true
prio a ≤′ mInfty = false
prio a ≤′ prio b = a ≤ b

false_neq_true : false ≢ true
false_neq_true ()

monoidPrio : Monoid (Prio ℕ)
monoidPrio = record { ∅ = mInfty ; _⊕_ = _⊕′_ ;
                          isMonoid = record { id1 = id1′ ; id2 = λ _ → refl ; assoc = assoc′ }}
                                      where
                                              _⊕′_ : Prio ℕ → Prio ℕ → Prio ℕ
                                              mInfty ⊕′ p = p
                                              p ⊕′ mInfty = p
                                              prio m ⊕′ prio n with m < n
                                              ... | true  = prio n
                                              ... | false = prio m
                                              
                                              id1′ : (x : Prio ℕ) → x ≡ x ⊕′ mInfty
                                              id1′ mInfty = refl
                                              id1′ (prio _) = refl
                                              
                                              assoc′ : (x y z : Prio ℕ) → (x ⊕′ y) ⊕′ z ≡ x ⊕′ (y ⊕′ z)
                                              assoc′ mInfty y z = refl
                                              assoc′ x mInfty z = cong (λ v → v ⊕′ z) (sym (id1′ x))
                                              assoc′ x y mInfty = trans (sym (id1′ (x ⊕′ y))) (cong (_⊕′_ x) (id1′ y))
                                              assoc′ (prio x) (prio y) (prio z) with (_<_ x) y | inspect (_<_ x) y
                                              ... | true | [ eq ] with y < z | inspect (_<_ y) z
                                              ...  | true | [ eq2 ] with x < z | inspect (_<_ x) z
                                              ...   | true | _ = refl
                                              ...   | false | [ eq3 ] = ⊥-elim (false_neq_true (trans (sym eq3) (trans1_< x y z eq eq2)))
                                              assoc′ (prio x) (prio y) (prio z) | true | [ eq ] | false | _ with x < y
                                              ...   | true = refl
                                              ...   | false = ⊥-elim (false_neq_true eq)
                                              assoc′ (prio x) (prio y) (prio z) | false | [ eq ] with y < z | inspect (_<_ y) z
                                              ... | true | _ = refl
                                              ... | false | [ eq2 ] with x < z | inspect (_<_ x) z
                                              ...  | true | [ eq3 ] = ⊥-elim (false_neq_true (trans (sym (trans2_< x y z eq eq2)) eq3))
                                              ...  | false | _ with x < y
                                              ...   | true = ⊥-elim (false_neq_true (sym eq))
                                              ...   | false = refl

measuredPrio : Measured ℕ (Prio ℕ)
measuredPrio = record { measure = λ x → prio x }



extractMax : {v : Prio ℕ} (ft : FingerTree {{monoidPrio}} ℕ v zero) → Maybe (ℕ × FingerTree {{monoidPrio}} ℕ (_⊕_ {{monoidPrio}}
                                                                                                                (splitTreeV1 {{monoidPrio}} (_≤′_ v) mInfty ft)
                                                                                                                (splitTreeV3 {{monoidPrio}} (_≤′_ v) mInfty ft)) zero)
extractMax Empty = nothing
extractMax (Single (Leaf x)) = just (x , substFingerTree {{monoidPrio}} (id1 {{monoidPrio}} mInfty) Empty)
extractMax (Deep pr m sf) with splitTree {{monoidPrio}} (_≤′_ (getV (Deep pr m sf))) mInfty (Deep pr m sf) {refl}
... | split l (Leaf x) r = just (x , l ⋈ r)
