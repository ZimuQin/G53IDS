open import FTM
open import Data.Nat hiding (_<_)
open import Data.List using (List; []; _∷_; foldr; foldl; length; _++_)
open import Monoid
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function using (_∘_; flip)
open import Measured
open import Data.Product
open import Data.Bool
open import Data.Empty

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

lemmaEmpty : {V : Set} {v : V} {{m : Monoid V}} {A : Set} {n : ℕ} (ft : FingerTree A v n) → v ≢ ∅ → isEmpty ft ≡ false
lemmaEmpty Empty le = ⊥-elim (le refl)
lemmaEmpty (Single _) le = refl
lemmaEmpty (Deep _ _ _) le = refl

suc_neq_zero : (n : ℕ) → suc n ≢ zero
suc_neq_zero n ()

_<_ : ℕ → ℕ → Bool
zero  < zero  = false
zero  < suc n = true
suc m < zero  = false
suc m < suc n = m < n

_!_ : {v : ℕ} {A : Set} (ft : FingerTree {{monoidSize}} A (suc v) zero) (i : ℕ) → A
_!_ {v} t i with splitTree {{monoidSize}} (_<_ i) 0 t {lemmaEmpty t (suc_neq_zero v)}
... | split _ (Leaf x) _ = x

listToSeq : {A : Set} (xs : List A) → FingerTree {{monoidSize}} A (length xs) zero
listToSeq = listToTree {{monoidSize}} {{measuredSize}}

concatSeq : {v1 v2 : ℕ} {A : Set} {n : ℕ} → FingerTree {{monoidSize}} A v1 n → FingerTree {{monoidSize}} A v2 n → FingerTree {{monoidSize}} A (v1 + v2) n
concatSeq = _⋈_

splitAt : {v : ℕ} {A : Set} {n : ℕ} (i : ℕ) (ft : FingerTree {{monoidSize}} A v n) → FingerTree {{monoidSize}} A (split′V1 {{monoidSize}} (_<_ i) ft) n × FingerTree {{monoidSize}} A (split′V2 {{monoidSize}} (_<_ i) ft) n
splitAt i = split′ {{monoidSize}} (_<_ i)

produceSeq : (n : ℕ) → FingerTree {{monoidSize}} ℕ n zero -- (foldr (λ _ → _+_ 1) zero (makeList v))
produceSeq n = substFingerTree {{monoidSize}} (lemma n) ((listToSeq ∘ makeList) n)
  where lemma′ : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
        lemma′ [] ys = refl
        lemma′ (x ∷ xs) ys = cong suc (lemma′ xs ys)
        lemma′′ : (n : ℕ) → n + 1 ≡ suc n
        lemma′′ zero = refl
        lemma′′ (suc n) = cong suc (lemma′′ n)
        lemma : (n : ℕ) → length (makeList n) ≡ n
        lemma zero = refl
        lemma (suc n) = begin length (makeList (suc n)) ≡⟨ lemma′ (makeList n) (suc n ∷ []) ⟩
                              length (makeList n) + 1 ≡⟨ lemma′′ (length (makeList n)) ⟩
                              suc (length (makeList n)) ≡⟨ cong suc (lemma n) ⟩
                              suc n ∎
