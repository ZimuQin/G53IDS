open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function using (_∘_; flip)

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
  open IsMonoid isMonoid public

open Monoid {{...}} public

lemma1 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 : V} → _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡ _⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)
lemma1 {_} {v1} {v2} {v3} {v4} = begin
                                    _⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4 ≡⟨
                                    cong (flip _⊕_ v4) (assoc v1 v2 v3) ⟩
                                    _⊕_ (_⊕_ v1 (_⊕_ v2 v3)) v4 ≡⟨ assoc v1 (_⊕_ v2 v3) v4 ⟩
                                    _⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4) ∎

lemma2 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 v5 : V} → _⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5 ≡ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5)
lemma2 {_} {v1} {v2} {v3} {v4} {v5} = begin
                                        _⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5 ≡⟨ cong (flip _⊕_ v5) lemma1 ⟩
                                        _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ v2 v3) v4)) v5 ≡⟨ assoc v1 (_⊕_ (_⊕_ v2 v3) v4) v5 ⟩
                                        _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) ∎

lemma3 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 v5 v6 : V} → _⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5) v6 ≡ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) v6)
lemma3 {_} {v1} {v2} {v3} {v4} {v5} {v6} = begin _⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v1 v2) v3) v4) v5) v6 ≡⟨ cong (flip _⊕_ v6) lemma2 ⟩
                                                 _⊕_ (_⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5)) v6 ≡⟨ assoc v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) v6 ⟩
                                                 _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) v6) ∎

lemma4 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 v5 v6 v7 : V} → _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6)) v7 ≡ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) v6) v7)
lemma4 {_} {v1} {v2} {v3} {v4} {v5} {v6} {v7} = begin
                                                  _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6)) v7 ≡⟨
                                                  cong (λ vx → _⊕_ (_⊕_ (_⊕_ v1 v2) vx) v7) (assoc (_⊕_ v3 v4) v5 v6)
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ v3 v4) (_⊕_ v5 v6))) v7 ≡⟨
                                                  cong (λ vx → _⊕_ (_⊕_ (_⊕_ v1 v2) vx) v7) (assoc v3 v4 (_⊕_ v5 v6))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ v3 (_⊕_ v4 (_⊕_ v5 v6)))) v7 ≡⟨
                                                  cong (flip _⊕_ v7) (assoc v1 v2 (_⊕_ v3 (_⊕_ v4 (_⊕_ v5 v6))))
                                                  ⟩
                                                  _⊕_ (_⊕_ v1 (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 (_⊕_ v5 v6))))) v7 ≡⟨
                                                  assoc v1 (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 (_⊕_ v5 v6)))) v7 ⟩
                                                  _⊕_ v1 (_⊕_ (_⊕_ v2 (_⊕_ v3 (_⊕_ v4 (_⊕_ v5 v6)))) v7) ≡⟨
                                                  cong (λ vx → _⊕_ v1 (_⊕_ vx v7))
                                                  (sym (assoc v2 v3 (_⊕_ v4 (_⊕_ v5 v6))))
                                                  ⟩
                                                  _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ v2 v3) (_⊕_ v4 (_⊕_ v5 v6))) v7) ≡⟨
                                                  cong (λ vx → _⊕_ v1 (_⊕_ vx v7))
                                                  (sym (assoc (_⊕_ v2 v3) v4 (_⊕_ v5 v6)))
                                                  ⟩
                                                  _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) (_⊕_ v5 v6)) v7) ≡⟨
                                                  cong (λ vx → _⊕_ v1 (_⊕_ vx v7))
                                                  (sym (assoc (_⊕_ (_⊕_ v2 v3) v4) v5 v6))
                                                  ⟩ _⊕_ v1 (_⊕_ (_⊕_ (_⊕_ (_⊕_ (_⊕_ v2 v3) v4) v5) v6) v7) ∎

lemma5 : {V : Set} {{m : Monoid V}} {v1 v2 v3 v4 v5 v6 v7 : V} → _⊕_ (_⊕_ v1 (_⊕_ v2 (_⊕_ (_⊕_ v3 v4) v5))) (_⊕_ v6 v7) ≡ _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6)) v7
lemma5 {_} {v1} {v2} {v3} {v4} {v5} {v6} {v7} = begin
                                                  _⊕_ (_⊕_ v1 (_⊕_ v2 (_⊕_ (_⊕_ v3 v4) v5))) (_⊕_ v6 v7) ≡⟨
                                                  cong (flip _⊕_ (_⊕_ v6 v7))
                                                  (sym (assoc v1 v2 (_⊕_ (_⊕_ v3 v4) v5)))
                                                  ⟩
                                                  _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ v3 v4) v5)) (_⊕_ v6 v7) ≡⟨
                                                  assoc (_⊕_ v1 v2) (_⊕_ (_⊕_ v3 v4) v5) (_⊕_ v6 v7) ⟩
                                                  _⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) (_⊕_ v6 v7)) ≡⟨
                                                  cong (_⊕_ (_⊕_ v1 v2)) (sym (assoc (_⊕_ (_⊕_ v3 v4) v5) v6 v7)) ⟩
                                                  _⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6) v7) ≡⟨
                                                  sym (assoc (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6) v7) ⟩
                                                  _⊕_ (_⊕_ (_⊕_ v1 v2) (_⊕_ (_⊕_ (_⊕_ v3 v4) v5) v6)) v7 ∎
