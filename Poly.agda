--- encode the type system of the assertion language in VST-IDE

{-# OPTIONS --without-K #-}

module plfa.part2.Poly where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Agda.Builtin.Bool using (true; false)

data Kind : Set where
 ⋆    :  Kind
 _⇛_  :  Kind → Kind → Kind

K-⟦_⟧ : Kind → Set₁
K-⟦ ⋆ ⟧     = Set
K-⟦ j ⇛ k ⟧ = K-⟦ j ⟧ → K-⟦ k ⟧

kind-≟ : ∀ (j k : Kind) → Dec (j ≡ k)
kind-≟ ⋆ ⋆ = true because ofʸ refl
kind-≟ ⋆ (k ⇛ k₁) = false because ofⁿ λ ()
kind-≟ (j ⇛ j₁) ⋆ = false because ofⁿ λ ()
kind-≟ (j ⇛ j') (k ⇛ k') with kind-≟ j k
... | no ¬j≡k = false because ofⁿ λ { refl → ¬j≡k refl }
... | yes j≡k with kind-≟ j' k'
...              | yes j'≡k' rewrite j≡k rewrite j'≡k' = true because ofʸ refl
...              | no ¬j'≡k' = false because ofⁿ λ { refl → ¬j'≡k' refl }

infixl 5  _,_

data KindContext : Set where
  ∅   : KindContext
  _,_ : KindContext → Kind → KindContext

infix  4  _∋-K_
infix  9  S_

data _∋-K_ : KindContext → Kind → Set where

  Z : ∀ {Γ A}
        ------------
      → Γ , A ∋-K A

  S_ : ∀ {Γ A B}
     → Γ ∋-K A
       ------------
     → Γ , B ∋-K A

infixr 7  _⇒_
infixl 8  _∘_
infix  9  ``_

infix  4  _⊩_

data _⊩_ (Γ : KindContext) : Kind → Set where
  ``_  :  ∀ {k} → (Γ ∋-K k) → Γ ⊩ k
  _∘_  :  ∀ {j k} → Γ ⊩ j ⇛ k → Γ ⊩ j → Γ ⊩ k
  _⇒_  :  Γ ⊩ ⋆ → Γ ⊩ ⋆ → Γ ⊩ ⋆

data KindContextDenote : KindContext → Set₁ where
  ∅   : KindContextDenote ∅
  _,_ : ∀ {Γ k}
        → KindContextDenote Γ
        → K-⟦ k ⟧
          ------------------
        → KindContextDenote (Γ , k)

typeIdDenote : ∀ {Γ : KindContext} {k} → (Γ ∋-K k) → KindContextDenote Γ → K-⟦ k ⟧
typeIdDenote {Γ , .k} {k} Z (E , K)    = K
typeIdDenote {Γ , _} {k} (S n) (E , _) = typeIdDenote n E

T-⟦_In_⟧ : ∀ {Γ : KindContext} {k} → Γ ⊩ k → KindContextDenote Γ → K-⟦ k ⟧
T-⟦ `` x In E ⟧  = typeIdDenote x E
T-⟦ a ∘ b In E ⟧ = T-⟦ a In E ⟧ T-⟦ b In E ⟧
T-⟦ a ⇒ b In E ⟧ = T-⟦ a In E ⟧ → T-⟦ b In E ⟧

infix  5  _⨟_

_⨟_ : KindContext → KindContext → KindContext
Γ ⨟ ∅            = Γ
Γ ⨟ (Δ , A) = (Γ ⨟ Δ) , A

--- type scheme
infix  4  _⊩Δ_

data _⊩Δ_ (Γ : KindContext) (K : Kind) : Set where
  [_&_] : (Δ : KindContext) → Γ ⨟ Δ ⊩ K → Γ ⊩Δ K

data TypeContext (Γ : KindContext) : Set where
  ∅    : TypeContext Γ
  _,_  : TypeContext Γ → Γ ⊩Δ ⋆ → TypeContext Γ

infix  4 _∋_

data _∋_ {Γ : KindContext} : TypeContext Γ → Γ ⊩Δ ⋆ → Set where

  Z : ∀ {Δ A}
      ------------------
    → Δ , A ∋ A

  S_ : ∀ {Δ A B}
     → Δ ∋ A
       ------------------
     → Δ , B ∋ A

subst : ∀ {Γ Δ}
  → (∀ {K} → Γ ∋-K K → Δ ⊩ K)
  → (∀ {K} → Γ ⊩ K → Δ ⊩ K)
subst σ (`` x)  = σ x
subst σ (t ∘ s) = (subst σ t) ∘ (subst σ s)
subst σ (s ⇒ t) = (subst σ s) ⇒ (subst σ t)

data SeparateContextCase {K} (Γ Δ : KindContext)
       (In : Γ ⨟ Δ ∋-K K) : Set where
  in-Γ : Γ ∋-K K → SeparateContextCase Γ Δ In
  in-Δ : Δ ∋-K K → SeparateContextCase Γ Δ In

separateContext : ∀ {K} (Γ Δ : KindContext)
  → (In : Γ ⨟ Δ ∋-K K) → SeparateContextCase Γ Δ In
separateContext Γ ∅ p            = in-Γ p
separateContext Γ (Δ , K) Z = in-Δ Z
separateContext Γ (Δ , K) (S n) with separateContext Γ Δ n
... | in-Γ p = in-Γ p
... | in-Δ q = in-Δ (S q)

lift : ∀ {Γ Δ}
  → (∀ {K} → Δ ∋-K K → Γ ⊩ K)
  → (∀ {K} → Γ ⨟ Δ ∋-K K → Γ ⊩ K)
lift {Γ} {Δ} σ p with separateContext Γ Δ p
... | in-Γ p = `` p
... | in-Δ q = σ q

data Instantiate (Γ : KindContext) : KindContext → Set where
  ∅   : Instantiate Γ ∅
  _,_ : ∀ {Δ} {K} → Instantiate Γ Δ → Γ ⊩ K → Instantiate Γ (Δ , K)

doInstantiate : ∀ {Γ Δ}
  → Instantiate Γ Δ
  → ∀ {K} → Δ ∋-K K → Γ ⊩ K
doInstantiate (σ , K) Z     = K
doInstantiate (σ , K) (S n) = doInstantiate σ n

substParameter : ∀ {Γ Δ}
  → (Instantiate Γ Δ)
  → (∀ {K} → Γ ⨟ Δ ⊩ K → Γ ⊩ K)
substParameter σ t = subst (lift (doInstantiate σ)) t

infix  4  _⊢_

infixl 7  _∙_
infix  9  `_∙_

data _⊢_ {Γ : KindContext} (Δ : TypeContext Γ) : Γ ⊩ ⋆ → Set where
  `_∙_  : ∀ {Γ' : KindContext} {T}
        → (p : Δ ∋ [ Γ' & T ])
        → (σ : Instantiate Γ Γ')
          ------------
        → Δ ⊢ substParameter σ T
  _∙_ : ∀ {a b}
        → Δ ⊢ a ⇒ b
        → Δ ⊢ a
          ------------
        → Δ ⊢ b

composeKindContextDenote : ∀ {Γ Δ}
  → KindContextDenote Γ
  → KindContextDenote Δ
    ---------------------
  → KindContextDenote (Γ ⨟ Δ)
composeKindContextDenote E ∅ = E
composeKindContextDenote E (F , V) = composeKindContextDenote E F , V

data TypeContextDenote {Γ : KindContext} (E : KindContextDenote Γ) :
  TypeContext Γ → Set₁ where
  ∅   : TypeContextDenote E ∅
  _,_ : ∀ {Γ' Δ T}
        → TypeContextDenote E Γ'
        → ((F : KindContextDenote Δ) →
            T-⟦ T In composeKindContextDenote E F ⟧)
          ------------------
        → TypeContextDenote E (Γ' , [ Δ & T ])

instantiationDenote : ∀ {Γ Δ}
  → KindContextDenote Γ
  → Instantiate Γ Δ
    ------------------
  → KindContextDenote Δ
instantiationDenote E ∅       = ∅
instantiationDenote E (σ , K) = (instantiationDenote E σ) , T-⟦ K In E ⟧

subst-S-≡ : ∀ {Γ Δ J K V}
          → (σ : Instantiate Γ Δ)
          → (p : Γ ⨟ Δ ∋-K K) → (q : Γ ⨟ (Δ , J) ∋-K K) → (q ≡ S p)
            ------------
          → substParameter (σ , V) (`` q) ≡ substParameter σ (`` p)
subst-S-≡ {Γ} {Δ} {J} σ p q eq
  rewrite eq with separateContext Γ Δ p
... | in-Γ p = refl
... | in-Δ q = refl

subst-≡-compose-id : ∀ {Γ Δ K}
  → (x : Γ ⨟ Δ ∋-K K) → (σ : Instantiate Γ Δ) → (E : KindContextDenote Γ)
  → T-⟦ substParameter σ (`` x) In E ⟧
    ------------------
  ≡ typeIdDenote x
      (composeKindContextDenote E (instantiationDenote E σ))
subst-≡-compose-id {Γ} {.∅} x ∅ E = refl
subst-≡-compose-id {Γ} {_ , _} Z (σ , _) E = refl
subst-≡-compose-id {Γ} {Δ , J} {K} (S x) (σ , V) E
  rewrite (subst-S-≡ {Γ} {Δ} {J} {K} {V} σ x (S x) refl) = subst-≡-compose-id x σ E

subst-≡-compose : ∀ {Γ Δ K}
  → (σ : Instantiate Γ Δ) → (T : Γ ⨟ Δ ⊩ K) → (E : KindContextDenote Γ)
    ------------
  → T-⟦ substParameter σ T In E ⟧
  ≡ T-⟦ T In composeKindContextDenote E (instantiationDenote E σ) ⟧
subst-≡-compose σ (`` x) E = subst-≡-compose-id x σ E
subst-≡-compose σ (t ∘ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl
subst-≡-compose σ (t ⇒ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl

termIdDenote : ∀ {Γ Γ' E} {Δ : TypeContext Γ} {T}
  → (Δ ∋ [ Γ' & T ])
  → (σ : Instantiate Γ Γ')
  → TypeContextDenote E Δ → T-⟦ substParameter σ T In E ⟧
termIdDenote {Γ} {Γ'} {E} {Δ} {T} Z σ (M , F)
  rewrite (subst-≡-compose σ T E) = (F (instantiationDenote E σ))
termIdDenote (S p) σ (M , _) = termIdDenote p σ M

⟦_In_⟧ : ∀ {Γ E T} {Δ : TypeContext Γ}
  → Δ ⊢ T
  → TypeContextDenote E Δ
  → T-⟦ T In E ⟧
⟦ ` x ∙ σ In E ⟧ = termIdDenote x σ E
⟦ a ∙ b In E ⟧   = ⟦ a In E ⟧ ⟦ b In E ⟧

--- test

length-K : KindContext → ℕ
length-K ∅        =  zero
length-K (Γ , _)  =  suc (length-K Γ)

length-T : ∀ {Γ} → TypeContext Γ → ℕ
length-T ∅        =  zero
length-T (Γ , _)  =  suc (length-T Γ)

count-K : ∀ {Γ} → {n : ℕ} → (p : n < length-K Γ) → Σ[ K ∈ Kind ] (Γ ∋-K K)
count-K {Γ , K} {zero} (s≤s z≤n)  =  ⟨ K , Z ⟩ 
count-K {Γ , _} {(suc n)} (s≤s p) with count-K p
...                                  | ⟨ K , n ⟩ = ⟨ K , S n ⟩

count-T : ∀ {Γ Δ} → {n : ℕ} → (p : n < length-T Δ) → Σ[ T ∈ Γ ⊩Δ ⋆ ] (Δ ∋ T)
count-T {Γ} {Δ , T} {zero} (s≤s z≤n)  =  ⟨ T , Z ⟩ 
count-T {Γ} {Δ , _} {(suc n)} (s≤s p) with count-T p
...                                  | ⟨ T , n ⟩ = ⟨ T , S n ⟩

K-#_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length-K Γ)}
      --------------------------------
    → Γ ⊩ proj₁ (count-K (toWitness n∈Γ))
K-#_ n {n∈Γ} = `` proj₂ (count-K (toWitness n∈Γ))

#-help : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length-T Δ)}
      --------------------------------
    → Σ[ Γ' ∈ KindContext ] (
      Σ[ B  ∈ Γ ⨟ Γ' ⊩ ⋆ ] (
        (σ : Instantiate Γ Γ')
      → Δ ⊢ substParameter σ B))
#-help n {n∈Γ} with count-T (toWitness n∈Γ)
...                 | ⟨ [ Δ & T ] , x ⟩ = ⟨ Δ , ⟨ T , `_∙_ x ⟩ ⟩

# : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length-T Δ)}
      ------------
    → (σ : Instantiate Γ (proj₁ (#-help {Γ} {Δ} n {n∈Γ})))
    → Δ ⊢ substParameter σ (proj₁ (proj₂ (#-help {Γ} {Δ} n)))
# n = proj₂ (proj₂ (#-help n))

K-Γ : KindContext
K-Γ = ∅ , ⋆
        , ⋆ ⇛ ⋆

T-Γ : TypeContext K-Γ
T-Γ = ∅ , [ ∅ & K-# 1 ]
        , [ ∅ & K-# 1 ⇒ K-# 1 ]
        , [ ∅ , ⋆ & K-# 1 ∘ K-# 0 ]
        , [ ∅ , ⋆ & K-# 0 ⇒ K-# 1 ∘ K-# 0 ⇒ K-# 1 ∘ K-# 0 ]
        , [ ∅ , ⋆ & K-# 0 ⇒ K-# 1 ∘ K-# 0 ⇒ K-# 0 ]

K-⟦⟧ : KindContextDenote K-Γ
K-⟦⟧ = ∅ , ℕ , List

T-⟦⟧ : TypeContextDenote K-⟦⟧ T-Γ
T-⟦⟧ = ∅ , (λ { ∅ → zero })
         , (λ { ∅ → suc })
         , (λ { (∅ , T) → [] })
         , (λ { (∅ , T) → _∷_ })
         , (λ { (∅ , T) → λ { x [] → x ; x (y ∷ l) → y} })

_ : ⟦ # 0 (∅ , K-# 1) ∙
        (# 3 ∅ ∙ # 4 ∅) ∙
        (# 1 (∅ , K-# 1) ∙ # 4 ∅ ∙ # 2 (∅ , K-# 1)) In T-⟦⟧ ⟧ ≡ zero
_ = refl

