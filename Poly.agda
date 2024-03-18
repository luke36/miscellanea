--- encode the type system of the assertion language in VST-IDE

{-# OPTIONS --without-K #-}

module plfa.part2.Poly where

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness)
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

--- todo : type-≟ , term-≟

infixl 5  _,_

data TypeContext : Set where
  ∅   : TypeContext
  _,_ : TypeContext → Kind → TypeContext

infix  4  _∋-T_
infix  9  S_

data _∋-T_ : TypeContext → Kind → Set where

  Z : ∀ {Γ A}
        ------------
      → Γ , A ∋-T A

  S_ : ∀ {Γ A B}
     → Γ ∋-T A
       ------------
     → Γ , B ∋-T A

infixr 7  _⇒_
infixl 8  _∘_
infix  9  ``_

infix  4  _⊩_

data _⊩_ (Γ : TypeContext) : Kind → Set where
  ``_  :  ∀ {k} → (Γ ∋-T k) → Γ ⊩ k
  _∘_  :  ∀ {j k} → Γ ⊩ j ⇛ k → Γ ⊩ j → Γ ⊩ k
  _⇒_  :  Γ ⊩ ⋆ → Γ ⊩ ⋆ → Γ ⊩ ⋆

data TypeContextDenote : TypeContext → Set₁ where
  ∅   : TypeContextDenote ∅
  _,_ : ∀ {Γ k}
        → TypeContextDenote Γ
        → K-⟦ k ⟧
          ------------------
        → TypeContextDenote (Γ , k)

typeIdDenote : ∀ {Γ : TypeContext} {k} → (Γ ∋-T k) → TypeContextDenote Γ → K-⟦ k ⟧
typeIdDenote {Γ , .k} {k} Z (E , K)    = K
typeIdDenote {Γ , _} {k} (S n) (E , _) = typeIdDenote n E

T-⟦_In_⟧ : ∀ {Γ : TypeContext} {k} → Γ ⊩ k → TypeContextDenote Γ → K-⟦ k ⟧
T-⟦ `` x In E ⟧  = typeIdDenote x E
T-⟦ a ∘ b In E ⟧ = T-⟦ a In E ⟧ T-⟦ b In E ⟧
T-⟦ a ⇒ b In E ⟧ = T-⟦ a In E ⟧ → T-⟦ b In E ⟧

infix  5  _⨟_

_⨟_ : TypeContext → TypeContext → TypeContext
Γ ⨟ ∅            = Γ
Γ ⨟ (Δ , A) = (Γ ⨟ Δ) , A

--- type scheme
infix  4  _⊩Δ_

data _⊩Δ_ (Γ : TypeContext) (K : Kind) : Set where
  [_&_] : (Δ : TypeContext) → Γ ⨟ Δ ⊩ K → Γ ⊩Δ K

data Context (Γ : TypeContext) : Set where
  ∅    : Context Γ
  _,_  : Context Γ → Γ ⊩Δ ⋆ → Context Γ

infix  4 _∋_

data _∋_ {Γ : TypeContext} : Context Γ → Γ ⊩Δ ⋆ → Set where

  Z : ∀ {Δ A}
      ------------------
    → Δ , A ∋ A

  S_ : ∀ {Δ A B}
     → Δ ∋ A
       ------------------
     → Δ , B ∋ A

subst : ∀ {Γ Δ}
  → (∀ {K} → Γ ∋-T K → Δ ⊩ K)
  → (∀ {K} → Γ ⊩ K → Δ ⊩ K)
subst σ (`` x)  = σ x
subst σ (t ∘ s) = (subst σ t) ∘ (subst σ s)
subst σ (s ⇒ t) = (subst σ s) ⇒ (subst σ t)

data SeparateContextCase (K : Kind) (Γ Δ : TypeContext) : Set where
  in-Γ : Γ ∋-T K → SeparateContextCase K Γ Δ
  in-Δ : Δ ∋-T K → SeparateContextCase K Γ Δ

separateContext : ∀ {K} (Γ Δ : TypeContext)
  → (In : Γ ⨟ Δ ∋-T K) → SeparateContextCase K Γ Δ
separateContext Γ ∅ p       = in-Γ p
separateContext Γ (Δ , K) Z = in-Δ Z
separateContext Γ (Δ , K) (S n) with separateContext Γ Δ n
... | in-Γ p = in-Γ p
... | in-Δ q = in-Δ (S q)

separateContextDenote : ∀ {Γ Δ K}
  → (E : TypeContextDenote Γ) → (F : TypeContextDenote Δ)
  → SeparateContextCase K Γ Δ
  → K-⟦ K ⟧
separateContextDenote E F (in-Γ p) = typeIdDenote p E
separateContextDenote E F (in-Δ q) = typeIdDenote q F

composeTypeContextDenote : ∀ {Γ Δ}
  → TypeContextDenote Γ
  → TypeContextDenote Δ
    ---------------------
  → TypeContextDenote (Γ ⨟ Δ)
composeTypeContextDenote E ∅ = E
composeTypeContextDenote E (F , V) = composeTypeContextDenote E F , V

separate-correct : ∀ {Γ Δ K}
  → (E : TypeContextDenote Γ) → (F : TypeContextDenote Δ)
  → (x : Γ ⨟ Δ ∋-T K)
    ------------
  → typeIdDenote x (composeTypeContextDenote E F)
  ≡ separateContextDenote E F (separateContext Γ Δ x)
separate-correct {Γ} {∅} E ∅ x               = refl
separate-correct {Γ} {Δ , K} E (F , V) Z     = refl
separate-correct {Γ} {Δ , K} E (F , V) (S x) with separateContext Γ Δ x in eq
... | in-Γ p = trans (separate-correct E F x) triv
               where
                 triv : separateContextDenote E F (separateContext Γ Δ x) ≡ typeIdDenote p E
                 triv rewrite eq = refl
... | in-Δ q = trans (separate-correct E F x) triv
               where
                 triv : separateContextDenote E F (separateContext Γ Δ x) ≡ typeIdDenote q F
                 triv rewrite eq = refl

lift : ∀ {Γ Δ}
  → (∀ {K} → Δ ∋-T K → Γ ⊩ K)
  → (∀ {K} → Γ ⨟ Δ ∋-T K → Γ ⊩ K)
lift {Γ} {Δ} σ p with separateContext Γ Δ p
... | in-Γ p = `` p
... | in-Δ q = σ q

data Instantiate (Γ : TypeContext) : TypeContext → Set where
  ∅   : Instantiate Γ ∅
  _,_ : ∀ {Δ} {K} → Instantiate Γ Δ → Γ ⊩ K → Instantiate Γ (Δ , K)

doInstantiate : ∀ {Γ Δ}
  → Instantiate Γ Δ
  → ∀ {K} → Δ ∋-T K → Γ ⊩ K
doInstantiate (σ , K) Z     = K
doInstantiate (σ , K) (S n) = doInstantiate σ n

substParameter : ∀ {Γ Δ}
  → (Instantiate Γ Δ)
  → (∀ {K} → Γ ⨟ Δ ⊩ K → Γ ⊩ K)
substParameter σ t = subst (lift (doInstantiate σ)) t

infix  4  _⊢_

infixl 7  _∙_
infix  9  `_∙_

data _⊢_ {Γ : TypeContext} (Δ : Context Γ) : Γ ⊩ ⋆ → Set where
  `_∙_  : ∀ {Γ' : TypeContext} {T}
        → (p : Δ ∋ [ Γ' & T ])
        → (σ : Instantiate Γ Γ')
          ------------
        → Δ ⊢ substParameter σ T
  _∙_ : ∀ {a b}
        → Δ ⊢ a ⇒ b
        → Δ ⊢ a
          ------------
        → Δ ⊢ b

data ContextDenote {Γ : TypeContext} (E : TypeContextDenote Γ) :
  Context Γ → Set₁ where
  ∅   : ContextDenote E ∅
  _,_ : ∀ {Γ' Δ T}
        → ContextDenote E Γ'
        → ((F : TypeContextDenote Δ) →
            T-⟦ T In composeTypeContextDenote E F ⟧)
          ------------------
        → ContextDenote E (Γ' , [ Δ & T ])

instantiationDenote : ∀ {Γ Δ}
  → TypeContextDenote Γ
  → Instantiate Γ Δ
    ------------------
  → TypeContextDenote Δ
instantiationDenote E ∅       = ∅
instantiationDenote E (σ , K) = (instantiationDenote E σ) , T-⟦ K In E ⟧

subst-S-≡ : ∀ {Γ Δ J K V}
          → (σ : Instantiate Γ Δ)
          → (p : Γ ⨟ Δ ∋-T K) → (q : Γ ⨟ (Δ , J) ∋-T K) → (q ≡ S p)
            ------------
          → substParameter (σ , V) (`` q) ≡ substParameter σ (`` p)
subst-S-≡ {Γ} {Δ} {J} σ p q eq
  rewrite eq with separateContext Γ Δ p
... | in-Γ p = refl
... | in-Δ q = refl

subst-≡-compose-id : ∀ {Γ Δ K}
  → (x : Γ ⨟ Δ ∋-T K) → (σ : Instantiate Γ Δ) → (E : TypeContextDenote Γ)
  → T-⟦ substParameter σ (`` x) In E ⟧
    ------------------
  ≡ typeIdDenote x
      (composeTypeContextDenote E (instantiationDenote E σ))
subst-≡-compose-id {Γ} {.∅} x ∅ E = refl
subst-≡-compose-id {Γ} {_ , _} Z (σ , _) E = refl
subst-≡-compose-id {Γ} {Δ , J} {K} (S x) (σ , V) E
  rewrite (subst-S-≡ {Γ} {Δ} {J} {K} {V} σ x (S x) refl) = subst-≡-compose-id x σ E

subst-≡-compose : ∀ {Γ Δ K}
  → (σ : Instantiate Γ Δ) → (T : Γ ⨟ Δ ⊩ K) → (E : TypeContextDenote Γ)
    ------------
  → T-⟦ substParameter σ T In E ⟧
  ≡ T-⟦ T In composeTypeContextDenote E (instantiationDenote E σ) ⟧
subst-≡-compose σ (`` x) E = subst-≡-compose-id x σ E
subst-≡-compose σ (t ∘ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl
subst-≡-compose σ (t ⇒ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl

termIdDenote : ∀ {Γ Γ' E} {Δ : Context Γ} {T}
  → (Δ ∋ [ Γ' & T ])
  → (σ : Instantiate Γ Γ')
  → ContextDenote E Δ → T-⟦ substParameter σ T In E ⟧
termIdDenote {Γ} {Γ'} {E} {Δ} {T} Z σ (M , F)
  rewrite (subst-≡-compose σ T E) = (F (instantiationDenote E σ))
termIdDenote (S p) σ (M , _) = termIdDenote p σ M

⟦_In_⟧ : ∀ {Γ E T} {Δ : Context Γ}
  → Δ ⊢ T
  → ContextDenote E Δ
  → T-⟦ T In E ⟧
⟦ ` x ∙ σ In E ⟧ = termIdDenote x σ E
⟦ a ∙ b In E ⟧   = ⟦ a In E ⟧ ⟦ b In E ⟧

--- test

length-T : TypeContext → ℕ
length-T ∅        =  zero
length-T (Γ , _)  =  suc (length-T Γ)

length : ∀ {Γ} → Context Γ → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count-T : ∀ {Γ} → {n : ℕ} → (p : n < length-T Γ) → Σ[ K ∈ Kind ] (Γ ∋-T K)
count-T {Γ , K} {zero} (s≤s z≤n)  =  ⟨ K , Z ⟩ 
count-T {Γ , _} {(suc n)} (s≤s p) with count-T p
...                                  | ⟨ K , n ⟩ = ⟨ K , S n ⟩

count : ∀ {Γ Δ} → {n : ℕ} → (p : n < length Δ) → Σ[ T ∈ Γ ⊩Δ ⋆ ] (Δ ∋ T)
count {Γ} {Δ , T} {zero} (s≤s z≤n)  =  ⟨ T , Z ⟩ 
count {Γ} {Δ , _} {(suc n)} (s≤s p) with count p
...                                    | ⟨ T , n ⟩ = ⟨ T , S n ⟩

T-#_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length-T Γ)}
      --------------------------------
    → Γ ⊩ proj₁ (count-T (toWitness n∈Γ))
T-#_ n {n∈Γ} = `` proj₂ (count-T (toWitness n∈Γ))

#-help : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Δ)}
      --------------------------------
    → Σ[ Γ' ∈ TypeContext ] (
      Σ[ B  ∈ Γ ⨟ Γ' ⊩ ⋆ ] (
        (σ : Instantiate Γ Γ')
      → Δ ⊢ substParameter σ B))
#-help n {n∈Γ} with count (toWitness n∈Γ)
...                 | ⟨ [ Δ & T ] , x ⟩ = ⟨ Δ , ⟨ T , `_∙_ x ⟩ ⟩

# : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Δ)}
      ------------
    → (σ : Instantiate Γ (proj₁ (#-help {Γ} {Δ} n {n∈Γ})))
    → Δ ⊢ substParameter σ (proj₁ (proj₂ (#-help {Γ} {Δ} n)))
# n = proj₂ (proj₂ (#-help n))

Γ : TypeContext
Γ = ∅ , ⋆
      , ⋆ ⇛ ⋆

Δ : Context Γ
Δ = ∅ , [ ∅ & T-# 1 ]
      , [ ∅ & T-# 1 ⇒ T-# 1 ]
      , [ ∅ , ⋆ & T-# 1 ∘ T-# 0 ]
      , [ ∅ , ⋆ & T-# 0 ⇒ T-# 1 ∘ T-# 0 ⇒ T-# 1 ∘ T-# 0 ]
      , [ ∅ , ⋆ & T-# 0 ⇒ T-# 1 ∘ T-# 0 ⇒ T-# 0 ]

T-⟦⟧ : TypeContextDenote Γ
T-⟦⟧ = ∅ , ℕ
         , List

⟦⟧ : ContextDenote T-⟦⟧ Δ
⟦⟧ = ∅ , (λ { ∅ → zero })
       , (λ { ∅ → suc })
       , (λ { (∅ , T) → [] })
       , (λ { (∅ , T) → _∷_ })
       , (λ { (∅ , T) → λ { x [] → x ; x (y ∷ l) → y} })

_ : ⟦ # 0 (∅ , T-# 1) ∙
        (# 3 ∅ ∙ # 4 ∅) ∙
        (# 1 (∅ , T-# 1) ∙ # 4 ∅ ∙ # 2 (∅ , T-# 1)) In ⟦⟧ ⟧ ≡ zero
_ = refl

extRight : ∀ {Γ A} → (K : Kind) → (Γ ⊩ A) → (Γ , K ⊩ A)
extRight _ (`` x)   = `` S x
extRight _ (t ∘ t₁) = extRight _ t ∘ extRight _ t₁
extRight _ (t ⇒ t₁) = extRight _ t ⇒ extRight _ t₁

ext-right-correct : ∀ {Γ A K}
  → (E : TypeContextDenote Γ) → (⟦K⟧ : K-⟦ K ⟧)
  → (t : Γ ⊩ A)
    ------------
  → T-⟦ t In E ⟧ ≡ T-⟦ extRight K t In E , ⟦K⟧ ⟧
ext-right-correct E ⟦K⟧ (`` x) = refl
ext-right-correct E ⟦K⟧ (t ∘ t₁)
 rewrite ext-right-correct E ⟦K⟧ t
 rewrite ext-right-correct E ⟦K⟧ t₁ = refl
ext-right-correct E ⟦K⟧ (t ⇒ t₁)
 rewrite ext-right-correct E ⟦K⟧ t
 rewrite ext-right-correct E ⟦K⟧ t₁ = refl

extsRight : ∀ {Γ A} → (Δ : TypeContext) → (Γ ⊩ A) → (Γ ⨟ Δ ⊩ A)
extsRight ∅ t       = t
extsRight (Δ , x) t = extRight x (extsRight Δ t)

exts-right-correct : ∀ {Γ Δ A}
  → (E : TypeContextDenote Γ) → (F : TypeContextDenote Δ)
  → (t : Γ ⊩ A)
    ------------
  → T-⟦ t In E ⟧ ≡ T-⟦ extsRight Δ t In composeTypeContextDenote E F ⟧
exts-right-correct E ∅ t                   = refl
exts-right-correct {Γ} {Δ , _} E (F , x) t =
  trans (exts-right-correct E F t)
        (ext-right-correct (composeTypeContextDenote E F) x (extsRight Δ t))

extTypeScheme : ∀ Γ Δ → {A : Kind} → (K : Kind) → (Γ ⨟ Δ ⊩ A) → ((Γ , K) ⨟ Δ ⊩ A)
extTypeScheme Γ Δ K (`` x) with separateContext Γ Δ x
... | in-Γ p = extsRight Δ (`` S p)
... | in-Δ Z = `` Z
extTypeScheme Γ .(_ , _) K (`` Z) | in-Δ (S_ {B = _} q) = `` Z
extTypeScheme Γ .(_ , B) K (`` (S x)) | in-Δ (S_ {B = B} q) = extRight B (extTypeScheme Γ _ K (`` x))
extTypeScheme _ _ K (t ∘ t₁) = extTypeScheme _ _ K t ∘ extTypeScheme _ _ K t₁
extTypeScheme _ _ K (t ⇒ t₁) = extTypeScheme _ _ K t ⇒ extTypeScheme _ _ K t₁

ext-scheme-correct : ∀ {Γ Δ K A}
  → (E : TypeContextDenote Γ) → (F : TypeContextDenote Δ) → (⟦K⟧ : K-⟦ K ⟧)
  → (t : Γ ⨟ Δ ⊩ A)
    ------------
  → T-⟦ t In composeTypeContextDenote E F ⟧ ≡
    T-⟦ extTypeScheme Γ Δ K t In composeTypeContextDenote (E , ⟦K⟧) F ⟧
ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (`` x) with separateContext Γ Δ x in eq
... | in-Γ p = trans (trans (separate-correct E F x) triv)
                     (exts-right-correct (E , ⟦K⟧) F (`` S p))
               where
                 triv : separateContextDenote E F (separateContext Γ Δ x) ≡ typeIdDenote p E
                 triv rewrite eq = refl
ext-scheme-correct {Γ} {Δ , y} E (F , V) ⟦K⟧ (`` x) | in-Δ Z =
  trans (separate-correct E (F , V) x) triv
  where
    triv : separateContextDenote E (F , V) (separateContext Γ (Δ , y) x) ≡ typeIdDenote Z (F , V)
    triv rewrite eq = refl
ext-scheme-correct {Γ} {Δ , y} E (F , V) ⟦K⟧ (`` (S x)) | in-Δ (S q) =
  trans (ext-scheme-correct E F ⟦K⟧ (`` x))
        (ext-right-correct (composeTypeContextDenote (E , ⟦K⟧) F) V
                              (extTypeScheme Γ _ _ (`` x)) )
ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (a ∘ b)
  rewrite ext-scheme-correct E F ⟦K⟧ a
  rewrite ext-scheme-correct E F ⟦K⟧ b = refl
ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (a ⇒ b)
  rewrite ext-scheme-correct E F ⟦K⟧ a
  rewrite ext-scheme-correct E F ⟦K⟧ b = refl

extContext : ∀ {Γ} → (K : Kind) → Context Γ → Context (Γ , K)
extContext _ ∅                    = ∅
extContext {Γ} K (Δ , [ Γ' & B ]) = extContext K Δ , [ Γ' & extTypeScheme Γ Γ' K B ]

extTerm : ∀ {Γ Δ B} → (A : Γ ⊩Δ ⋆) → (Δ ⊢ B) → (Δ , A ⊢ B)
extTerm A (` p ∙ σ) = ` S p ∙ σ
extTerm A (t ∙ t₁)  = extTerm A t ∙ extTerm A t₁

extContextDenote : ∀ {Γ} → {Δ : Context Γ}
  → {T-⟦⟧ : TypeContextDenote Γ}
  → (K : Kind) → (⟦K⟧ : K-⟦ K ⟧)
  → (⟦⟧ : ContextDenote T-⟦⟧ Δ)
    ------------
  → ContextDenote (T-⟦⟧ , ⟦K⟧) (extContext K Δ)
extContextDenote {Γ} {∅} {T-⟦⟧} K ⟦K⟧ ⟦⟧ = ∅
extContextDenote {Γ} {Δ , [ Γ' & T ]} {T-⟦⟧} K ⟦K⟧ (⟦⟧ , x) =
  extContextDenote K ⟦K⟧ ⟦⟧ , λ { F → change (ext-scheme-correct T-⟦⟧ F ⟦K⟧ T) (x F) }
  where
    change : ∀ {A B : Set} → (A ≡ B) → A → B
    change refl a = a

car-cons-a-nil≡a : ∀ (A : Set) (a : A)
                 → let ⟦⟧' = (extContextDenote ⋆ A ⟦⟧) , (λ { ∅ → a }) in
                   ⟦ # 1 (∅ , T-# 0) ∙ # 0 ∅ ∙
                       (# 2 (∅ , T-# 0) ∙ # 0 ∅ ∙ # 3 (∅ , T-# 0)) In ⟦⟧' ⟧
                 ≡ ⟦ # 0 ∅ In ⟦⟧' ⟧

car-cons-a-nil≡a A a = refl
