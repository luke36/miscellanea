--- encode the type system of the assertion language in VST-IDE

module plfa.part2.Poly where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Agda.Builtin.Bool using (true; false)

Id : Set
Id = String

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

infixl 5  _,_⦂⦂_

data KindContext : Set where
  ∅      : KindContext
  _,_⦂⦂_ : KindContext → Id → Kind → KindContext

infix  4  _∋_⦂⦂_

data _∋_⦂⦂_ : KindContext → Id → Kind → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂⦂ A ∋ x ⦂⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂⦂ A
      ------------------
    → Γ , y ⦂⦂ B ∋ x ⦂⦂ A

infixr 7  _⇒_
infixl 8  _∘_
infix  9  ``_

infix  4  _⊩_

data _⊩_ (Γ : KindContext) : Kind → Set where
  ``_  :  ∀ {k} → (x : Id) → {Γ ∋ x ⦂⦂ k} → Γ ⊩ k
  _∘_  :  ∀ {j k} → Γ ⊩ j ⇛ k → Γ ⊩ j → Γ ⊩ k
  _⇒_  :  Γ ⊩ ⋆ → Γ ⊩ ⋆ → Γ ⊩ ⋆

infixl 5  _,_

data KindContextDenote : KindContext → Set₁ where
  ∅   : KindContextDenote ∅
  _,_ : ∀ {Γ x k}
      → KindContextDenote Γ
      → K-⟦ k ⟧
      ------------------
      → KindContextDenote (Γ , x ⦂⦂ k)

typeIdDenote : ∀ {Γ : KindContext} {k} → (x : Id) → (Γ ∋ x ⦂⦂ k) → KindContextDenote Γ → K-⟦ k ⟧
typeIdDenote {Γ , .x ⦂⦂ .k} {k} x Z (E , K)     = K
typeIdDenote {Γ , _ ⦂⦂ _} {k} y (S p n) (E , _) = typeIdDenote y n E

T-⟦_In_⟧ : ∀ {Γ : KindContext} {k} → Γ ⊩ k → KindContextDenote Γ → K-⟦ k ⟧
T-⟦ ``_ x {proof} In E ⟧ = typeIdDenote x proof E
T-⟦ a ∘ b In E ⟧         = T-⟦ a In E ⟧ T-⟦ b In E ⟧
T-⟦ a ⇒ b In E ⟧         = T-⟦ a In E ⟧ → T-⟦ b In E ⟧

infix  5  _⨟_

_⨟_ : KindContext → KindContext → KindContext
Γ ⨟ ∅            = Γ
Γ ⨟ (Δ , x ⦂⦂ A) = (Γ ⨟ Δ) , x ⦂⦂ A

--- type scheme
infix  4  _⊩Δ_

data _⊩Δ_ (Γ : KindContext) (K : Kind) : Set where
  [_,_] : (Δ : KindContext) → Γ ⨟ Δ ⊩ K → Γ ⊩Δ K

infixl 5  _,_⦂_

data TypeContext (Γ : KindContext) : Set where
  ∅      : TypeContext Γ
  _,_⦂_  : TypeContext Γ → Id → Γ ⊩Δ ⋆ → TypeContext Γ

infixl 4  _∋_⦂_

data _∋_⦂_ {Γ : KindContext} : TypeContext Γ → Id → Γ ⊩Δ ⋆ → Set where

  Z : ∀ {Δ x A}
      ------------------
    → Δ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Δ x y A B}
    → x ≢ y
    → Δ ∋ x ⦂ A
      ------------------
    → Δ , y ⦂ B ∋ x ⦂ A

subst : ∀ {Γ Δ}
  → (∀ {K} → (x : Id) → (Γ ∋ x ⦂⦂ K) → Δ ⊩ K)
  → (∀ {K} → Γ ⊩ K → Δ ⊩ K)
subst σ (``_ x {proof}) = σ x proof
subst σ (t ∘ s) = (subst σ t) ∘ (subst σ s)
subst σ (s ⇒ t) = (subst σ s) ⇒ (subst σ t)

data SeparateContextCase {x} {K} (Γ Δ : KindContext)
       (In : Γ ⨟ Δ ∋ x ⦂⦂ K) : Set where
  in-Γ : Γ ∋ x ⦂⦂ K → SeparateContextCase Γ Δ In
  in-Δ : Δ ∋ x ⦂⦂ K → SeparateContextCase Γ Δ In

separateContext : ∀ {x} {K} (Γ Δ : KindContext)
  → (In : Γ ⨟ Δ ∋ x ⦂⦂ K) → SeparateContextCase Γ Δ In
separateContext Γ ∅ p            = in-Γ p
separateContext Γ (Δ , x ⦂⦂ K) Z = in-Δ Z
separateContext Γ (Δ , x ⦂⦂ K) (S y p) with separateContext Γ Δ p
... | in-Γ p = in-Γ p
... | in-Δ q = in-Δ (S y q)

lift : ∀ {Γ Δ}
  → (∀ {K} → (x : Id) → Δ ∋ x ⦂⦂ K → Γ ⊩ K)
  → (∀ {K} → (x : Id) → Γ ⨟ Δ ∋ x ⦂⦂ K → Γ ⊩ K)
lift {Γ} {Δ} σ x p with separateContext Γ Δ p
... | in-Γ p = ``_ x {p}
... | in-Δ q = σ x q

data Instantiate (Γ : KindContext) : KindContext → Set where
  ∅     : Instantiate Γ ∅
  _,_ : ∀ {Δ} {K} {x} → Instantiate Γ Δ → Γ ⊩ K → Instantiate Γ (Δ , x ⦂⦂ K)

doInstantiate : ∀ {Γ Δ}
  → Instantiate Γ Δ
  → ∀ {K} → (x : Id) → Δ ∋ x ⦂⦂ K → Γ ⊩ K
doInstantiate (σ , K) x Z       = K
doInstantiate (σ , K) x (S y p) = doInstantiate σ x p

substParameter : ∀ {Γ Δ}
  → (Instantiate Γ Δ)
  → (∀ {K} → Γ ⨟ Δ ⊩ K → Γ ⊩ K)
substParameter σ t = subst (lift (doInstantiate σ)) t

infix  4  _⊢_

infixr 7  _∙_
infix  9  `_

data _⊢_ {Γ : KindContext} (Δ : TypeContext Γ) : Γ ⊩ ⋆ → Set where
  `_  : ∀ {Γ' : KindContext} {T}
        → (x : Id) → {p : Δ ∋ x ⦂ [ Γ' , T ]}
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
  _,_ : ∀ {Γ' Δ x T}
        → TypeContextDenote E Γ'
        → ((F : KindContextDenote Δ) →
            T-⟦ T In composeKindContextDenote E F ⟧)
        ------------------
        → TypeContextDenote E (Γ' , x ⦂ [ Δ , T ])

instantiationDenoteType : ∀ {Γ K}
  → KindContextDenote Γ
  → Γ ⊩ K
  ------------
  → K-⟦ K ⟧
instantiationDenoteType E (``_ x {p}) = typeIdDenote x p E
instantiationDenoteType E (s ∘ t) = (instantiationDenoteType E s) (instantiationDenoteType E t)
instantiationDenoteType E (s ⇒ t) = (instantiationDenoteType E s) → (instantiationDenoteType E t)

instantiationDenote : ∀ {Γ Δ}
  → KindContextDenote Γ
  → Instantiate Γ Δ
  ------------------
  → KindContextDenote Δ
instantiationDenote E ∅       = ∅
instantiationDenote E (σ , K) = (instantiationDenote E σ) , instantiationDenoteType E K

T-⟦⟧-≡-instantiate : ∀ {Γ K} (E : KindContextDenote Γ) (T : Γ ⊩ K) →
  T-⟦ T In E ⟧ ≡ instantiationDenoteType E T
T-⟦⟧-≡-instantiate E (`` x) = refl
T-⟦⟧-≡-instantiate E (s ∘ t)
  rewrite (T-⟦⟧-≡-instantiate E s) rewrite (T-⟦⟧-≡-instantiate E t) = refl
T-⟦⟧-≡-instantiate E (s ⇒ t)
  rewrite (T-⟦⟧-≡-instantiate E s) rewrite (T-⟦⟧-≡-instantiate E t) = refl

subst-≢ : ∀ {Γ Δ J K V}
          → (σ : Instantiate Γ Δ)
          → (x y : Id) → (neq : x ≢ y)
          → (p : Γ ⨟ Δ ∋ x ⦂⦂ K) → (q : Γ ⨟ (Δ , y ⦂⦂ J) ∋ x ⦂⦂ K) → (q ≡ S neq p)
          ------------
          → substParameter (σ , V) (``_ x {q}) ≡ substParameter σ (``_ x {p})
subst-≢ {Γ} {Δ} {J} σ x y x≢y p neq eq
  rewrite eq with separateContext Γ Δ p
... | in-Γ p = refl
... | in-Δ q = refl

subst-≡-compose-id : ∀ {Γ Δ K} → (σ : Instantiate Γ Δ) → (E : KindContextDenote Γ)
  → (x : Id) → (p : Γ ⨟ Δ ∋ x ⦂⦂ K)
  → T-⟦ substParameter σ (``_ x {p}) In E ⟧
  ≡ typeIdDenote x p
      (composeKindContextDenote E (instantiationDenote E σ))
subst-≡-compose-id {Γ} {.∅} ∅ E x p = refl
subst-≡-compose-id {Γ} {.(_ , x ⦂⦂ _)} (σ , T) E x Z = T-⟦⟧-≡-instantiate E T
subst-≡-compose-id {Γ} {Δ , w ⦂⦂ J} {K} (σ , z) E x (S y p)
  rewrite subst-≢ {Γ} {Δ} {J} {K} {z} σ x w y p (S y p) refl = subst-≡-compose-id σ E x p

subst-≡-compose : ∀ {Γ Δ K}
  → (σ : Instantiate Γ Δ) → (T : Γ ⨟ Δ ⊩ K) → (E : KindContextDenote Γ)
  ------------
  → T-⟦ substParameter σ T In E ⟧
  ≡ T-⟦ T In composeKindContextDenote E (instantiationDenote E σ) ⟧
subst-≡-compose σ (``_ x {p}) E = subst-≡-compose-id σ E x p
subst-≡-compose σ (t ∘ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl
subst-≡-compose σ (t ⇒ s) E
  rewrite (subst-≡-compose σ t E) rewrite (subst-≡-compose σ s E) = refl

termIdDenote : ∀ {Γ Γ' E} {Δ : TypeContext Γ} {T}
  → (x : Id) → (Δ ∋ x ⦂ [ Γ' , T ])
  → (σ : Instantiate Γ Γ')
  → TypeContextDenote E Δ → T-⟦ substParameter σ T In E ⟧
termIdDenote {Γ} {Γ'} {E} {Δ} {T} x Z σ (M , F)
  rewrite (subst-≡-compose σ T E) = (F (instantiationDenote E σ))
termIdDenote x (S y p) σ (M , _) = termIdDenote x p σ M

⟦_In_⟧ : ∀ {Γ E T} {Δ : TypeContext Γ}
  → Δ ⊢ T
  → TypeContextDenote E Δ
  → T-⟦ T In E ⟧
⟦ `_ x {p} σ In E ⟧ = termIdDenote x p σ E
⟦ a ∙ b In E ⟧      = ⟦ a In E ⟧ ⟦ b In E ⟧

