{-# OPTIONS --without-K #-}
-- {-# OPTIONS --cumulativity #-}

module hott where

open import Data.Sum using () renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr)
open import Data.Empty using () renaming (⊥ to 𝟘 ; ⊥-elim to 𝟘-elim)
open import Relation.Nullary using (¬_)
open import Agda.Primitive using (Level ; _⊔_ ; lsuc ; lzero) renaming (Set to U)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma using (Σ ; _,_) renaming (fst to pr₁ ; snd to pr₂)

_×_ : {a b : Level} (A : U a) (B : U b) → U (a ⊔ b)
A × B = Σ A (λ _ → B)

_∘_ : {a b c : Level} {A : U a} {B : U b} {C : U c}
    → (f : B → C) → (g : A → B) → (A → C)
(f ∘ g) x = f (g x)

_~_ : {a b : Level} {A : U a} {P : A → U b} → (f g : (x : A) → P x) → U (a ⊔ b)
f ~ g = ∀ x → f x ≡ g x

id : {a : Level} {A : U a} → A → A
id x = x

transp : {a b : Level} {A : U a} {x y : A} (P : A → U b) (p : x ≡ y) → (P x → P y)
transp P refl = id

_·_ : {a : Level} {A : U a} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl · refl = refl

_⁻¹ : {a : Level} {A : U a} {a b : A} → a ≡ b → b ≡ a
refl ⁻¹ = refl

·-refl-r : {a : Level} {A : U a} {a b : A} (p : a ≡ b) → p ≡ p · refl
·-refl-r refl = refl

·-refl-l : {a : Level} {A : U a} {a b : A} (p : a ≡ b) → p ≡ refl · p
·-refl-l refl = refl

transp-→ : {a b c : Level} {X : U a} {x y : X} {A : X → U b} {B : X → U c}
           (p : x ≡ y) (f : A x → B x)
         → transp (λ x → (A x → B x)) p f ≡ λ x → transp B p (f (transp A (p ⁻¹) x))
transp-→ refl f = refl

transp-≡-1 : {a : Level} {A : U a} {a x y : A} (p : x ≡ y) (q : a ≡ x)
           → transp _ p q ≡ q · p
transp-≡-1 refl q = ·-refl-r q

·-⁻¹-refl : {a : Level} {A : U a} {a b : A} (p : a ≡ b) → (p ⁻¹) · p ≡ refl
·-⁻¹-refl refl = refl

≡-·-l : {a : Level} {A : U a} {a b c : A} {p q : b ≡ c} (r : a ≡ b)
      → p ≡ q → r · p ≡ r · q
≡-·-l r refl = refl

·-cong : {a : Level} {A : U a} {a b c : A} {p q : a ≡ b} {r s : b ≡ c}
       → p ≡ q → r ≡ s → p · r ≡ q · s
·-cong refl refl = refl

·-assoc : {a : Level} {A : U a} {a b c d : A} (p : a ≡ b) (q : b ≡ c)(r : c ≡ d)
        → p · (q · r) ≡ (p · q) · r
·-assoc refl refl refl = refl

·-cancel-l : {a : Level} {A : U a} {a b c : A} {p q : b ≡ c} {r : a ≡ b}
           → r · p ≡ r · q → p ≡ q
·-cancel-l {l}{A}{a}{b}{c}{p}{q}{r} s =
  ·-refl-l p · (·-cong ((·-⁻¹-refl r) ⁻¹) refl · (((·-assoc _ _ _) ⁻¹) · (·-cong refl s · ((·-assoc _ _ _) · (·-cong (·-⁻¹-refl r) refl · ((·-refl-l q) ⁻¹))))))

transp-⁻¹ : {a b : Level} {A : U a} {x y : A} {P : A → U b} (p : x ≡ y)
          → (transp P (p ⁻¹)) ∘ (transp P p) ≡ id
transp-⁻¹ refl = refl

⁻¹-⁻¹-id : {a : Level} {A : U a} {a b : A} (p : a ≡ b) → (p ⁻¹) ⁻¹ ≡ p
⁻¹-⁻¹-id refl = refl

~-refl : {a b : Level} {A : U a} {P : A → U b} (f : (x : A) → P x) → f ~ f
~-refl f = λ x → refl

~-assoc : {a b : Level} {A : U a} {P : A → U b} {f g h : (x : A) → P x} → f ~ g → g ~ h → f ~ h
~-assoc f~g g~h = λ x → f~g x · g~h x

happly : {a b : Level} {A : U a} {P : A → U b} {f g : (x : A) → P x} → f ≡ g → f ~ g
happly refl = ~-refl _

transp-⁻¹' : {a b : Level} {A : U a} {x y : A} {P : A → U b} (p : x ≡ y)
           → (transp P p) ∘ (transp P (p ⁻¹)) ≡ id
transp-⁻¹' p = transp (λ q → (transp _ q ∘ transp _ (p ⁻¹)) ≡ id) (⁻¹-⁻¹-id p) (transp-⁻¹ (p ⁻¹))

isequiv : {a b : Level} {A : U a} {B : U b} → (f : A → B) → U (a ⊔ b)
isequiv f = Σ _ (λ g → (f ∘ g) ~ id) × Σ _ (λ h → (h ∘ f) ~ id)

qinv : {a b : Level} {A : U a} {B : U b} → (f : A → B) → U (a ⊔ b)
qinv f = Σ _ (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

_≃_ : {a b : Level} (A : U a) (B : U b) → U (a ⊔ b)
A ≃ B = Σ (A → B) (λ f → isequiv f)

≃-refl : {a : Level} (A : U a) → A ≃ A
≃-refl A = id , (id , (λ x → refl)) , id , (λ x → refl)

qinv→isequiv : {a b : Level} {A : U a} {B : U b} {f : A → B}
             → qinv f → isequiv f
qinv→isequiv (g , (inv₁ , inv₂)) = (g , inv₁) , (g , inv₂)

ap : {a b : Level} {A : U a} {B : U b} {x y : A} (f : A → B)
   → x ≡ y → f x ≡ f y
ap f refl = refl

apd : {a b : Level} {A : U a} {x y : A} {P : A → U b} (f : ∀ (x : A) → P x)
    → ((p : x ≡ y) → transp _ p (f x) ≡ f y)
apd f refl = refl

∘-~-cong : {a b c : Level} {A : U a} {B : U b} {C : U c} {f g : B → C} {h i : A → B}
         → f ~ g → h ~ i → (f ∘ h) ~ (g ∘ i)
∘-~-cong {a}{b}{c}{A}{B}{C}{f} f~g h~i = λ x → ap f (h~i x) · f~g _

isequiv→qinv : {a b : Level} {A : U a} {B : U b} {f : A → B}
             → isequiv f → qinv f
isequiv→qinv {a}{b}{A}{B} {f} ((g , invg) , (h , invh)) =
  (h ∘ (f ∘ g)) ,
  (~-assoc (∘-~-cong (~-refl f) (∘-~-cong invh (~-refl g))) invg ,
   ~-assoc (∘-~-cong (∘-~-cong (~-refl h) invg) (~-refl f)) invh)

≃-sym : {a b : Level} {A : U a} {B : U b} → A ≃ B → B ≃ A
≃-sym (f , e) with isequiv→qinv e
...              | (g , h , h') = g , (qinv→isequiv (f , h' , h))

≃-assoc : {a b c : Level} {A : U a} {B : U b} {C : U c} → A ≃ B → B ≃ C → A ≃ C
≃-assoc (f₁ , e₁) (f₂ , e₂) with isequiv→qinv e₁ | isequiv→qinv e₂
...                            | (g₁ , h₁ , h₁') | (g₂ , h₂ , h₂') =
  (f₂ ∘ f₁) , qinv→isequiv (g₁ ∘ g₂ , ~-assoc ((∘-~-cong (~-refl f₂) (∘-~-cong h₁ (~-refl g₂)))) h₂
                                    , ~-assoc ((∘-~-cong (~-refl g₁) (∘-~-cong h₂' (~-refl f₁)))) h₁')

≡-Σ : {a b : Level} {A : U a} {P : A → U b} (w w' : Σ A P)
    → (w ≡ w') ≃ Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w')
≡-Σ w w' = f w w' , qinv→isequiv (g w w' , (λ p → inv₂ w w' p) , λ p → inv₁ w w' p)
  where
    f : {a b : Level} {A : U a} {P : A → U b} (w w' : Σ A P)
      → (w ≡ w') → Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w')
    f w w refl = refl , refl
    g : {a b : Level} {A : U a} {P : A → U b} (w w' : Σ A P)
      → Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w') → (w ≡ w')
    g (w₁ , w₂) (w₁ , w₂) (refl , refl) = refl
    inv₁ : {a b : Level} {A : U a} {P : A → U b} (w w' : Σ A P) → (p : w ≡ w')
         → g w w' (f w w' p) ≡ p
    inv₁ w w refl = refl
    inv₂ : {a b : Level} {A : U a} {P : A → U b} (w w' : Σ A P)
         → (p : Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w'))
         → f w w' (g w w' p) ≡ p
    inv₂ w w (refl , refl) = refl

pair-≡ : {a b : Level} {A : U a} {P : A → U b} {w w' : Σ A P}
       → Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w') → (w ≡ w')
pair-≡{a}{b}{A}{P}{w}{w'} = pr₁ (isequiv→qinv (pr₂ (≡-Σ w w')))

pair-≡-elim : {a b : Level} {A : U a} {P : A → U b} {w w' : Σ A P}
            → (w ≡ w') → Σ (pr₁ w ≡ pr₁ w') (λ p → transp _ p (pr₂ w) ≡ pr₂ w')
pair-≡-elim = pr₁ (≡-Σ _ _)

pair-≡-inv₂ : {a b : Level} {A : U a} {P : A → U b} {w w' : Σ A P}
            → (p : w ≡ w') → pair-≡ (pair-≡-elim p) ≡ p
pair-≡-inv₂ p = pr₂ (pr₂ (isequiv→qinv (pr₂ (≡-Σ _ _)))) p

transp-is-equiv : {a b : Level} {A : U a} {x y : A} (P : A → U b) (p : x ≡ y)
                → isequiv (transp P p)
transp-is-equiv P p = qinv→isequiv (transp P (p ⁻¹) , happly (transp-⁻¹' p) , happly (transp-⁻¹ p))

idtoeqv : {a : Level} {A B : U a} → A ≡ B → A ≃ B
idtoeqv A≡B = transp id A≡B , transp-is-equiv id A≡B

idtoeqv-refl : {a : Level} {A : U a} → idtoeqv refl ≡ ≃-refl A
idtoeqv-refl = refl

postulate
  function-extensionality : {a b : Level} {A : U a} {P : A → U b} {f g : (x : A) → P x} → isequiv (happly{a}{b}{A}{P}{f}{g})
  univalence : {a : Level} {A B : U a} → isequiv (idtoeqv {a}{A}{B})

funext : {a b : Level} {A : U a} {P : A → U b} {f g : (x : A) → P x} → f ~ g → f ≡ g
funext f~g = pr₁ (isequiv→qinv function-extensionality) f~g

funext-happly-id : {a b : Level} {A : U a} {P : A → U b} {f g : (x : A) → P x} (p : f ≡ g)
                 → funext (happly p) ≡ p
funext-happly-id p = pr₂ (pr₂ (isequiv→qinv function-extensionality)) p

ua : {a : Level} → {A B : U a} → A ≃ B → A ≡ B
ua = pr₁ (isequiv→qinv univalence)

idtoeqv-ua-id : {a : Level} {A B : U a} (e : A ≃ B) → idtoeqv (ua e) ≡ e
idtoeqv-ua-id e = pr₁ (pr₂ (isequiv→qinv univalence)) e

univalence' : {a : Level} → {A B : U a} → (A ≡ B) ≃ (A ≃ B)
univalence' = idtoeqv , univalence

ua-comp-lem : {a : Level} {A B : U a} (p : A ≡ B) (x : A) → transp id p x ≡ pr₁ (idtoeqv p) x
ua-comp-lem refl x = refl

ua-comp : {a : Level} {A B : U a} (e : A ≃ B) (x : A) → transp id (ua e) x ≡ pr₁ e x
ua-comp e x = ua-comp-lem (ua e) x · ap (λ e → pr₁ e x) (idtoeqv-ua-id e)

isSet : {a : Level} (A : U a) → U a
isSet A = (x y : A) → (p q : x ≡ y) → p ≡ q

isProp : {a : Level} (A : U a) → U a
isProp A = (x y : A) → x ≡ y

is-set-Σ : {a b : Level} {A : U a} {B : A → U b} → isSet A → (∀ a → isSet (B a))
         → isSet (Σ A B)
is-set-Σ a f = λ u v p q → ((pair-≡-inv₂ p) ⁻¹) · (ap pair-≡ (pair-≡ (a _ _ _ _ , f _ _ _ _ _)) · pair-≡-inv₂ q)

is-set-Π : {a b : Level} {A : U a} {B : A → U b} → (∀ a → isSet (B a)) → isSet ((a : A) → B a)
is-set-Π set-B = λ f g p q → ((funext-happly-id p) ⁻¹) · (ap funext (funext λ x → set-B _ _ _ _ _) · funext-happly-id q)

is1-type : {a : Level} (A : U a) → U a
is1-type A = (x y : A) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

set-is-1-type : {a : Level} {A : U a} → isSet A → is1-type A
set-is-1-type f x y p = λ q r s → ·-cancel-l (factor p q r · ((factor p q s) ⁻¹))
  where
    g : (q : x ≡ y) → p ≡ q
    g q = f x y p q
    factor : (q q' : x ≡ y) (r : q ≡ q') → (g q) · r ≡ g q'
    factor q q' r = ((transp-≡-1 r (g q)) ⁻¹) · apd g r

data 𝟙 : U where
  ⋆ : 𝟙

data 𝟚 : U where
  𝟎 : 𝟚
  𝟏 : 𝟚

swap : 𝟚 → 𝟚
swap 𝟎 = 𝟏
swap 𝟏 = 𝟎

swap-swap-id : (swap ∘ swap) ~ id
swap-swap-id 𝟎 = refl
swap-swap-id 𝟏 = refl

swap-is-eqv : isequiv swap
swap-is-eqv = qinv→isequiv (swap , swap-swap-id , swap-swap-id)

swap-equiv : 𝟚 ≃ 𝟚
swap-equiv = (swap , swap-is-eqv)

swap-path : 𝟚 ≡ 𝟚
swap-path = ua swap-equiv

¬𝟎≡𝟏 : ¬ 𝟎 ≡ 𝟏
¬𝟎≡𝟏 ()

¬𝟚≡𝟚-prop : ¬ isProp (𝟚 ≡ 𝟚)
¬𝟚≡𝟚-prop prop = ¬𝟎≡𝟏 (ap (λ f → f 𝟎) abs)
  where
    abs = ap (pr₁ ∘ idtoeqv) (prop refl swap-path) · ap pr₁ (idtoeqv-ua-id swap-equiv)

U-is-not-set : ¬ isSet(U)
U-is-not-set Set-is-set = ¬𝟚≡𝟚-prop (Set-is-set _ _)

swap-¬≡ : (b : 𝟚) → ¬ swap b ≡ b
swap-¬≡ 𝟎 ()
swap-¬≡ 𝟏 ()

¬¬𝟚-single : (u v : ¬ ¬ 𝟚) → u ≡ v
¬¬𝟚-single u v = funext λ x → 𝟘-elim (u x)

∞-lem-unsound : ¬ ∀ (A : U) → ¬ ¬ A → A
∞-lem-unsound f = swap-¬≡ (f 𝟚 u) ((eq₄ _ ⁻¹) · (((eq₂ · ap (λ u → transp id swap-path (f 𝟚 u)) eq₃) ⁻¹) · eq₁))
  where
    u : ¬ ¬ 𝟚
    u = λ x → 𝟘-elim (x 𝟎)
    eq₁ : transp (λ A → ¬ ¬ A → A) swap-path (f 𝟚) u ≡ f 𝟚 u
    eq₁ = happly (apd f swap-path) u
    eq₂ : transp (λ A → ¬ ¬ A → A) swap-path (f 𝟚) u
        ≡ transp id swap-path (f 𝟚 (transp (λ A → ¬ ¬ A) (swap-path ⁻¹) u))
    eq₂ = happly (transp-→ swap-path (f 𝟚)) u
    eq₃ : transp (λ A → ¬ ¬ A) (swap-path ⁻¹) u ≡ u
    eq₃ = ¬¬𝟚-single _ _
    eq₄ : (b : 𝟚) → transp id swap-path b ≡ swap b
    eq₄ b = ua-comp swap-equiv b

𝟙-is-prop : isProp 𝟙
𝟙-is-prop ⋆ ⋆ = refl

𝟘-is-prop : isProp 𝟘
𝟘-is-prop x = 𝟘-elim x

𝟚-is-set : isSet 𝟚
𝟚-is-set = λ { 𝟎 𝟎 refl refl → refl ; 𝟏 𝟏 refl refl → refl }

is-prop-Π : {a b : Level} {A : U a} {B : A → U b}
          → (∀ x → isProp (B x)) → isProp (∀ x → B x)
is-prop-Π p = λ f g → funext λ x → p x (f x) (g x)

inhabited-prop→≃𝟙 : {a : Level} {P : U a} → isProp P × P → P ≃ 𝟙
inhabited-prop→≃𝟙 (isprop , x) = (λ _ → ⋆) , qinv→isequiv ((λ _ → x) , (λ _ → 𝟙-is-prop _ _) , λ _ → isprop _ _)

prop-leqv→eqv : {a b : Level} {P : U a} {Q : U b} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≃ Q
prop-leqv→eqv P-prop Q-prop f g = f , qinv→isequiv (g , (λ _ → Q-prop _ _) , λ _ → P-prop _ _)

prop-is-set : {a : Level} {A : U a} → isProp A → isSet A
prop-is-set f x = λ y p q → ·-cancel-l (factor x y p · ((factor x y q) ⁻¹))
  where
    g : (y : _) → x ≡ y
    g y = f x y
    factor : (y y' : _) (p : y ≡ y') → (g y) · p ≡ g y'
    factor y y' p = ((transp-≡-1 p (g y)) ⁻¹) · apd g p

is-set-≃ : {a b : Level} {A : U a} {B : U b} → isSet A → isSet B → isSet (A ≃ B)
is-set-≃ a b = is-set-Σ (is-set-Π λ _ → b) λ _ → is-set-Σ (is-set-Σ (is-set-Π λ _ → a) λ _ → is-set-Π λ _ → prop-is-set (b _ _)) λ _ → is-set-Σ (is-set-Π λ _ → a) λ _ → is-set-Π λ _ → prop-is-set (a _ _)

isProp-is-prop : {a : Level} (A : U a) → isProp (isProp (A))
isProp-is-prop A = λ f g → funext λ x → funext λ y → prop-is-set f x y (f x y) (g x y)

isSet-is-prop : {a : Level} (A : U a) → isProp (isSet (A))
isSet-is-prop A = λ f g → funext λ x → funext λ y → funext λ p → funext λ q → set-is-1-type g _ _ _ _ _ _

subset-proper : {a b : Level} {A : U a} {P : A → U b} {u v : Σ A P}
                → (∀ a → isProp (P a)) → pr₁ u ≡ pr₁ v → u ≡ v
subset-proper{a}{b}{A}{P}{u}{v} is-prop p = pair-≡ (p , is-prop (pr₁ v) _ _)

Set_ : (a : Level) → U (lsuc a)
Set a = Σ (U a) (λ A → isSet(A))

Prop_ : (a : Level) → U (lsuc a)
Prop a = Σ (U a) (λ A → isProp(A))

record Lift {a ℓ} (A : U a) : U (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

lift-≃ : {a ℓ : Level} (A : U a) → Lift{a}{ℓ} A ≃ A
lift-≃ A = (λ { (lift x) → x }) , qinv→isequiv ((λ x → lift x) , (λ x → refl) , λ { (lift x) → refl })

≡-lift : {a ℓ : Level} {A : U a} (x y : Lift{a}{ℓ}A) → (x ≡ y) ≃ (lower x ≡ lower y)
≡-lift{a}{ℓ}{A} x y = f x y , qinv→isequiv (g x y , h x y , h' x y)
  where
    f : (x y : Lift{a}{ℓ}A) → (x ≡ y) → (lower x ≡ lower y)
    f x x refl = refl
    g : (x y : Lift{a}{ℓ}A) → (lower x ≡ lower y) → (x ≡ y)
    g x x refl = refl
    h : (x y : Lift{a}{ℓ}A) → (p : lower x ≡ lower y) → f x y (g x y p) ≡ p
    h x x refl = refl
    h' : (x y : Lift{a}{ℓ}A) → (p : x ≡ y) → g x y (f x y p) ≡ p
    h' x x refl = refl

lift-≡-elim : {a ℓ : Level} {A : U a} {x y : Lift{a}{ℓ}A} → (x ≡ y) → (lower x ≡ lower y)
lift-≡-elim{a}{ℓ}{A}{x}{y} = pr₁ (≡-lift _ _)

lift-≡-intro : {a ℓ : Level} {A : U a} {x y : Lift{a}{ℓ}A} → (lower x ≡ lower y) → (x ≡ y)
lift-≡-intro{a}{ℓ}{A}{x}{y} = pr₁ (isequiv→qinv (pr₂ (≡-lift x y)))

lift-≡-inv₂ : {a ℓ : Level} {A : U a} {x y : Lift{a}{ℓ}A} → (p : x ≡ y) → lift-≡-intro (lift-≡-elim p) ≡ p
lift-≡-inv₂ p = pr₂ (pr₂ (isequiv→qinv (pr₂ (≡-lift _ _)))) p

prop-up : {a ℓ : Level} → Prop a → Prop (a ⊔ ℓ)
prop-up{a}{ℓ} (A , A-prop) = Lift{a}{ℓ} A , λ { (lift x) (lift y) → ap lift (A-prop x y) }

module truncation-try where

  ∥_∥ : {a : Level} (A : U a) → U a
  ∥ A ∥ = ¬ ¬ A

  postulate
    LEM : {a : Level} (A : U a) → isProp A → A + (¬ A)

  ∣_∣ : {a : Level} {A : U a} → A → ∥ A ∥
  ∣ a ∣ = λ x → x a

  ∥∥-is-prop : {a : Level} (A : U a) → isProp (∥ A ∥)
  ∥∥-is-prop A = λ f g → funext λ x → 𝟘-elim (f x)

  ∥∥-elim : {a b : Level} {A : U a} {B : U b} → isProp B → (A → B) → (∥ A ∥ → B)
  ∥∥-elim B-prop f with (LEM _ B-prop)
  ...                 | inl b  = λ _ → b
  ...                 | inr ¬b = λ ¬¬a → 𝟘-elim (¬¬a λ a → ¬b (f a))

  ∥∥-comp : {a b : Level} {A : U a} {B : U b} {B-prop : isProp B} (f : A → B) (a : A)
          → ∥∥-elim B-prop f ∣ a ∣ ≡ f a
  ∥∥-comp{a'}{b}{A}{B}{B-prop} f a = B-prop _ _

module truncation-try' where

  postulate
    propositional-resizing : {a ℓ : Level} → isequiv (prop-up{a}{ℓ})

  prop-down : {a ℓ : Level} → Prop (a ⊔ ℓ) → Prop a
  prop-down{a}{ℓ} A = pr₁ (isequiv→qinv (propositional-resizing{a}{ℓ})) A

  prop-up-down-id : {a ℓ : Level} (P : Prop (a ⊔ ℓ)) → prop-up{a}{ℓ} (prop-down P) ≡ P
  prop-up-down-id P = pr₁ (pr₂ (isequiv→qinv propositional-resizing)) P

  prop-down-intro : {a ℓ b : Level} (A : Prop a → Prop (a ⊔ ℓ) → U b)
                  → ((P : Prop a) → A P (prop-up{a}{ℓ} P))
                  → ((P : Prop (a ⊔ ℓ)) → A (prop-down{a}{ℓ} P) P)
  prop-down-intro A f P = transp (λ Q → A (prop-down P) Q) (prop-up-down-id _) (f (prop-down P))

  prop-lower : {a ℓ : Level} {P : Prop (a ⊔ ℓ)} (p : pr₁ P) → pr₁ (prop-down{a}{ℓ} P)
  prop-lower{a}{ℓ}{P} = prop-down-intro (λ Q P → (∀ (p : pr₁ P) → pr₁ Q)) (λ P₁ → lower) P

  prop-lift : {a ℓ : Level} {P : Prop a} (p : pr₁ P) → pr₁ (prop-up{a}{ℓ} P)
  prop-lift p = lift p

  ∥∥-raw : {a : Level} (A : U a) → U (a ⊔ lsuc lzero)
  ∥∥-raw{a} A = (P : Prop lzero) → ((A → pr₁ P) → pr₁ P)

  ∥∥-raw-prop : {a : Level} (A : U a) → isProp (∥∥-raw A)
  ∥∥-raw-prop A = λ f g → funext λ x → funext λ y → pr₂ x _ _

  ∥_∥ : {a : Level} (A : U a) → U a
  ∥_∥{a} A = pr₁ (prop-down{a}{lsuc lzero} (∥∥-raw{a} A , ∥∥-raw-prop A))

  ∣_∣-raw : {a : Level} {A : U a} → A → ∥∥-raw A
  ∣ a ∣-raw = λ P z → z a

  ∣_∣ : {a : Level} {A : U a} → A → ∥ A ∥
  ∣ a ∣ = prop-lower ∣ a ∣-raw

  ∥∥-is-prop : {a : Level} (A : U a) → isProp (∥ A ∥)
  ∥∥-is-prop A = pr₂ (prop-down (∥∥-raw A , ∥∥-raw-prop A))

  ∥∥-raw-elim : {a b : Level} {A : U a} {B : U b} → isProp B → (A → B) → (∥∥-raw A → B)
  ∥∥-raw-elim{a}{b}{A}{B} B-prop f g = transp (λ P → pr₁ P) (prop-up-down-id (B , B-prop)) (prop-lift{lzero}{b}{prop-down{lzero}{b} (B , B-prop)} (g (prop-down{lzero}{b} (B , B-prop)) λ a → prop-lower (f a)))

  ∥∥-elim : {a b : Level} {A : U a} {B : U b} → isProp B → (A → B) → (∥ A ∥ → B)
  ∥∥-elim{a}{b}{A}{B} B-prop f = λ a → ∥∥-raw-elim B-prop f (transp (λ P → pr₁ P) (prop-up-down-id A') (prop-lift{_}{_}{prop-down A'} a))
    where
      A' = ∥∥-raw A , ∥∥-raw-prop A

  ∥∥-comp : {a b : Level} {A : U a} {B : U b} {B-prop : isProp B} (f : A → B) (a : A)
          → ∥∥-elim B-prop f ∣ a ∣ ≡ f a
  ∥∥-comp{a'}{b}{A}{B}{B-prop} f a = B-prop _ _

open truncation-try' public

≃-∥∥-≃ : {a b : Level} {A : U a} {B : U b} → A ≃ B → ∥ A ∥ ≃ ∥ B ∥
≃-∥∥-≃ (f , e) = prop-leqv→eqv (∥∥-is-prop _) (∥∥-is-prop _) (∥∥-elim (∥∥-is-prop _) (λ a → ∣ f a ∣)) ((∥∥-elim (∥∥-is-prop _) (λ b → ∣ pr₁ (pr₂ e) b ∣)))

isContr : {a : Level} (A : U a) → U a
isContr A = Σ A (λ a → ∀ x → a ≡ x)

contr→inhabited-prop : {a : Level} {A : U a} → isContr A → isProp A × A
contr→inhabited-prop (a , p) = (λ x y → ((p x) ⁻¹) · p y) , a

inhabited-prop→contr : {a : Level} {A : U a} → isProp A × A → isContr A
inhabited-prop→contr (p , a) = a , λ x → p a x

Lift-𝟙-is-prop : {a : Level} → isProp (Lift{lzero}{a} 𝟙)
Lift-𝟙-is-prop (lift ⋆) (lift ⋆) = refl

≃𝟙→inhabited-prop : {a : Level} {A : U a} → A ≃ 𝟙 → isProp A × A
≃𝟙→inhabited-prop{a}{A} (f , e) = transp (λ A → isProp A × A) ((ua e') ⁻¹) (Lift-𝟙-is-prop , lift ⋆)
  where
    e' : A ≃ Lift{lzero}{a} 𝟙
    e' = (λ x → lift (f x)) , qinv→isequiv ((λ { (lift s) → pr₁ (isequiv→qinv e) s }) , (λ { (lift s) → ap lift (pr₁ (pr₂ (isequiv→qinv e)) s) }) , (λ { x → pr₂ (pr₂ (isequiv→qinv e)) x }))

isContr-is-prop : {a : Level} (A : U a) → isProp (isContr (A))
isContr-is-prop A = λ { c@(a , p) (a' , p') → pair-≡ (p a' , →≡-is-prop a' c _ _) }
  where
    →≡-is-prop : (a : A) → isContr A → isProp (∀ x → a ≡ x)
    →≡-is-prop a isc = is-prop-Π λ x → prop-is-set (pr₁ (contr→inhabited-prop isc)) _ _

contr-isContr-contr : {a : Level} {A : U a} → isContr A → isContr (isContr A)
contr-isContr-contr contr = inhabited-prop→contr (isContr-is-prop _ , contr)

is-contr-Π : {a b : Level} {A : U a} {B : A → U b}
          → (∀ x → isContr (B x)) → isContr (∀ x → B x)
is-contr-Π f = inhabited-prop→contr ((is-prop-Π λ x → pr₁ (contr→inhabited-prop (f x))) , λ x → pr₁ (f x))

isretraction : {a b : Level} {A : U a} {B : U b} (r : A → B) → U (a ⊔ b)
isretraction r = Σ _ (λ s → (r ∘ s) ~ id)

isretract : {a b : Level} (B : U a) (A : U b) → U (a ⊔ b)
isretract B A = Σ (A → B) isretraction

retract-contr : {a b : Level} {A : U a} {B : U b}
              → isretract B A → isContr A → isContr B
retract-contr (r , s , e) (a₀ , p) = r a₀ , λ b → ap r (p (s b)) · e b

pointed-is-contr : {a : Level} {A : U a} (a : A) → isContr (Σ A (λ x → a ≡ x))
pointed-is-contr a = (a , refl) , λ { (a' , p) → pair-≡ (p , (transp-≡-1 p refl · ((·-refl-l p) ⁻¹))) }

Σ₂-contr-equiv : {a b : Level} {A : U a} {B : A → U b}
               → (∀ x → isContr (B x)) → (Σ A B) ≃ A
Σ₂-contr-equiv f = pr₁ , qinv→isequiv ((λ x → x , pr₁ (f x)) , happly refl , λ { (a , b) → pair-≡ (refl , pr₂ (f a) _) })

Σ₁-contr-equiv : {a b : Level} {A : U a} (B : A → U b)
               → (c : isContr A) → (Σ A B) ≃ B (pr₁ c)
Σ₁-contr-equiv B c@(a₀ , p) = (λ w → transp _ ((p (pr₁ w)) ⁻¹) (pr₂ w))
                            , qinv→isequiv ((λ b → a₀ , b) , (λ b → transp (λ q → transp B q b ≡ b) (prop-is-set (pr₁ (contr→inhabited-prop c)) _ _ refl ((p a₀) ⁻¹)) refl)
                                                           , λ { (a , b) → pair-≡ (p a , ap (λ f → f b) (transp-⁻¹' (p a))) })

_↔_ : {a b : Level} (A : U a) (B : U b) → U (a ⊔ b)
A ↔ B = (A → B) × (B → A)

is-prop↔≡-is-contr : {a : Level} (A : U a) → (isProp A ↔ ∀ (x y : A) → isContr (x ≡ y))
is-prop↔≡-is-contr A = (λ prop x y → inhabited-prop→contr ((prop-is-set prop _ _) , (prop x y)))
                     , λ f → λ x y → pr₁ (f x y)

AC : {a b c : Level} → U (lsuc (a ⊔ b ⊔ c))
AC{a}{b}{c} = (X : U a) (A : X → U b) (P : (x : X) → A x → U c)
            → isSet X → (∀ x → isSet (A x)) → (∀ x (a : A x) → isProp (P x a))
            → (∀ x → ∥ Σ (A x) (λ a → P x a) ∥)
            → ∥ Σ (∀ x → A x) (λ g → ∀ x → P x (g x)) ∥

AC' : {a b : Level} → U (lsuc (a ⊔ b))
AC'{a}{b} = (X : U a) (Υ : X → U b)
          → isSet X → (∀ x → isSet (Υ x))
          → (∀ x → ∥ Υ x ∥) → ∥ (∀ x → Υ x) ∥

Σ-universal : {a b c : Level} {X : U a} (A : X → U b) (P : ∀ x → A x → U c)
            → (∀ x → Σ (A x) (λ a → P x a)) ≃ Σ (∀ x → A x) (λ g → ∀ x → P x (g x))
Σ-universal A P = (λ f → (λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))
                , qinv→isequiv ((λ { (a , b) x → a x , b x }) , happly refl , happly refl)

Lift𝟙≃𝟙 : {a : Level} → Lift{lzero}{a} 𝟙 ≃ 𝟙
Lift𝟙≃𝟙 = prop-leqv→eqv Lift-𝟙-is-prop 𝟙-is-prop (λ z → ⋆) lift

AC≃AC' : {a b : Level} → AC{a}{a}{a} ≃ AC'{a}{a}
AC≃AC' = prop-leqv→eqv (is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → ∥∥-is-prop _)
                       (is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → is-prop-Π λ _ → ∥∥-is-prop _)
                       (λ AC X Y X-set Y-set f → pr₁ (≃-∥∥-≃ (Σ₂-≃𝟙-equiv λ _ → ≃𝟙-Π λ _ → Lift𝟙≃𝟙)) (AC X Y (λ _ _ → Lift 𝟙) X-set Y-set (λ _ _ → Lift-𝟙-is-prop) λ x → ∥∥-elim (∥∥-is-prop _) (λ x → ∣ x , lift ⋆ ∣) (f x)))
                       λ AC X A P X-set A-set P-prop f → pr₁ (eqv₁ X A P) (AC X (λ x → Σ (A x) (P x)) X-set (λ x → is-set-Σ (A-set x) λ a → prop-is-set (P-prop x a)) f)
  where
    eqv₁ : {a b c : Level} (X : U a) (A : X → U b) (P : (x : X) → A x → U c)
         → ∥ (∀ x → Σ (A x) (λ a → P x a)) ∥ ≃ ∥ Σ (∀ x → A x) (λ g → ∀ x → P x (g x)) ∥
    eqv₁ X A P = ≃-∥∥-≃ (Σ-universal A P)

    ≃𝟙-Π : {a b : Level} {A : U a} {B : A → U b} → (∀ x → (B x) ≃ 𝟙) → (∀ x → B x) ≃ 𝟙
    ≃𝟙-Π{a}{b}{A}{B} f = inhabited-prop→≃𝟙 (contr→inhabited-prop (is-contr-Π (λ x → inhabited-prop→contr (≃𝟙→inhabited-prop (f x)))))

    Σ₂-≃𝟙-equiv : {a b : Level} {A : U a} {B : A → U b}
                   → (∀ x → (B x) ≃ 𝟙) → (Σ A B) ≃ A
    Σ₂-≃𝟙-equiv f = Σ₂-contr-equiv λ x → inhabited-prop→contr (pr₁ (≃𝟙→inhabited-prop (f x)) , pr₂ (≃𝟙→inhabited-prop (f x)))

is-set-lift : {a b : Level} {A : U a} → isSet A → isSet (Lift{a}{b} A)
is-set-lift a = λ { (lift x) (lift y) p q → ((lift-≡-inv₂ p) ⁻¹) · (ap lift-≡-intro (a _ _ _ _) · lift-≡-inv₂ q)}

∞-AC'-unsound : Σ (U (lsuc lzero)) λ X → Σ (X → (U (lsuc lzero))) λ Y → (∀ x → isSet (Y x)) × (¬ ((∀ x → ∥ Y x ∥) → ∥ (∀ x → Y x) ∥))
∞-AC'-unsound = X , Y
              , (λ { u@(A , p) → ∥∥-elim (isSet-is-prop _) (λ 𝟚≡A → transp (λ B → isSet B) ((ua (≡-Σ x₀ u)) ⁻¹) (is-set-Σ (𝟚≡A-is-set 𝟚≡A) λ _ → prop-is-set (prop-is-set (∥∥-is-prop _) _ _))) p})
              , λ AC → ∥∥-elim 𝟘-is-prop (λ f → X-not-set (prop-is-set λ x y → ((f x) ⁻¹) · f y)) (AC λ { (A , p) → ∥∥-elim (∥∥-is-prop _) (λ 𝟚≡A → ∣ pair-≡ (𝟚≡A , ∥∥-is-prop _ _ _) ∣) p })
  where
    X = Σ U (λ A → ∥ 𝟚 ≡ A ∥)
    x₀ : X
    x₀ = (𝟚 , ∣ refl ∣)
    Y = λ x → x₀ ≡ x
    X-≡-≃ : (u v : X) → (u ≡ v) ≃ (pr₁ u ≃ pr₁ v)
    X-≡-≃ (A , p) (B , q) = ≃-assoc (≡-Σ _ _) (≃-assoc (Σ₂-contr-equiv λ _ → pr₁ (is-prop↔≡-is-contr _) (∥∥-is-prop _) _ _) univalence')
    X-not-set : ¬ isSet(X)
    X-not-set X-is-set = ¬𝟚≡𝟚-prop (pr₁ (≃𝟙→inhabited-prop 𝟚≡𝟚≃𝟙))
      where
        𝟚≡𝟚≃𝟙 : (𝟚 ≡ 𝟚) ≃ 𝟙
        𝟚≡𝟚≃𝟙 = ≃-assoc univalence' (≃-assoc (≃-sym (X-≡-≃ x₀ x₀)) (inhabited-prop→≃𝟙 (X-is-set _ _ , refl)))
    𝟚≡A-is-set : {A : U} → 𝟚 ≡ A → isSet (𝟚 ≡ A)
    𝟚≡A-is-set 𝟚≡A = transp (λ B → isSet B) (ua (≃-assoc (lift-≃ _) (≃-sym univalence'))) (is-set-lift (is-set-≃ 𝟚-is-set (transp _ 𝟚≡A 𝟚-is-set)))

