{-# OPTIONS --rewriting #-}

module Properties.Subtyping where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Subtyping using (_<:_; _≮:_; Value; Language; ¬Language; RLanguage; ¬RLanguage; witness; any; never; scalar; scalar-function; scalar-scalar; scalar-error; function-scalar; function-ok; function-nok; function-error; function-none; function-one; check-one; check-none; check-ok; check-nok; check-error; check-scalar; left; right; _,_; _↦_; ⟨⟩; ⟨_⟩; error; diverge; one; function-arity; blame; caller; callee; suppression)
open import Luau.Type using (Type; Scalar; scalar; error; never; unknown; funktion; negate; check; _⇒_; _∪_; _∩_; any; number; string; function; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_; ⌊_⌋; _\\_)
open import Properties.Contradiction using (CONTRADICTION; ¬; ⊥)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Equality using (_≢_)
open import Properties.Functions using (_∘_)
open import Properties.Product using (_×_; _,_)

-- Language membership is decidable
dec-language : ∀ T t → Either (¬Language T t) (Language T t)
dec-rlanguage : ∀ T t → Either (¬RLanguage T t) (RLanguage T t)

dec-language (scalar S) error = Left (scalar-error S)
dec-language (scalar S) ⟨ scalar T ⟩ with T ≡ˢ S 
dec-language (scalar S) ⟨ scalar T ⟩ | yes refl = Right (scalar S)
dec-language (scalar S) ⟨ scalar T ⟩ | no p = Left (scalar-scalar T S p)
dec-language (scalar S) ⟨ s ↦ t ⟩ = Left (scalar-function S)
dec-language never t = Left never
dec-language any t = Right any
dec-language (S ∪ T) t = cond (λ p → mapLR (_,_ p) right (dec-language T t)) (Right ∘ left) (dec-language S t)
dec-language (S ∩ T) t = cond (Left ∘ left) (λ p → mapLR right (_,_ p) (dec-language T t)) (dec-language S t)
dec-language error error = Right error
dec-language error ⟨ t ⟩ = Left error
dec-language (S ⇒ T) error = Left function-error
dec-language (S ⇒ T) ⟨ scalar s ⟩ = Left (function-scalar s)
dec-language (S ⇒ T) ⟨ ⟨ s ⟩ ↦ t ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-one p) function-ok (dec-rlanguage T t)) (dec-language S ⟨ s ⟩)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ blame caller ⟩ = cond (Right ∘ function-arity) (Left ∘ function-arity) (dec-language S error)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ blame callee ⟩ = Right (function-ok callee)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ blame suppression ⟩ = mapLR (function-none (λ ()) ∘ suppression) (function-ok ∘ suppression) (dec-language T error)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ diverge ⟩ = Right (function-ok diverge)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = mapLR (function-none (λ ())) function-ok (dec-rlanguage T ⟨ t ⟩)
dec-language (check T) error = Left check-error
dec-language (check T) ⟨ scalar S ⟩ = Left check-scalar
dec-language (check T) ⟨ ⟨⟩ ↦ blame callee ⟩ = Right check-nok
dec-language (check T) ⟨ ⟨⟩ ↦ blame caller ⟩ = Left (check-none (λ ()))
dec-language (check T) ⟨ ⟨⟩ ↦ blame suppression ⟩ = Left (check-none (λ ()))
dec-language (check T) ⟨ ⟨⟩ ↦ diverge ⟩ = Left (check-none (λ ()))
dec-language (check T) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = Left (check-none (λ ()))
dec-language (check T) ⟨ ⟨ s ⟩ ↦ blame callee ⟩ = Right check-nok
dec-language (check T) ⟨ ⟨ s ⟩ ↦ blame caller ⟩ = mapLR (check-one (λ ())) check-ok (dec-language ⌊ T ⌋ ⟨ s ⟩)
dec-language (check T) ⟨ ⟨ s ⟩ ↦ blame suppression ⟩ = mapLR (check-one (λ ())) check-ok (dec-language ⌊ T ⌋ ⟨ s ⟩)
dec-language (check T) ⟨ ⟨ s ⟩ ↦ diverge ⟩ = mapLR (check-one (λ ())) check-ok (dec-language ⌊ T ⌋ ⟨ s ⟩)
dec-language (check T) ⟨ ⟨ s ⟩ ↦ ⟨ t ⟩ ⟩ = mapLR (check-one (λ ())) check-ok (dec-language ⌊ T ⌋ ⟨ s ⟩)

dec-rlanguage T diverge = Right diverge
dec-rlanguage T ⟨ t ⟩ = mapLR one one (dec-language T ⟨ t ⟩)
dec-rlanguage T (blame caller) = Left caller
dec-rlanguage T (blame callee) = Right callee
dec-rlanguage T (blame suppression) = mapLR suppression suppression (dec-language T error)

-- ¬Language T is the complement of Language T
language-comp : ∀ {T t} → ¬Language T t → ¬(Language T t)
language-comp (p₁ , p₂) (left q) = language-comp p₁ q
language-comp (p₁ , p₂) (right q) = language-comp p₂ q
language-comp (left p) (q₁ , q₂) = language-comp p q₁
language-comp (right p) (q₁ , q₂) = language-comp p q₂
language-comp (scalar-scalar s p₁ p₂) (scalar s) = p₂ refl
language-comp (function-one p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-one p₁ (one p₂)) (function-ok (one q)) = language-comp p₂ q
language-comp (function-one p₁ (suppression p₂)) (function-ok (suppression q)) = language-comp p₂ q
language-comp (function-none p₁ (one p₂)) (function-ok (one q)) = language-comp p₂ q
language-comp (function-none p₁ p₂) (function-arity q) = p₁ refl
language-comp (function-none p₁ (suppression p₂)) (function-ok (suppression q)) = language-comp p₂ q
language-comp (function-arity p) (function-arity q) = language-comp q p
language-comp (check-one p₁ p₂) (check-ok q) = language-comp p₂ q
language-comp (check-one p₁ p₂) check-nok = p₁ refl
language-comp (check-none p) check-nok = p refl

-- ≮: is the complement of <:
¬≮:-impl-<: : ∀ {T U} → ¬(T ≮: U) → (T <: U)
¬≮:-impl-<: {T} {U} p {t} q with dec-language U t
¬≮:-impl-<: {T} {U} p q | Left r = CONTRADICTION (p (witness q r))
¬≮:-impl-<: {T} {U} p q | Right r = r

<:-impl-¬≮: : ∀ {T U} → (T <: U) → ¬(T ≮: U)
<:-impl-¬≮: p (witness q r) = language-comp r (p q)

<:-impl-⊇ : ∀ {T U} → (T <: U) → ∀ {t} → ¬Language U t → ¬Language T t
<:-impl-⊇ {T} p {t} q with dec-language T t
<:-impl-⊇ p q | Left r = r
<:-impl-⊇ p q | Right r = CONTRADICTION (language-comp q (p r))

-- reflexivity
≮:-refl : ∀ {T} → ¬(T ≮: T)
≮:-refl (witness p q) = language-comp q p

<:-refl : ∀ {T} → (T <: T)
<:-refl = ¬≮:-impl-<: ≮:-refl

-- transititivity
≮:-trans-≡ : ∀ {S T U} → (S ≮: T) → (T ≡ U) → (S ≮: U)
≮:-trans-≡ p refl = p

<:-trans-≡ : ∀ {S T U} → (S <: T) → (T ≡ U) → (S <: U)
<:-trans-≡ p refl = p

≡-impl-<: : ∀ {T U} → (T ≡ U) → (T <: U)
≡-impl-<: refl = <:-refl

≡-trans-≮: : ∀ {S T U} → (S ≡ T) → (T ≮: U) → (S ≮: U)
≡-trans-≮: refl p = p

≡-trans-<: : ∀ {S T U} → (S ≡ T) → (T <: U) → (S <: U)
≡-trans-<: refl p = p

≮:-trans : ∀ {S T U} → (S ≮: U) → Either (S ≮: T) (T ≮: U)
≮:-trans {T = T} (witness p q) = mapLR (witness p) (λ z → witness z q) (dec-language T _)

<:-trans : ∀ {S T U} → (S <: T) → (T <: U) → (S <: U)
<:-trans p q r = q (p r)

<:-trans-≮: : ∀ {S T U} → (S <: T) → (S ≮: U) → (T ≮: U)
<:-trans-≮: p (witness q r) = witness (p q) r

≮:-trans-<: : ∀ {S T U} → (S ≮: U) → (T <: U) → (S ≮: T)
≮:-trans-<: (witness p q) r = witness p (<:-impl-⊇ r q)

-- Properties of union

<:-union : ∀ {R S T U} → (R <: T) → (S <: U) → ((R ∪ S) <: (T ∪ U))
<:-union p q (left r) = left (p r)
<:-union p q (right r) = right (q r)

<:-∪-left : ∀ {S T} → S <: (S ∪ T)
<:-∪-left p = left p

<:-∪-right : ∀ {S T} → T <: (S ∪ T)
<:-∪-right p = right p

<:-∪-lub : ∀ {S T U} → (S <: U) → (T <: U) → ((S ∪ T) <: U)
<:-∪-lub p q (left r) = p r
<:-∪-lub p q (right r) = q r

<:-∪-symm : ∀ {T U} → (T ∪ U) <: (U ∪ T)
<:-∪-symm (left p) = right p
<:-∪-symm (right p) = left p

<:-∪-assocl : ∀ {S T U} → (S ∪ (T ∪ U)) <: ((S ∪ T) ∪ U)
<:-∪-assocl (left p) = left (left p)
<:-∪-assocl (right (left p)) = left (right p)
<:-∪-assocl (right (right p)) = right p

<:-∪-assocr : ∀ {S T U} → ((S ∪ T) ∪ U) <: (S ∪ (T ∪ U))
<:-∪-assocr (left (left p)) = left p
<:-∪-assocr (left (right p)) = right (left p)
<:-∪-assocr (right p) = right (right p)

≮:-∪-left : ∀ {S T U} → (S ≮: U) → ((S ∪ T) ≮: U)
≮:-∪-left (witness p q) = witness (left p) q

≮:-∪-right : ∀ {S T U} → (T ≮: U) → ((S ∪ T) ≮: U)
≮:-∪-right (witness p q) = witness (right p) q

≮:-left-∪ : ∀ {S T U} → (S ≮: (T ∪ U)) → (S ≮: T)
≮:-left-∪ (witness p (q₁ , q₂)) = witness p q₁

≮:-right-∪ : ∀ {S T U} → (S ≮: (T ∪ U)) → (S ≮: U)
≮:-right-∪ (witness p (q₁ , q₂)) = witness p q₂

-- Properties of intersection

<:-intersect : ∀ {R S T U} → (R <: T) → (S <: U) → ((R ∩ S) <: (T ∩ U))
<:-intersect p q (r₁ , r₂) = (p r₁ , q r₂)

<:-∩-left : ∀ {S T} → (S ∩ T) <: S
<:-∩-left (p , _) = p

<:-∩-right : ∀ {S T} → (S ∩ T) <: T
<:-∩-right (_ , p) = p

<:-∩-glb : ∀ {S T U} → (S <: T) → (S <: U) → (S <: (T ∩ U))
<:-∩-glb p q r = (p r , q r)

<:-∩-symm : ∀ {T U} → (T ∩ U) <: (U ∩ T)
<:-∩-symm (p₁ , p₂) = (p₂ , p₁)

<:-∩-assocl : ∀ {S T U} → (S ∩ (T ∩ U)) <: ((S ∩ T) ∩ U)
<:-∩-assocl (p , (p₁ , p₂)) = (p , p₁) , p₂

<:-∩-assocr : ∀ {S T U} → ((S ∩ T) ∩ U) <: (S ∩ (T ∩ U))
<:-∩-assocr ((p , p₁) , p₂) = p , (p₁ , p₂)

≮:-∩-left : ∀ {S T U} → (S ≮: T) → (S ≮: (T ∩ U))
≮:-∩-left (witness p q) = witness p (left q)

≮:-∩-right : ∀ {S T U} → (S ≮: U) → (S ≮: (T ∩ U))
≮:-∩-right (witness p q) = witness p (right q)

-- Distribution properties
<:-∩-distl-∪ : ∀ {S T U} → (S ∩ (T ∪ U)) <: ((S ∩ T) ∪ (S ∩ U))
<:-∩-distl-∪ (p₁ , left p₂) = left (p₁ , p₂)
<:-∩-distl-∪ (p₁ , right p₂) = right (p₁ , p₂)

∩-distl-∪-<: : ∀ {S T U} → ((S ∩ T) ∪ (S ∩ U)) <: (S ∩ (T ∪ U))
∩-distl-∪-<: (left (p₁ , p₂)) = (p₁ , left p₂)
∩-distl-∪-<: (right (p₁ , p₂)) = (p₁ , right p₂)

<:-∩-distr-∪ : ∀ {S T U} → ((S ∪ T) ∩ U) <:  ((S ∩ U) ∪ (T ∩ U))
<:-∩-distr-∪ (left p₁ , p₂) = left (p₁ , p₂)
<:-∩-distr-∪ (right p₁ , p₂) = right (p₁ , p₂)

∩-distr-∪-<: : ∀ {S T U} → ((S ∩ U) ∪ (T ∩ U)) <: ((S ∪ T) ∩ U)
∩-distr-∪-<: (left (p₁ , p₂)) = (left p₁ , p₂)
∩-distr-∪-<: (right (p₁ , p₂)) = (right p₁ , p₂)

<:-∪-distl-∩ : ∀ {S T U} → (S ∪ (T ∩ U)) <: ((S ∪ T) ∩ (S ∪ U))
<:-∪-distl-∩ (left p) = (left p , left p)
<:-∪-distl-∩ (right (p₁ , p₂)) = (right p₁ , right p₂)

∪-distl-∩-<: : ∀ {S T U} → ((S ∪ T) ∩ (S ∪ U)) <: (S ∪ (T ∩ U))
∪-distl-∩-<: (left p₁ , p₂) = left p₁
∪-distl-∩-<: (right p₁ , left p₂) = left p₂
∪-distl-∩-<: (right p₁ , right p₂) = right (p₁ , p₂)

<:-∪-distr-∩ : ∀ {S T U} → ((S ∩ T) ∪ U) <: ((S ∪ U) ∩ (T ∪ U))
<:-∪-distr-∩ (left (p₁ , p₂)) = left p₁ , left p₂
<:-∪-distr-∩ (right p) = (right p , right p)

∪-distr-∩-<: : ∀ {S T U} → ((S ∪ U) ∩ (T ∪ U)) <: ((S ∩ T) ∪ U)
∪-distr-∩-<: (left p₁ , left p₂) = left (p₁ , p₂)
∪-distr-∩-<: (left p₁ , right p₂) = right p₂
∪-distr-∩-<: (right p₁ , p₂) = right p₁

∩-<:-∪ : ∀ {S T} → (S ∩ T) <: (S ∪ T)
∩-<:-∪ (p , _) = left p

-- Properties of functions
<:-function : ∀ {R S T U} → (R <: S) → (T <: U) → (S ⇒ T) <: (R ⇒ U)
<:-function p q (function-ok diverge) = function-ok diverge
<:-function p q (function-ok callee) = function-ok callee
<:-function p q (function-ok (suppression r)) = function-ok (suppression (q r))
<:-function p q (function-ok (one r)) = function-ok (one (q r))
<:-function p q (function-nok r) = function-nok (<:-impl-⊇ p r)
<:-function p q (function-arity r) = function-arity (<:-impl-⊇ p r)

<:-function-∩-∩ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∩ S) ⇒ (T ∩ U))
<:-function-∩-∩ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩-∩ (function-ok callee , q) = function-ok callee
<:-function-∩-∩ (function-ok (suppression p) , function-ok (suppression q)) = function-ok (suppression (p , q))
<:-function-∩-∩ (function-nok p , q) = function-nok (left p)
<:-function-∩-∩ (p , function-nok q) = function-nok (right q)
<:-function-∩-∩ (function-arity p , q) = function-arity (left p)

<:-function-∩-∪ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∪ S) ⇒ (T ∪ U))
<:-function-∩-∪ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∪ (p , function-ok (one q)) = function-ok (one (right q))
<:-function-∩-∪ (function-ok diverge , q) = function-ok diverge
<:-function-∩-∪ (function-ok (one p) , q) = function-ok (one (left p))
<:-function-∩-∪ (function-ok callee , q) = function-ok callee
<:-function-∩-∪ (function-ok (suppression p) , q) = function-ok (suppression (left p))
<:-function-∩-∪ (function-nok p , function-nok q) = function-nok (p , q)
<:-function-∩-∪ (function-nok p , function-ok callee) = function-ok callee
<:-function-∩-∪ (function-nok p , function-ok (suppression q)) = function-ok (suppression (right q))
<:-function-∩-∪ (function-arity p , function-arity q) = function-arity (p , q)

<:-function-∩ : ∀ {S T U} → ((S ⇒ T) ∩ (S ⇒ U)) <: (S ⇒ (T ∩ U))
<:-function-∩ (function-ok diverge , q) = function-ok diverge
<:-function-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩ (function-ok callee , q) = function-ok callee
<:-function-∩ (function-ok (suppression p) , function-ok (suppression q)) = function-ok (suppression (p , q))
<:-function-∩ (function-nok p , q) = function-nok p
<:-function-∩ (p , function-nok q) = function-nok q
<:-function-∩ (function-arity p , q) = function-arity p

<:-function-∪ : ∀ {R S T U} → ((R ⇒ S) ∪ (T ⇒ U)) <: ((R ∩ T) ⇒ (S ∪ U))
<:-function-∪ (left (function-ok diverge)) = function-ok diverge
<:-function-∪ (left (function-ok (one p))) = function-ok (one (left p))
<:-function-∪ (left (function-ok callee)) = function-ok callee
<:-function-∪ (left (function-ok (suppression p))) = function-ok (suppression (left p))
<:-function-∪ (left (function-nok p)) = function-nok (left p)
<:-function-∪ (left (function-arity p)) = function-arity (left p)
<:-function-∪ (right (function-ok diverge)) = function-ok diverge
<:-function-∪ (right (function-ok (one p))) = function-ok (one (right p))
<:-function-∪ (right (function-ok callee)) = function-ok callee
<:-function-∪ (right (function-ok (suppression q))) = function-ok (suppression (right q))
<:-function-∪ (right (function-nok p)) = function-nok (right p)
<:-function-∪ (right (function-arity p)) = function-arity (right p)

<:-function-∪-∩ : ∀ {R S T U} → ((R ∩ S) ⇒ (T ∪ U)) <: ((R ⇒ T) ∪ (S ⇒ U))
<:-function-∪-∩ (function-ok diverge) = left (function-ok diverge)
<:-function-∪-∩ (function-ok (one (left p))) = left (function-ok (one p))
<:-function-∪-∩ (function-ok (one (right p))) = right (function-ok (one p))
<:-function-∪-∩ (function-ok callee) = left (function-ok callee)
<:-function-∪-∩ (function-ok (suppression (left p))) = left (function-ok (suppression p))
<:-function-∪-∩ (function-ok (suppression (right p))) = right (function-ok (suppression p))
<:-function-∪-∩ (function-nok (left p)) = left (function-nok p)
<:-function-∪-∩ (function-nok (right p)) = right (function-nok p)
<:-function-∪-∩ (function-arity (left p)) = left (function-arity p)
<:-function-∪-∩ (function-arity (right p)) = right (function-arity p)

<:-function-left : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (R <: S)
<:-function-left {R} {S} p {error} Re with <:-impl-⊇ p { ⟨ ⟨⟩ ↦ blame caller ⟩ } (function-arity Re)
<:-function-left {R} {S} p {error} Re | function-none q r = CONTRADICTION (q refl)
<:-function-left {R} {S} p {error} Re | function-arity Se = Se
<:-function-left {R} {S} p {⟨ s ⟩} Rs with <:-impl-⊇ p { ⟨ ⟨ s ⟩ ↦ blame caller ⟩ } (function-one Rs caller)
<:-function-left {R} {S} p {⟨ s ⟩} Rs | function-one Ss caller = Ss

<:-function-right : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (T <: U)
<:-function-right p {error} Te with p {t = ⟨ ⟨⟩ ↦ blame suppression ⟩} (function-ok (suppression Te))
<:-function-right p {error} Te | function-ok (suppression Ue) = Ue
<:-function-right p {⟨ t ⟩} Tt with p { t = ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ } (function-ok (one Tt))
<:-function-right p {⟨ t ⟩} Tt | function-ok (one Ut) = Ut

≮:-function-left : ∀ {R S T U} → (R ≮: S) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-left (witness {error} p q) = witness {t = ⟨ ⟨⟩ ↦ blame caller ⟩} (function-arity q) (function-arity p)
≮:-function-left (witness {⟨ s ⟩} p q) = witness {t = ⟨ ⟨ s ⟩ ↦ blame caller ⟩} (function-nok q) (function-one p caller)

≮:-function-right : ∀ {R S T U} → (T ≮: U) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-right (witness {error} p q) = witness { t = ⟨ ⟨⟩ ↦ blame suppression ⟩ } (function-ok (suppression p)) (function-none (λ ()) (suppression q))
≮:-function-right (witness {⟨ s ⟩} p q) = witness { t = ⟨ ⟨⟩ ↦ ⟨ s ⟩ ⟩ } (function-ok (one p)) (function-none (λ ()) (one q))

function-<:-funktion : ∀ {S T} → (S ⇒ T) <: funktion
function-<:-funktion = <:-function (λ()) (λ p → any)

function-<:-unknown : ∀ {S T} → (S ⇒ T) <: unknown
function-<:-unknown p = left (left (left (left (function-<:-funktion p))))

error-≮:-function : ∀ {S T} → error ≮: (S ⇒ T)
error-≮:-function = witness error function-error

-- Properties of type subtraction
test-¬error : ∀ {S} → ¬Language ⌊ S ⌋ error
test-¬error {scalar S} = scalar-error S
test-¬error {function} = function-error
test-¬error {never} = never
test-¬error {S ∪ T} = (test-¬error , test-¬error)

negate-lang : ∀ {S t} → Language ⌊ S ⌋ t → ¬Language (negate S) t
negate-lang {scalar NUMBER} (scalar NUMBER) = ((((error , function-scalar NUMBER) ,
                                                   scalar-scalar NUMBER STRING (λ ()))
                                                  , scalar-scalar NUMBER NIL (λ ())) , scalar-scalar NUMBER BOOLEAN (λ ()))
negate-lang {scalar BOOLEAN} (scalar BOOLEAN) = (((error , function-scalar BOOLEAN) ,
                                                    scalar-scalar BOOLEAN NUMBER (λ ()))
                                                   , scalar-scalar BOOLEAN STRING (λ ()))
                                                  , scalar-scalar BOOLEAN NIL (λ ())
negate-lang {scalar STRING} (scalar STRING) = (((error , function-scalar STRING) ,
                                                  scalar-scalar STRING NUMBER (λ ()))
                                                 , scalar-scalar STRING NIL (λ ()))
                                                , scalar-scalar STRING BOOLEAN (λ ())
negate-lang {scalar NIL} (scalar NIL) = (((error , function-scalar NIL) , scalar-scalar NIL NUMBER (λ ()))
                                           , scalar-scalar NIL STRING (λ ()))
                                          , scalar-scalar NIL BOOLEAN (λ ())
negate-lang {function} (function-nok p) = ((((error , scalar-function NUMBER) , scalar-function STRING) ,
                                             scalar-function NIL) , scalar-function BOOLEAN)
negate-lang {function} (function-ok p) = (((error , scalar-function NUMBER) , scalar-function STRING) ,
                                            scalar-function NIL)
                                           , scalar-function BOOLEAN
negate-lang {function} (function-arity p) = (((error , scalar-function NUMBER) , scalar-function STRING) ,
                                               scalar-function NIL)
                                              , scalar-function BOOLEAN
negate-lang {S ∪ T} (left p) = left (negate-lang p)
negate-lang {S ∪ T} (right p) = right (negate-lang p)

negate-¬lang : ∀ {S t} → ¬Language ⌊ S ⌋ t → Language (negate S) t
negate-¬lang {scalar NUMBER} (scalar-scalar NUMBER NUMBER p) = CONTRADICTION (p refl)
negate-¬lang {scalar NUMBER} (scalar-scalar BOOLEAN NUMBER p) = right (scalar BOOLEAN)
negate-¬lang {scalar NUMBER} (scalar-scalar STRING NUMBER p) = left (left (right (scalar STRING)))
negate-¬lang {scalar NUMBER} (scalar-scalar NIL NUMBER p) = left (right (scalar NIL))
negate-¬lang {scalar BOOLEAN} (scalar-scalar NUMBER BOOLEAN p) = left (left (right (scalar NUMBER)))
negate-¬lang {scalar BOOLEAN} (scalar-scalar BOOLEAN BOOLEAN p) = CONTRADICTION (p refl)
negate-¬lang {scalar BOOLEAN} (scalar-scalar STRING BOOLEAN p) = left (right (scalar STRING))
negate-¬lang {scalar BOOLEAN} (scalar-scalar NIL BOOLEAN p) = right (scalar NIL)
negate-¬lang {scalar STRING} (scalar-scalar NUMBER STRING p) = left (left (right (scalar NUMBER)))
negate-¬lang {scalar STRING} (scalar-scalar BOOLEAN STRING p) = right (scalar BOOLEAN)
negate-¬lang {scalar STRING} (scalar-scalar STRING STRING p) = CONTRADICTION (p refl)
negate-¬lang {scalar STRING} (scalar-scalar NIL STRING p) = left (right (scalar NIL))
negate-¬lang {scalar NIL} (scalar-scalar NUMBER NIL p) = left (left (right (scalar NUMBER)))
negate-¬lang {scalar NIL} (scalar-scalar BOOLEAN NIL p) = right (scalar BOOLEAN)
negate-¬lang {scalar NIL} (scalar-scalar STRING NIL p) = left (right (scalar STRING))
negate-¬lang {scalar NIL} (scalar-scalar NIL NIL p) = CONTRADICTION (p refl)
negate-¬lang {scalar NUMBER} (scalar-error NUMBER) = left (left (left (left error)))
negate-¬lang {scalar BOOLEAN} (scalar-error BOOLEAN) = left (left (left (left error)))
negate-¬lang {scalar STRING} (scalar-error STRING) = left (left (left (left error)))
negate-¬lang {scalar NIL} (scalar-error NIL) = left (left (left (left error)))
negate-¬lang {scalar NUMBER} {⟨ ⟨⟩ ↦ blame callee ⟩} (scalar-function NUMBER) = left (left (left (right (function-ok callee))))
negate-¬lang {scalar NUMBER} {⟨ ⟨⟩ ↦ blame caller ⟩} (scalar-function NUMBER) = left (left (left (right (function-arity never))))
negate-¬lang {scalar NUMBER} {⟨ ⟨⟩ ↦ blame suppression ⟩} (scalar-function NUMBER) = left (left (left (right (function-ok (suppression any)))))
negate-¬lang {scalar NUMBER} {⟨ ⟨⟩ ↦ diverge ⟩} (scalar-function NUMBER) = left (left (left (right (function-ok diverge))))
negate-¬lang {scalar NUMBER} {⟨ ⟨⟩ ↦ ⟨ x ⟩ ⟩} (scalar-function NUMBER) = left (left (left (right (function-ok (one any)))))
negate-¬lang {scalar NUMBER} {⟨ ⟨ s ⟩ ↦ t ⟩} (scalar-function NUMBER) = left (left (left (right (function-nok never))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨⟩ ↦ blame callee ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-ok callee))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨⟩ ↦ blame caller ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-arity never))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨⟩ ↦ blame suppression ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-ok (suppression any)))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨⟩ ↦ diverge ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-ok diverge))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-ok (one any)))))
negate-¬lang {scalar BOOLEAN} {⟨ ⟨ s ⟩ ↦ t ⟩} (scalar-function BOOLEAN) = left (left (left (right (function-nok never))))
negate-¬lang {scalar STRING} {⟨ ⟨⟩ ↦ blame callee ⟩} (scalar-function STRING) = left (left (left (right (function-ok callee))))
negate-¬lang {scalar STRING} {⟨ ⟨⟩ ↦ blame caller ⟩} (scalar-function STRING) = left (left (left (right (function-arity never))))
negate-¬lang {scalar STRING} {⟨ ⟨⟩ ↦ blame suppression ⟩} (scalar-function STRING) = left (left (left (right (function-ok (suppression any)))))
negate-¬lang {scalar STRING} {⟨ ⟨⟩ ↦ diverge ⟩} (scalar-function STRING) = left (left (left (right (function-ok diverge))))
negate-¬lang {scalar STRING} {⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩} (scalar-function STRING) = left (left (left (right (function-ok (one any)))))
negate-¬lang {scalar STRING} {⟨ ⟨ s ⟩ ↦ t ⟩} (scalar-function STRING) = left (left (left (right (function-nok never))))
negate-¬lang {scalar NIL} {⟨ ⟨⟩ ↦ blame callee ⟩} (scalar-function NIL) = left (left (left (right (function-ok callee))))
negate-¬lang {scalar NIL} {⟨ ⟨⟩ ↦ blame caller ⟩} (scalar-function NIL) = left (left (left (right (function-arity never))))
negate-¬lang {scalar NIL} {⟨ ⟨⟩ ↦ blame suppression ⟩} (scalar-function NIL) = left (left (left (right (function-ok (suppression any)))))
negate-¬lang {scalar NIL} {⟨ ⟨⟩ ↦ diverge ⟩} (scalar-function NIL) = left (left (left (right (function-ok diverge))))
negate-¬lang {scalar NIL} {⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩} (scalar-function NIL) = left (left (left (right (function-ok (one any)))))
negate-¬lang {scalar NIL} {⟨ ⟨ s ⟩ ↦ t ⟩} (scalar-function NIL) = left (left (left (right (function-nok never))))
negate-¬lang {function} (function-scalar NUMBER) = left (left (left (right (scalar NUMBER))))
negate-¬lang {function} (function-scalar BOOLEAN) = right (scalar BOOLEAN)
negate-¬lang {function} (function-scalar STRING) = left (left (right (scalar STRING)))
negate-¬lang {function} (function-scalar NIL) = left (right (scalar NIL))
negate-¬lang {function} (function-none p caller) = CONTRADICTION (p refl)
negate-¬lang {function} function-error = left (left (left (left error)))
negate-¬lang {never} p = any
negate-¬lang {S ∪ T} (p , q) = (negate-¬lang p , negate-¬lang q)

¬lang-negate : ∀ {S t} → ¬Language (negate S) t → Language ⌊ S ⌋ t
¬lang-negate {S} {t} p with dec-language ⌊ S ⌋ t
¬lang-negate {S} {t} p | Left q = CONTRADICTION (language-comp p (negate-¬lang q))
¬lang-negate {S} {t} p | Right q = q

lang-negate : ∀ {S t} → Language (negate S) t → ¬Language ⌊ S ⌋ t
lang-negate {S} {t} p with dec-language ⌊ S ⌋ t
lang-negate {S} {t} p | Left q = q
lang-negate {S} {t} p | Right q = CONTRADICTION (language-comp (negate-lang q) p)

\\-left : ∀ {S T t} → ¬Language T t → ¬Language (T \\ S) t
\\-left p = left p

\\-right : ∀ {S T t} → Language ⌊ S ⌋ t → ¬Language (T \\ S) t
\\-right p = right (negate-lang p)

\\-case : ∀ {S T t} → ¬Language (T \\ S) t → Either (¬Language T t) (Language ⌊ S ⌋ t)
\\-case (left p) = Left p
\\-case (right p) = Right (¬lang-negate p)

-- Properties of check functions
<:-check : ∀ {S T} → ⌊ S ⌋ <: ⌊ T ⌋ → check S <: check T
<:-check p (check-ok q) = check-ok (p q)
<:-check p check-nok = check-nok

<:-check-dist-∪ : ∀ {S T} → check (S ∪ T) <: (check(S) ∪ check(T))
<:-check-dist-∪ (check-ok (left p)) = left (check-ok p)
<:-check-dist-∪ (check-ok (right p)) = right (check-ok p)
<:-check-dist-∪ check-nok = left check-nok

check-dist-∪-<: : ∀ {S T} → (check(S) ∪ check(T)) <: check (S ∪ T)
check-dist-∪-<: (left (check-ok p)) = check-ok (left p)
check-dist-∪-<: (left check-nok) = check-nok
check-dist-∪-<: (right (check-ok p)) = check-ok (right p)
check-dist-∪-<: (right check-nok) = check-nok

<:-function-∪-check : ∀ {S T U} → (check S ∪ (T ⇒ U)) <: ((T \\ S) ⇒ U)
<:-function-∪-check (left (check-ok p)) = function-nok (\\-right p)
<:-function-∪-check (left check-nok) = function-ok callee
<:-function-∪-check {S} (right (function-nok p)) = function-nok (\\-left {S} p)
<:-function-∪-check (right (function-ok p)) = function-ok p
<:-function-∪-check {S} (right (function-arity p)) = function-arity (\\-left {S} p)

function-∪-check-<: : ∀ {S T U} → ((T \\ S) ⇒ U) <: (check S ∪ (T ⇒ U))
function-∪-check-<: (function-nok p) with \\-case p
function-∪-check-<: (function-nok p) | Left q = right (function-nok q)
function-∪-check-<: (function-nok p) | Right q = left (check-ok q)
function-∪-check-<: (function-ok p) = right (function-ok p)
function-∪-check-<: {S} (function-arity p) with \\-case {S} p
function-∪-check-<: {S} (function-arity p) | Left q = right (function-arity q)
function-∪-check-<: {S} (function-arity p) | Right q = CONTRADICTION (language-comp test-¬error q)

-- Properties of scalars
scalar-<: : ∀ S {T} → Language T ⟨ scalar S ⟩ → (scalar S <: T)
scalar-<: S p (scalar S) = p

scalar-<:-unknown : ∀ {S} → (scalar S <: unknown)
scalar-<:-unknown {NUMBER} p = left (left (left (right p)))
scalar-<:-unknown {BOOLEAN} p = right p
scalar-<:-unknown {STRING} p = left (left (right p))
scalar-<:-unknown {NIL} p = left (right p)

function-∩-scalar-<:-never : ∀ S {T U V} → ((T ⇒ U) ∩ scalar S) <: V
function-∩-scalar-<:-never S (() , scalar S)

error-∩-scalar-<:-never : ∀ S {V} → (error ∩ scalar S) <: V
error-∩-scalar-<:-never S (() , scalar S)

scalar-∩-error-<:-never : ∀ S {V} → (scalar S ∩ error) <: V
scalar-∩-error-<:-never S (() , error)

function-≮:-scalar : ∀ {S T} U → ((S ⇒ T) ≮: scalar U)
function-≮:-scalar S = witness (function-ok {t = ⟨⟩} diverge) (scalar-function S)

error-≮:-scalar : ∀ S → (error ≮: scalar S)
error-≮:-scalar S = witness error (scalar-error S)

scalar-≮:-function : ∀ {S T} U → (scalar U ≮: (S ⇒ T))
scalar-≮:-function S = witness (scalar S) (function-scalar S)

any-≮:-scalar : ∀ U → (any ≮: scalar U)
any-≮:-scalar s = witness any (scalar-function s {t = ⟨⟩} {u = diverge})

scalar-≮:-never : ∀ U → (scalar U ≮: never)
scalar-≮:-never s = witness (scalar s) never

scalar-≢-impl-≮: : ∀ T U → (T ≢ U) → (scalar T ≮: scalar U)
scalar-≢-impl-≮: s₁ s₂ p = witness (scalar s₁) (scalar-scalar s₁ s₂ p)

scalar-≢-∩-<:-never : ∀ T U {V} → (T ≢ U) → (scalar T ∩ scalar U) <: V
scalar-≢-∩-<:-never s t p (scalar s₁ , scalar s₂) = CONTRADICTION (p refl)

-- Properties of error
error-<: : ∀ {T} → Language T error → (error <: T)
error-<: p error = p

function-∩-error-<:-never : ∀ {T U V} → ((T ⇒ U) ∩ error) <: V
function-∩-error-<:-never (() , error)

error-≮:-never : error ≮: never
error-≮:-never = witness error never

-- Properties of any and never
any-≮: : ∀ {T U} → (T ≮: U) → (any ≮: U)
any-≮: (witness p q) = witness any q

never-≮: : ∀ {T U} → (T ≮: U) → (T ≮: never)
never-≮: (witness p q) = witness p never

any-≮:-never : (any ≮: never)
any-≮:-never = witness {t = ⟨ scalar NIL ⟩} any never

any-≮:-function : ∀ {S T} → (any ≮: (S ⇒ T))
any-≮:-function = witness any (function-scalar NIL)

function-≮:-never : ∀ {T U} → ((T ⇒ U) ≮: never)
function-≮:-never = witness (function-ok {t = ⟨⟩} diverge) never

<:-never : ∀ {T} → (never <: T)
<:-never ()

≮:-never-left : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: T) → (S ∩ U) ≮: never
≮:-never-left p (witness q₁ q₂) with p q₁
≮:-never-left p (witness q₁ q₂) | left r = CONTRADICTION (language-comp q₂ r)
≮:-never-left p (witness q₁ q₂) | right r = witness (q₁ , r) never

≮:-never-right : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: U) → (S ∩ T) ≮: never
≮:-never-right p (witness q₁ q₂) with p q₁
≮:-never-right p (witness q₁ q₂) | left r = witness (q₁ , r) never
≮:-never-right p (witness q₁ q₂) | right r = CONTRADICTION (language-comp q₂ r)

<:-any : ∀ {T} → (T <: any)
<:-any p = any

<:-everything : any <: (unknown ∪ error)
<:-everything {error} p = right error
<:-everything {⟨ scalar NUMBER ⟩} p = left (left (left (left (right (scalar NUMBER)))))
<:-everything {⟨ scalar BOOLEAN ⟩} p = left (right (scalar BOOLEAN))
<:-everything {⟨ scalar STRING ⟩} p = left (left (left (right (scalar STRING))))
<:-everything {⟨ scalar NIL ⟩} p = left (left (right (scalar NIL)))
<:-everything {⟨ ⟨⟩ ↦ blame caller ⟩} p = left (left (left (left (left (function-arity never)))))
<:-everything {⟨ s ↦ blame callee ⟩} p = left (left (left (left (left (function-ok callee)))))
<:-everything {⟨ s ↦ blame suppression ⟩} p = left (left (left (left (left (function-ok (suppression any))))))
<:-everything {⟨ ⟨⟩ ↦ diverge ⟩} p = left (left (left (left (left (function-ok diverge)))))
<:-everything {⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩} p = left (left (left (left (left (function-ok (one any))))))
<:-everything {⟨ ⟨ s ⟩ ↦ t ⟩} p = left (left (left (left (left (function-nok never)))))

-- A Gentle Introduction To Semantic Subtyping (https://www.cduce.org/papers/gentle.pdf)
-- defines a "set-theoretic" model (sec 2.5)
-- Unfortunately we don't quite have this property, due to uninhabited types,
-- for example (never -> T) is equivalent to (never -> U)
-- when types are interpreted as sets of syntactic values.

_⊆_ : ∀ {A : Set} → (A → Set) → (A → Set) → Set
(P ⊆ Q) = ∀ a → (P a) → (Q a)

_⊗_ : ∀ {A B : Set} → (A → Set) → (B → Set) → ((A × B) → Set)
(P ⊗ Q) (a , b) = (P a) × (Q b)

Comp : ∀ {A : Set} → (A → Set) → (A → Set)
Comp P a = ¬(P a)

Lift : ∀ {A : Set} → (A → Set) → (Maybe A → Set)
Lift P nothing = ⊥
Lift P (just a) = P a

set-theoretic-if : ∀ {S₁ T₁ S₂ T₂} →

  -- This is the "if" part of being a set-theoretic model
  -- though it uses the definition from Frisch's thesis
  -- rather than from the Gentle Introduction. The difference
  -- being the presence of Lift, (written D_Ω in Defn 4.2 of
  -- https://www.cduce.org/papers/frisch_phd.pdf).
  (Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂)) →
  (∀ Q → Q ⊆ Comp((Language S₁) ⊗ Comp(Lift(Language T₁))) → Q ⊆ Comp((Language S₂) ⊗ Comp(Lift(Language T₂))))

set-theoretic-if {S₁} {T₁} {S₂} {T₂} p Q q (t , u) Qtu (S₂t , ¬T₂u) = q (t , u) Qtu (S₂⊆S₁ t S₂t , ¬T₂⊆¬T₁ u ¬T₂u) where

  S₂⊆S₁ : Language S₂ ⊆ Language S₁
  S₂⊆S₁ t S₂t with dec-language S₁ t
  S₂⊆S₁ error S₂e | Left ¬S₁e with p ⟨ ⟨⟩ ↦ blame caller ⟩ (function-arity ¬S₁e)
  S₂⊆S₁ error S₂e | Left ¬S₁e | function-arity ¬S₂e = CONTRADICTION (language-comp ¬S₂e S₂e)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t with p ⟨ ⟨ t ⟩ ↦ blame caller ⟩ (function-nok ¬S₁t)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t | function-nok ¬S₂t = CONTRADICTION (language-comp ¬S₂t S₂t)
  S₂⊆S₁ t S₂t | Right S₁t = S₁t
  
  ¬T₂⊆¬T₁ : Comp(Lift(Language T₂)) ⊆ Comp(Lift(Language T₁))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩ (function-ok (one T₁u))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u | function-ok (one T₂u) = ¬T₂u T₂u
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ blame suppression ⟩ (function-ok (suppression T₁u))
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u | function-ok (suppression T₂u) = ¬T₂u T₂u

not-quite-set-theoretic-only-if : ∀ {S₁ T₁ S₂ T₂} →

  -- We don't quite have that this is a set-theoretic model
  -- it's only true when Language S₂ is inhabited
  -- in particular it's not true when S₂ is never,
  ∀ s₂ → Language S₂ s₂ →

  -- This is the "only if" part of being a set-theoretic model
  (∀ Q → Q ⊆ Comp((Language S₁) ⊗ Comp(Lift(Language T₁))) → Q ⊆ Comp((Language S₂) ⊗ Comp(Lift(Language T₂)))) →
  (Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂))

not-quite-set-theoretic-only-if {S₁} {T₁} {S₂} {T₂} s₂ S₂s₂ p = r where

  Q : (Value × Maybe Value) → Set
  Q (t , just u) = Either (¬Language S₁ t) (Language T₁ u)
  Q (t , nothing) = ¬Language S₁ t
  
  q : Q ⊆ Comp(Language S₁ ⊗ Comp(Lift(Language T₁)))
  q (t , just u) (Left ¬S₁t) (S₁t , ¬T₁u) = language-comp ¬S₁t S₁t
  q (t , just u) (Right T₂u) (S₁t , ¬T₁u) = ¬T₁u T₂u
  q (t , nothing) ¬S₁t (S₁t , _) = language-comp ¬S₁t S₁t

  ¬S₁⊆¬S₂ : ¬Language S₁ ⊆ ¬Language S₂
  ¬S₁⊆¬S₂ s ¬S₁s with dec-language S₂ s
  ¬S₁⊆¬S₂ s ¬S₁s | Left ¬S₂s = ¬S₂s
  ¬S₁⊆¬S₂ s ¬S₁s | Right S₂s = CONTRADICTION (p Q q (s , nothing) ¬S₁s (S₂s , λ ()))

  T₁⊆T₂ : Language T₁ ⊆ Language T₂
  T₁⊆T₂ t T₁t with dec-language T₂ t
  T₁⊆T₂ t T₁t | Left ¬T₂t = CONTRADICTION (p Q q (s₂ , just t) (Right T₁t) (S₂s₂ , language-comp ¬T₂t)) 
  T₁⊆T₂ t T₁t | Right T₂t = T₂t

  r : Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂)
  r ⟨ ⟨ s ⟩ ↦ t ⟩ (function-nok ¬S₁s) = function-nok (¬S₁⊆¬S₂ ⟨ s ⟩ ¬S₁s)
  r ⟨ s ↦ ⟨ t ⟩ ⟩ (function-ok (one T₁t)) = function-ok (one (T₁⊆T₂ ⟨ t ⟩ T₁t))
  r ⟨ s ↦ blame suppression ⟩ (function-ok (suppression T₁e)) = function-ok (suppression (T₁⊆T₂ error T₁e))
  r ⟨ ⟨⟩ ↦ blame caller ⟩ (function-arity ¬S₁e) = function-arity (¬S₁⊆¬S₂ error ¬S₁e)
  r ⟨ s ↦ blame callee ⟩ (function-ok callee) = function-ok callee
  r ⟨ s ↦ diverge ⟩ p = function-ok diverge

-- A counterexample when the argument type is empty.

set-theoretic-counterexample-one : (∀ Q → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language number))) → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language string))))
set-theoretic-counterexample-one Q q (⟨ scalar s ⟩ , u) Qtu (() , p)

set-theoretic-counterexample-two : (never ⇒ number) ≮: (never ⇒ string)
set-theoretic-counterexample-two = witness (function-ok (one (scalar NUMBER)))
                                     (function-none (λ ()) (one (scalar-scalar NUMBER STRING (λ ()))))
