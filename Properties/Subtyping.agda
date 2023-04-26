{-# OPTIONS --rewriting #-}

module Properties.Subtyping where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Subtyping using (_<:_; _≮:_; Value; Language; ¬Language; RLanguage; ¬RLanguage; witness; any; never; scalar; scalar-function; scalar-scalar; scalar-error; function-scalar; function-ok; function-nok; function-error; function-function; function-none; function-none-error; check-ok; check-nok; check-diverge; check-scalar; check-error; check-none; left; right; _,_; _↦_; ⟨⟩; ⟨_⟩; error; diverge; one; arity; function-arity; check-arity)
open import Luau.Type using (Type; Scalar; scalar; error; never; unknown; funktion; negate; check; _⇒_; _∪_; _∩_; any; number; string; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_)
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
dec-language (S ⇒ T) ⟨ ⟨ s ⟩ ↦ t ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-function p) function-ok (dec-rlanguage T t)) (dec-language S ⟨ s ⟩)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ error ⟩ = mapLR (λ p → function-none-error (error p)) (function-ok ∘ error) (dec-language T error)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ diverge ⟩ = Right (function-ok diverge)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ arity ⟩ = cond (Right ∘ function-arity) (Left ∘ function-arity) (dec-language S error)
dec-language (S ⇒ T) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = mapLR (function-none ∘ one) (function-ok ∘ one) (dec-language T ⟨ t ⟩)
dec-language (check S) error = Left check-error
dec-language (check S) ⟨ scalar s ⟩ = Left check-scalar
dec-language (check S) ⟨ ⟨⟩ ↦ error ⟩ = Left check-nok
dec-language (check S) ⟨ ⟨⟩ ↦ diverge ⟩ = Left check-diverge
dec-language (check S) ⟨ ⟨⟩ ↦ arity ⟩ = Right check-arity
dec-language (check S) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = Left check-none
dec-language (check S) ⟨ ⟨ s ⟩ ↦ error ⟩ = Right check-error
dec-language (check S) ⟨ ⟨ s ⟩ ↦ diverge ⟩ = Right check-diverge
dec-language (check S) ⟨ ⟨ s ⟩ ↦ arity ⟩ = Left check-arity
dec-language (check S) ⟨ ⟨ s ⟩ ↦ ⟨ t ⟩ ⟩ = mapLR check-ok check-ok (dec-language S ⟨ s ⟩)

dec-rlanguage T error = mapLR error error (dec-language T error)
dec-rlanguage T diverge = Right diverge
dec-rlanguage T ⟨ t ⟩ = mapLR one one (dec-language T ⟨ t ⟩)
dec-rlanguage T arity = Left arity

-- ¬Language T is the complement of Language T
language-comp : ∀ {T t} → ¬Language T t → ¬(Language T t)
language-comp (p₁ , p₂) (left q) = language-comp p₁ q
language-comp (p₁ , p₂) (right q) = language-comp p₂ q
language-comp (left p) (q₁ , q₂) = language-comp p q₁
language-comp (right p) (q₁ , q₂) = language-comp p q₂
language-comp (scalar-scalar s p₁ p₂) (scalar s) = p₂ refl
language-comp (function-function p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-function p₁ (error p₂)) (function-ok (error q)) = language-comp p₂ q
language-comp (function-function p₁ (one p₂)) (function-ok (one q)) = language-comp p₂ q
language-comp (check-ok p) (check-ok q) = language-comp p q
language-comp (function-none-error (error p)) (function-ok (error q)) = language-comp p q
language-comp (function-none (one p)) (function-ok (one q)) = language-comp p q
language-comp (function-arity p) (function-arity q) = language-comp q p

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
<:-function p q (function-ok (error r)) = function-ok (error (q r))
<:-function p q (function-ok diverge) = function-ok diverge
<:-function p q (function-ok (one r)) = function-ok (one (q r))
<:-function p q (function-nok r) = function-nok (<:-impl-⊇ p r)
<:-function p q (function-arity r) = function-arity (<:-impl-⊇ p r)

<:-function-∩-∩ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∩ S) ⇒ (T ∩ U))
<:-function-∩-∩ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∩ (function-nok p , q) = function-nok (left p)
<:-function-∩-∩ (p , function-nok q) = function-nok (right q)
<:-function-∩-∩ (function-ok (error p) , function-ok (error q)) = function-ok (error (p , q))
<:-function-∩-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩-∩ (function-arity p , q) = function-arity (left p)

<:-function-∩-∪ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∪ S) ⇒ (T ∪ U))
<:-function-∩-∪ (p , function-ok (error q)) = function-ok (error (right q))
<:-function-∩-∪ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∪ (p , function-ok (one q)) = function-ok (one (right q))
<:-function-∩-∪ (function-nok p , function-nok q) = function-nok (p , q)
<:-function-∩-∪ (function-ok (error p) , q) = function-ok (error (left p))
<:-function-∩-∪ (function-ok diverge , q) = function-ok diverge
<:-function-∩-∪ (function-ok (one p) , q) = function-ok (one (left p))
<:-function-∩-∪ (function-arity p , function-arity q) = function-arity (p , q)

<:-function-∩ : ∀ {S T U} → ((S ⇒ T) ∩ (S ⇒ U)) <: (S ⇒ (T ∩ U))
<:-function-∩ (function-nok p , q) = function-nok p
<:-function-∩ (p , function-nok q) = function-nok q
<:-function-∩ (function-ok (error p) , function-ok (error q)) = function-ok (error (p , q))
<:-function-∩ (function-ok diverge , q) = function-ok diverge
<:-function-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩ (function-arity p , function-arity q) = function-arity q

<:-function-∪ : ∀ {R S T U} → ((R ⇒ S) ∪ (T ⇒ U)) <: ((R ∩ T) ⇒ (S ∪ U))
<:-function-∪ (left (function-nok p)) = function-nok (left p)
<:-function-∪ (left (function-ok (error p))) = function-ok (error (left p))
<:-function-∪ (left (function-ok diverge)) = function-ok diverge
<:-function-∪ (left (function-ok (one p))) = function-ok (one (left p))
<:-function-∪ (left (function-arity p)) = function-arity (left p)
<:-function-∪ (right (function-nok p)) = function-nok (right p)
<:-function-∪ (right (function-ok (error p))) = function-ok (error (right p))
<:-function-∪ (right (function-ok diverge)) = function-ok diverge
<:-function-∪ (right (function-ok (one p))) = function-ok (one (right p))
<:-function-∪ (right (function-arity p)) = function-arity (right p)

<:-function-∪-∩ : ∀ {R S T U} → ((R ∩ S) ⇒ (T ∪ U)) <: ((R ⇒ T) ∪ (S ⇒ U))
<:-function-∪-∩ (function-nok (left p)) = left (function-nok p)
<:-function-∪-∩ (function-nok (right p)) = right (function-nok p)
<:-function-∪-∩ (function-ok (error (left p))) = left (function-ok (error p))
<:-function-∪-∩ (function-ok (error (right p))) = right (function-ok (error p))
<:-function-∪-∩ (function-ok diverge) = left (function-ok diverge)
<:-function-∪-∩ (function-ok (one (left p))) = left (function-ok (one p))
<:-function-∪-∩ (function-ok (one (right p))) = right (function-ok (one p))
<:-function-∪-∩ (function-arity (left p)) = left (function-arity p)
<:-function-∪-∩ (function-arity (right p)) = right (function-arity p)

<:-function-left : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (R <: S)
<:-function-left {R} {S} p {error} Re with <:-impl-⊇ p (function-arity Re)
<:-function-left {R} {S} p {error} Re | function-arity Se = Se
<:-function-left {R} {S} p {⟨ s ⟩} Rs with <:-impl-⊇ p (function-function Rs arity)
<:-function-left {R} {S} p {⟨ s ⟩} Rs | function-function Ss arity = Ss

<:-function-right : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (T <: U)
<:-function-right p {error} Te with p (function-ok {t = ⟨⟩} (error Te))
<:-function-right p {error} Te | function-ok (error Ue) = Ue
<:-function-right p {⟨ t ⟩} Tt with p (function-ok {t = ⟨⟩} (one Tt))
<:-function-right p {⟨ t ⟩} Tt | function-ok (one Ut) = Ut

≮:-function-left : ∀ {R S T U} → (R ≮: S) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-left (witness {error} p q) = witness {t = ⟨ ⟨⟩ ↦ arity ⟩} (function-arity q) (function-arity p)
≮:-function-left (witness {⟨ s ⟩} p q) = witness {t = ⟨ ⟨ s ⟩ ↦ arity ⟩} (function-nok q) (function-function p arity)

≮:-function-right : ∀ {R S T U} → (T ≮: U) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-right (witness {error} p q) = witness (function-ok (error p)) (function-none-error (error q))
≮:-function-right (witness {⟨ s ⟩} p q) = witness (function-ok (one p)) (function-none (one q))

function-<:-funktion : ∀ {S T} → (S ⇒ T) <: funktion
function-<:-funktion = <:-function (λ()) (λ p → any)

function-<:-unknown : ∀ {S T} → (S ⇒ T) <: unknown
function-<:-unknown p = left (left (left (left (function-<:-funktion p))))

error-≮:-function : ∀ {S T} → error ≮: (S ⇒ T)
error-≮:-function = witness error function-error

-- Properties of check functions
<:-check : ∀ {S T} → S <: T → check S <: check T
<:-check p (check-ok q) = check-ok (p q)
<:-check p check-error = check-error
<:-check p check-diverge = check-diverge
<:-check p check-arity = check-arity

<:-check-dist-∪ : ∀ {S T} → check (S ∪ T) <: (check(S) ∪ check(T))
<:-check-dist-∪ (check-ok (left p)) = left (check-ok p)
<:-check-dist-∪ (check-ok (right p)) = right (check-ok p)
<:-check-dist-∪ check-error = left check-error
<:-check-dist-∪ check-diverge = left check-diverge
<:-check-dist-∪ check-arity = left check-arity

check-dist-∪-<: : ∀ {S T} → (check(S) ∪ check(T)) <: check (S ∪ T)
check-dist-∪-<: (left (check-ok p)) = check-ok (left p)
check-dist-∪-<: (left check-error) = check-error
check-dist-∪-<: (left check-diverge) = check-diverge
check-dist-∪-<: (left check-arity) = check-arity
check-dist-∪-<: (right (check-ok p)) = check-ok (right p)
check-dist-∪-<: (right check-error) = check-error
check-dist-∪-<: (right check-diverge) = check-diverge
check-dist-∪-<: (right check-arity) = check-arity

<:-check-dist-∩ : ∀ {S T} → check (S ∩ T) <: (check(S) ∩ check(T))
<:-check-dist-∩ (check-ok (p , q)) = (check-ok p , check-ok q)
<:-check-dist-∩ check-error = (check-error , check-error)
<:-check-dist-∩ check-diverge = (check-diverge , check-diverge)
<:-check-dist-∩ check-arity = (check-arity , check-arity)

check-dist-∩-<: : ∀ {S T} → (check(S) ∩ check(T)) <: check (S ∩ T)
check-dist-∩-<: (check-ok p , check-ok q) = check-ok (p , q)
check-dist-∩-<: (check-error , q) = check-error
check-dist-∩-<: (check-diverge , q) = check-diverge
check-dist-∩-<: (check-arity , q) = check-arity


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
<:-everything {⟨ ⟨⟩ ↦ error ⟩} p = left (left (left (left (left (function-ok (error any))))))
<:-everything {⟨ ⟨⟩ ↦ diverge ⟩} p = left (left (left (left (left (function-ok diverge)))))
<:-everything {⟨ ⟨⟩ ↦ arity ⟩} p = left (left (left (left (left (function-arity never)))))
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
  S₂⊆S₁ error S₂e | Left ¬S₁e with p ⟨ ⟨⟩ ↦ arity ⟩ (function-arity ¬S₁e)
  S₂⊆S₁ error S₂e | Left ¬S₁e | function-arity ¬S₂e = CONTRADICTION (language-comp ¬S₂e S₂e)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t with p ⟨ ⟨ t ⟩ ↦ arity ⟩ (function-nok ¬S₁t)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t | function-nok ¬S₂t = CONTRADICTION (language-comp ¬S₂t S₂t)
  S₂⊆S₁ t S₂t | Right S₁t = S₁t
  
  ¬T₂⊆¬T₁ : Comp(Lift(Language T₂)) ⊆ Comp(Lift(Language T₁))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩ (function-ok (one T₁u))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u | function-ok (one T₂u) = ¬T₂u T₂u
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ error ⟩ (function-ok (error T₁u))
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u | function-ok (error T₂e) = ¬T₂u T₂e

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
  r ⟨ ⟨⟩ ↦ arity ⟩ (function-arity ¬S₁e) = function-arity (¬S₁⊆¬S₂ error ¬S₁e)
  r ⟨ ⟨ s ⟩ ↦ t ⟩ (function-nok ¬S₁s) = function-nok (¬S₁⊆¬S₂ ⟨ s ⟩ ¬S₁s)
  r ⟨ s ↦ ⟨ t ⟩ ⟩ (function-ok (one T₁t)) = function-ok (one (T₁⊆T₂ ⟨ t ⟩ T₁t))
  r ⟨ s ↦ error ⟩ (function-ok (error T₁e)) = function-ok (error (T₁⊆T₂ error T₁e))
  r ⟨ s ↦ diverge ⟩ p = function-ok diverge

-- A counterexample when the argument type is empty.

set-theoretic-counterexample-one : (∀ Q → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language number))) → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language string))))
set-theoretic-counterexample-one Q q (⟨ scalar s ⟩ , u) Qtu (() , p)

set-theoretic-counterexample-two : (never ⇒ number) ≮: (never ⇒ string)
set-theoretic-counterexample-two = witness (function-ok (one (scalar NUMBER)))
                                     (function-none (one (scalar-scalar NUMBER STRING (λ ())))) -- witness (function-ok (one (scalar NUMBER)))
                                     -- (function-function none (one (scalar-scalar NUMBER STRING (λ ()))))
