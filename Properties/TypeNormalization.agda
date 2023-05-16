{-# OPTIONS --rewriting #-}

module Properties.TypeNormalization where

open import Agda.Builtin.Equality using (refl)
open import Luau.Type using (Type; Scalar; nill; number; string; boolean; error; never; any; unknown; scalar; check; function; _⇒_; _∪_; _∩_; _\\_; ⌊_⌋; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_; _≡ᵀ_)
open import Luau.Subtyping using (Language; ¬Language; scalar; any; left; right; function-ok; function-error; function-nok; scalar-function; function-scalar; function-none; _,_; _↦_; ⟨⟩; ⟨_⟩; error; diverge; untyped)
open import Luau.TypeNormalization using (_∪ⁿ_; _∩ⁿ_; _∪ᶠ_; _∪ⁿˢ_; _∩ⁿˢ_; normalize)
open import Luau.Subtyping using (_<:_; _≮:_; witness; never)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Subtyping using (<:-trans; <:-refl; <:-any; <:-never; <:-∪-left; <:-∪-right; <:-∪-lub; <:-∩-left; <:-∩-right; <:-∩-glb; <:-∩-symm; <:-∩-assocl; <:-∩-assocr; <:-function; <:-function-∪-∩; <:-function-∩-∪; <:-function-∪; <:-everything; <:-union; <:-∪-assocl; <:-∪-assocr; <:-∪-symm; <:-intersect;  ∪-distl-∩-<:; ∪-distr-∩-<:; <:-∪-distr-∩; <:-∪-distl-∩; ∩-distl-∪-<:; <:-∩-distl-∪; <:-∩-distr-∪; ∩-distr-∪-<:; function-∩-scalar-<:-never; function-∩-error-<:-never; error-∩-scalar-<:-never; scalar-∩-error-<:-never; scalar-≢-∩-<:-never; <:-check-dist-∪; check-dist-∪-<:; <:-check-dist-∩; check-dist-∩-<:; <:-check; check-<:-function; function-∪-check-<:; <:-function-∪-check; <:-function-∩-check)

data ErrScalar : Type → Set where
  error : ErrScalar error
  scalar : ∀ S → ErrScalar (scalar S)

data AnyCheck : Type → Set where
  any : AnyCheck(any)
  check : ∀ T → AnyCheck(check T)

data Check : Type → Set where
  check : ∀ T → Check(check T)

-- Normal forms for types
data FunType : Type → Set
data Normal : Type → Set

data FunType where
  _⇒_ : ∀ S T → FunType (S ⇒ T)
  _∩_ : ∀ {F G} → FunType F → FunType G → FunType (F ∩ G)

data Normal where
  _∩_ : ∀ {F G} → FunType F → AnyCheck G → Normal (F ∩ G)
  _∪_ : ∀ {S T} → Normal S → ErrScalar T → Normal (S ∪ T)
  never : Normal never

data OptScalar : Type → Set where
  never : OptScalar never
  error : OptScalar error
  scalar : ∀ S → OptScalar (scalar S)

-- Top function type
fun-top : ∀ {F} → (FunType F) → (F <: (never ⇒ any))
fun-top (S ⇒ T) = <:-function <:-never <:-any
fun-top (F ∩ G) = <:-trans <:-∩-left (fun-top F)

-- function types are inhabited
fun-function : ∀ {F} → FunType F → Language F (⟨⟩ ↦ diverge)
fun-function (S ⇒ T) = function-ok diverge
fun-function (F ∩ G) = (fun-function F , fun-function G)

fun-≮:-never : ∀ {F} → FunType F → (F ≮: never)
fun-≮:-never F = witness (fun-function F) never

-- function types aren't scalars
fun-¬scalar : ∀ S {F t} → FunType F → Language F t → ¬Language (scalar S) t
fun-¬scalar s (S ⇒ T) (function-nok p) = scalar-function s
fun-¬scalar s (S ⇒ T) (function-ok p) = scalar-function s
fun-¬scalar s (S ⇒ T) function-none = scalar-function s
fun-¬scalar s (F ∩ G) (p , q) = fun-¬scalar s G q

¬scalar-fun : ∀ {F} → FunType F → ∀ S → ¬Language F (scalar S)
¬scalar-fun (S ⇒ T) s = function-scalar s
¬scalar-fun (F ∩ G) s = left (¬scalar-fun F s)

scalar-≮:-fun : ∀ {F} → FunType F → ∀ S → scalar S ≮: F
scalar-≮:-fun F s = witness (scalar s) (¬scalar-fun F s)

fun-≮:-scalar : ∀ {F} → FunType F → ∀ S → F ≮: scalar S
fun-≮:-scalar F s = witness (fun-function F) (scalar-function s)

-- function types aren't errors
fun-¬error : ∀ {F t} → FunType F → Language F t → ¬Language error t
fun-¬error (S ⇒ T) (function-nok p) = error (λ ())
fun-¬error (S ⇒ T) (function-ok p) = error (λ ())
fun-¬error (S ⇒ T) function-none = error (λ ())
fun-¬error (F ∩ G) (p , q) = fun-¬error G q

¬error-fun : ∀ {F} → FunType F → ¬Language F untyped
¬error-fun (S ⇒ T) = function-error
¬error-fun (F ∩ G) = left (¬error-fun F)

error-≮:-fun : ∀ {F} → FunType F → error ≮: F
error-≮:-fun F = witness error (¬error-fun F)

-- unknown is normal
normal-unknown : Normal unknown
normal-unknown = (((((never ⇒ any) ∩ any) ∪ (scalar NUMBER)) ∪ (scalar STRING)) ∪ (scalar NIL)) ∪ (scalar BOOLEAN)

-- Normalization produces normal types
normal : ∀ T → Normal (normalize T)
normal-∪ⁿ : ∀ {S T} → Normal S → Normal T → Normal (S ∪ⁿ T)
normal-∩ⁿ : ∀ {S T} → Normal S → Normal T → Normal (S ∩ⁿ T)
normal-∪ⁿˢ : ∀ {S T} → Normal S → OptScalar T → Normal (S ∪ⁿˢ T)
normal-∩ⁿˢ : ∀ {S T} → Normal S → ErrScalar T → OptScalar (S ∩ⁿˢ T)
normal-∪ᶠ : ∀ {F G} → FunType F → FunType G → FunType (F ∪ᶠ G)
normal-∪ᶠᶜ : ∀ {F T} → FunType F → Check T → FunType (F ∪ᶠ T)
normal-∪ᶜᶠ : ∀ {S G} → Check S → FunType G → FunType (S ∪ᶠ G)

normal (scalar S) = never ∪ scalar S
normal (S ⇒ T) = (S ⇒ T) ∩ any
normal (check S) = (never ⇒ any) ∩ (check S)
normal never = never
normal any = normal-unknown ∪ error
normal error = never ∪ error
normal (S ∪ T) = normal-∪ⁿ (normal S) (normal T)
normal (S ∩ T) = normal-∩ⁿ (normal S) (normal T)

normal-∪ⁿ S (T₁ ∪ T₂) = (normal-∪ⁿ S T₁) ∪ T₂
normal-∪ⁿ S never = S
normal-∪ⁿ never (G₁ ∩ G₂) = G₁ ∩ G₂
normal-∪ⁿ (F ∩ any) (G ∩ any) = (normal-∪ᶠ F G) ∩ any
normal-∪ⁿ (F ∩ any) (G ∩ check T) = ((normal-∪ᶠ F G) ∩ (normal-∪ᶠᶜ F (check T))) ∩ any
normal-∪ⁿ (F ∩ check S) (G ∩ any) = ((normal-∪ᶠ F G) ∩ (normal-∪ᶜᶠ (check S) G)) ∩ any
normal-∪ⁿ (F ∩ check S) (G ∩ check T) = ((normal-∪ᶠ F G ∩ normal-∪ᶠᶜ F (check T)) ∩ normal-∪ᶜᶠ (check S) G) ∩ check (S ∪ T)
normal-∪ⁿ (S₁ ∪ S₂) (G₁ ∩ G₂) = normal-∪ⁿ S₁ (G₁ ∩ G₂) ∪ S₂

normal-∩ⁿ S never = never
normal-∩ⁿ S (T ∪ U) = normal-∪ⁿˢ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U )
normal-∩ⁿ never (T ∩ U) = never
normal-∩ⁿ (R ∪ S) (G ∩ T) = normal-∩ⁿ R (G ∩ T)
normal-∩ⁿ (F ∩ any) (G ∩ any) = (F ∩ G) ∩ any
normal-∩ⁿ (F ∩ any) (G ∩ check T) = (F ∩ G) ∩ check T
normal-∩ⁿ (F ∩ check S) (G ∩ any) = (F ∩ G) ∩ check S
normal-∩ⁿ (F ∩ check S) (G ∩ check T) = (F ∩ G) ∩ check (S ∩ T)

normal-∪ⁿˢ S never = S
normal-∪ⁿˢ never (scalar T) = never ∪ (scalar T)
normal-∪ⁿˢ (R ∩ S) (scalar T) = (R ∩ S) ∪ (scalar T)
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = R ∪ scalar S
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) | no p = normal-∪ⁿˢ R (scalar T) ∪ scalar S
normal-∪ⁿˢ (R ∪ error) (scalar T) = normal-∪ⁿˢ R (scalar T) ∪ error
normal-∪ⁿˢ (F ∩ G) error = (F ∩ G) ∪ error
normal-∪ⁿˢ (R ∪ error) error = R ∪ error
normal-∪ⁿˢ (R ∪ scalar S) error = normal-∪ⁿˢ R error ∪ scalar S
normal-∪ⁿˢ never error = never ∪ error

normal-∩ⁿˢ never (scalar T) = never
normal-∩ⁿˢ never error = never
normal-∩ⁿˢ (R ∩ S) (scalar T) = never
normal-∩ⁿˢ (R ∩ S) error = never
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = scalar S
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) | no p = normal-∩ⁿˢ R (scalar T)
normal-∩ⁿˢ (R ∪ error) error = error
normal-∩ⁿˢ (R ∪ error) (scalar T) = normal-∩ⁿˢ R (scalar T)
normal-∩ⁿˢ (R ∪ scalar S) error = normal-∩ⁿˢ R error

normal-∪ᶠ (R ⇒ S) (T ⇒ U) = (R ∩ T) ⇒ (S ∪ U)
normal-∪ᶠ (R ⇒ S) (G ∩ H) = normal-∪ᶠ (R ⇒ S) G ∩ normal-∪ᶠ (R ⇒ S) H
normal-∪ᶠ (E ∩ F) G = normal-∪ᶠ E G ∩ normal-∪ᶠ F G

normal-∪ᶠᶜ (R ⇒ S) (check T) = (R \\ T) ⇒ S
normal-∪ᶠᶜ (F ∩ G) (check T) = normal-∪ᶠᶜ F (check T) ∩ normal-∪ᶠᶜ G (check T)

normal-∪ᶜᶠ (check S) (T ⇒ U) = (T \\ S) ⇒ U
normal-∪ᶜᶠ (check S) (G ∩ H) = normal-∪ᶜᶠ (check S) G ∩ normal-∪ᶜᶠ (check S) H

fun-∩-scalar-<:-never : ∀ {F} → FunType F → ∀ S {V} → (F ∩ scalar S) <: V
fun-∩-scalar-<:-never (T ⇒ U) S = function-∩-scalar-<:-never S
fun-∩-scalar-<:-never (F ∩ G) S = <:-trans (<:-intersect <:-∩-left <:-refl) (fun-∩-scalar-<:-never F S)

fun-∩-error-<:-never : ∀ {F} → FunType F → ∀ {V} → (F ∩ error) <: V
fun-∩-error-<:-never (T ⇒ U) = function-∩-error-<:-never
fun-∩-error-<:-never (F ∩ G) = <:-trans (<:-intersect <:-∩-left <:-refl) (fun-∩-error-<:-never F)

fun-∩-errscalar-<:-never : ∀ {F} → FunType F → ∀ {S} → ErrScalar S → ∀ {V} → (F ∩ S) <: V
fun-∩-errscalar-<:-never F error = fun-∩-error-<:-never F
fun-∩-errscalar-<:-never F (scalar S) = fun-∩-scalar-<:-never F S

<:-fun-∩-check : ∀ {S F} → (FunType F) → ((F ∪ (⌊ S ⌋ ⇒ never)) ∩ (check S)) <: (F ∩ (check S))
<:-fun-∩-check (S ⇒ T) = <:-function-∩-check
<:-fun-∩-check {S} (F ∩ G) = <:-trans (<:-∩-glb (<:-intersect (<:-union <:-∩-left <:-refl) <:-refl) (<:-intersect (<:-union <:-∩-right <:-refl) <:-refl))
  (<:-trans (<:-intersect (<:-fun-∩-check {S} F) (<:-fun-∩-check {S} G))
    (<:-∩-glb (<:-intersect <:-∩-left <:-∩-left) (<:-trans <:-∩-right <:-∩-right)))

flipper : ∀ {S T U} → ((S ∪ T) ∪ U) <: ((S ∪ U) ∪ T)
flipper = <:-trans <:-∪-assocr (<:-trans (<:-union <:-refl <:-∪-symm) <:-∪-assocl)

∩-<:-∩ⁿ :  ∀ {S T} → Normal S → Normal T → (S ∩ T) <: (S ∩ⁿ T)
∩ⁿ-<:-∩ :  ∀ {S T} → Normal S → Normal T → (S ∩ⁿ T) <: (S ∩ T)
∩-<:-∩ⁿˢ :  ∀ {S T} → Normal S → ErrScalar T → (S ∩ T) <: (S ∩ⁿˢ T)
∩ⁿˢ-<:-∩ :  ∀ {S T} → Normal S → ErrScalar T → (S ∩ⁿˢ T) <: (S ∩ T)
∪ᶠ-<:-∪ : ∀ {F G} → FunType F → FunType G → (F ∪ᶠ G) <: (F ∪ G)
∪ⁿ-<:-∪ : ∀ {S T} → Normal S → Normal T → (S ∪ⁿ T) <: (S ∪ T)
∪-<:-∪ⁿ : ∀ {S T} → Normal S → Normal T → (S ∪ T) <: (S ∪ⁿ T)
∪ⁿˢ-<:-∪ : ∀ {S T} → Normal S → OptScalar T → (S ∪ⁿˢ T) <: (S ∪ T)
∪-<:-∪ⁿˢ : ∀ {S T} → Normal S → OptScalar T → (S ∪ T) <: (S ∪ⁿˢ T)
∪ᶜᶠ-<:-∪ : ∀ {S G} → Check S → FunType G → (S ∪ᶠ G) <: (S ∪ G)
∪ᶠᶜ-<:-∪ : ∀ {F T} → FunType F → Check T → (F ∪ᶠ T) <: (F ∪ T)
∪-<:-∪ᶜᶠ : ∀ {S G} → Check S → FunType G → (S ∪ G) <: (S ∪ᶠ G)
∪-<:-∪ᶠᶜ : ∀ {F T} → FunType F → Check T →  (F ∪ T) <: (F ∪ᶠ T)

∩-<:-∩ⁿ S never = <:-∩-right
∩-<:-∩ⁿ S (T ∪ U) = <:-trans <:-∩-distl-∪ (<:-trans (<:-union (∩-<:-∩ⁿ S T) (∩-<:-∩ⁿˢ S U)) (∪-<:-∪ⁿˢ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U)) )
∩-<:-∩ⁿ never (T ∩ U) = <:-∩-left
∩-<:-∩ⁿ (F ∩ any) (G ∩ T) = <:-∩-glb (<:-intersect <:-∩-left <:-∩-left) (<:-trans <:-∩-right <:-∩-right)
∩-<:-∩ⁿ (F ∩ check S) (G ∩ any) = <:-∩-glb (<:-intersect <:-∩-left <:-∩-left) (<:-trans <:-∩-left <:-∩-right)
∩-<:-∩ⁿ (F ∩ check S) (G ∩ check T) = <:-∩-glb (<:-intersect <:-∩-left <:-∩-left) (<:-trans (<:-intersect <:-∩-right <:-∩-right) check-dist-∩-<:)
∩-<:-∩ⁿ (R ∪ S) (G ∩ T) = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿ R (G ∩ T)) (<:-trans <:-∩-assocl (<:-trans <:-∩-left (<:-trans <:-∩-symm (fun-∩-errscalar-<:-never G S)))))

∩ⁿ-<:-∩ S never = <:-never
∩ⁿ-<:-∩ S (T ∪ U) = <:-trans (∪ⁿˢ-<:-∪ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U)) (<:-trans (<:-union (∩ⁿ-<:-∩ S T) (∩ⁿˢ-<:-∩ S U)) ∩-distl-∪-<:)
∩ⁿ-<:-∩ never (T ∩ U) = <:-never
∩ⁿ-<:-∩ (F ∩ any) (G ∩ T) = <:-∩-glb (<:-∩-glb (<:-trans <:-∩-left <:-∩-left) <:-any) (<:-∩-glb (<:-trans <:-∩-left <:-∩-right) <:-∩-right)
∩ⁿ-<:-∩ (F ∩ check S) (G ∩ any) = <:-∩-glb (<:-intersect <:-∩-left <:-refl) (<:-intersect <:-∩-right <:-any)
∩ⁿ-<:-∩ (F ∩ check S) (G ∩ check T) = <:-trans (<:-intersect <:-refl <:-check-dist-∩) (<:-∩-glb (<:-intersect <:-∩-left <:-∩-left) (<:-intersect <:-∩-right <:-∩-right))
∩ⁿ-<:-∩ (R ∪ S) (G ∩ T) = <:-trans (∩ⁿ-<:-∩ R (G ∩ T)) (<:-intersect <:-∪-left <:-refl)

∩-<:-∩ⁿˢ never (scalar T) = <:-∩-left
∩-<:-∩ⁿˢ never error = <:-∩-left
∩-<:-∩ⁿˢ (F ∩ S) T = <:-trans (<:-intersect <:-∩-left <:-refl) (fun-∩-errscalar-<:-never F T)
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = <:-∩-right
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) | no p = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R (scalar T)) (scalar-≢-∩-<:-never S T p))
∩-<:-∩ⁿˢ (R ∪ error) error = <:-∩-right
∩-<:-∩ⁿˢ (R ∪ error) (scalar T) = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R (scalar T)) (error-∩-scalar-<:-never T))
∩-<:-∩ⁿˢ (R ∪ scalar S) error = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R error) (scalar-∩-error-<:-never S))

∩ⁿˢ-<:-∩ never T = <:-never
∩ⁿˢ-<:-∩ (F ∩ G) T = <:-never
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) | yes refl = <:-∩-glb <:-∪-right <:-refl
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) | no p = <:-trans (∩ⁿˢ-<:-∩ R (scalar T)) (<:-intersect <:-∪-left <:-refl)
∩ⁿˢ-<:-∩ (R ∪ scalar S) error = <:-trans (∩ⁿˢ-<:-∩ R error) (<:-intersect <:-∪-left <:-refl)
∩ⁿˢ-<:-∩ (R ∪ error) error = <:-∩-glb <:-∪-right <:-refl
∩ⁿˢ-<:-∩ (R ∪ error) (scalar S) = <:-trans (∩ⁿˢ-<:-∩ R (scalar S)) (<:-intersect <:-∪-left <:-refl)

∪ᶠ-<:-∪ (R ⇒ S) (T ⇒ U) = <:-function-∪-∩
∪ᶠ-<:-∪ (R ⇒ S) (G ∩ H) = <:-trans (<:-intersect (∪ᶠ-<:-∪ (R ⇒ S) G) (∪ᶠ-<:-∪ (R ⇒ S) H)) ∪-distl-∩-<:
∪ᶠ-<:-∪ (E ∩ F) G = <:-trans (<:-intersect (∪ᶠ-<:-∪ E G) (∪ᶠ-<:-∪ F G)) ∪-distr-∩-<:

∪-<:-∪ᶠ : ∀ {F G} → FunType F → FunType G → (F ∪ G) <: (F ∪ᶠ G)
∪-<:-∪ᶠ (R ⇒ S) (T ⇒ U) = <:-function-∪
∪-<:-∪ᶠ (R ⇒ S) (G ∩ H) = <:-trans <:-∪-distl-∩ (<:-intersect (∪-<:-∪ᶠ (R ⇒ S) G) (∪-<:-∪ᶠ (R ⇒ S) H))
∪-<:-∪ᶠ (E ∩ F) G = <:-trans <:-∪-distr-∩ (<:-intersect (∪-<:-∪ᶠ E G) (∪-<:-∪ᶠ F G))

∪ⁿˢ-<:-∪ S never = <:-∪-left
∪ⁿˢ-<:-∪ never (scalar T) = <:-refl
∪ⁿˢ-<:-∪ never error = <:-refl
∪ⁿˢ-<:-∪ (R ∩ S) (scalar T) = <:-refl
∪ⁿˢ-<:-∪ (R ∩ S) error = <:-refl
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) | yes refl = <:-∪-left
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) | no p = <:-trans (<:-union (∪ⁿˢ-<:-∪ R (scalar T)) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ scalar S) error = <:-trans (<:-union (∪ⁿˢ-<:-∪ R error) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ error) (scalar T) = <:-trans (<:-union (∪ⁿˢ-<:-∪ R (scalar T)) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ error) error = <:-∪-left

∪-<:-∪ⁿˢ T never = <:-∪-lub <:-refl <:-never
∪-<:-∪ⁿˢ never (scalar T) = <:-refl
∪-<:-∪ⁿˢ never error = <:-refl
∪-<:-∪ⁿˢ (R ∩ S) (scalar T) = <:-refl
∪-<:-∪ⁿˢ (R ∩ S) error = <:-refl
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = <:-∪-lub <:-refl <:-∪-right
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) | no p = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R (scalar T)) <:-refl)
∪-<:-∪ⁿˢ (R ∪ scalar S) error = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R error) <:-refl)
∪-<:-∪ⁿˢ (R ∪ error) (scalar T) = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R (scalar T)) <:-refl)
∪-<:-∪ⁿˢ (R ∪ error) error = <:-∪-lub <:-refl <:-∪-right

∪ⁿ-<:-∪ S never = <:-∪-left
∪ⁿ-<:-∪ never (G ∩ T) = <:-∪-right
∪ⁿ-<:-∪ (F ∩ any) (G ∩ any) = <:-trans (<:-intersect (∪ᶠ-<:-∪ F G) <:-refl) (<:-trans <:-∩-distr-∪ (<:-union (<:-∩-glb <:-∩-left <:-any) <:-refl))
∪ⁿ-<:-∪ (F ∩ any) (G ∩ check T) = <:-trans <:-∩-left (<:-trans (<:-intersect (∪ᶠ-<:-∪ F G) (∪ᶠᶜ-<:-∪ F (check T))) (<:-trans ∪-distl-∩-<: (<:-union (<:-∩-glb <:-refl <:-any) <:-refl)))
∪ⁿ-<:-∪ (F ∩ check S) (G ∩ any) = <:-trans <:-∩-left (<:-trans (<:-intersect (∪ᶠ-<:-∪ F G) (∪ᶜᶠ-<:-∪ (check S) G)) (<:-trans ∪-distr-∩-<: (<:-union <:-refl (<:-∩-glb <:-refl <:-any))))
∪ⁿ-<:-∪ (F ∩ check S) (G ∩ check T) = <:-trans (<:-intersect (<:-intersect (<:-intersect (∪ᶠ-<:-∪ F G) (∪ᶠᶜ-<:-∪ F (check T))) (∪ᶜᶠ-<:-∪ (check S) G)) <:-check-dist-∪)
  (<:-trans <:-∩-assocr (<:-trans (<:-intersect ∪-distl-∩-<: ∪-distl-∩-<:) ∪-distr-∩-<:))
∪ⁿ-<:-∪ (R ∪ S) (G ∩ T) = <:-trans (<:-union (∪ⁿ-<:-∪ R (G ∩ T)) <:-refl) (<:-∪-lub (<:-∪-lub (<:-trans <:-∪-left <:-∪-left) <:-∪-right) (<:-trans <:-∪-right <:-∪-left))
∪ⁿ-<:-∪ S (T ∪ U) = <:-∪-lub (<:-trans (∪ⁿ-<:-∪ S T) (<:-union <:-refl <:-∪-left)) (<:-trans <:-∪-right <:-∪-right)

∪-<:-∪ⁿ S never = <:-∪-lub <:-refl <:-never
∪-<:-∪ⁿ never (T ∩ U) = <:-∪-lub <:-never <:-refl
∪-<:-∪ⁿ (F ∩ any) (G ∩ any) = <:-trans (<:-union <:-∩-left <:-∩-left) (<:-∩-glb (∪-<:-∪ᶠ F G) <:-any)
∪-<:-∪ⁿ (F ∩ any) (G ∩ check T) = <:-trans (<:-union <:-∩-left <:-refl) (<:-trans <:-∪-distl-∩ (<:-∩-glb (<:-intersect (∪-<:-∪ᶠ F G) (∪-<:-∪ᶠᶜ F (check T))) <:-any))
∪-<:-∪ⁿ (F ∩ check S) (G ∩ any) = <:-trans (<:-union <:-refl <:-∩-left) (<:-trans <:-∪-distr-∩ (<:-∩-glb (<:-intersect (∪-<:-∪ᶠ F G) (∪-<:-∪ᶜᶠ (check S) G)) <:-any))
∪-<:-∪ⁿ (F ∩ check S) (G ∩ check T) = <:-trans <:-∪-distr-∩ (<:-trans (<:-intersect <:-∪-distl-∩  <:-∪-distl-∩) (<:-trans <:-∩-assocl
  (<:-intersect (<:-intersect (<:-intersect (∪-<:-∪ᶠ F G) (∪-<:-∪ᶠᶜ F (check T))) (∪-<:-∪ᶜᶠ (check S) G)) check-dist-∪-<:)))
∪-<:-∪ⁿ (R ∪ S) (G ∩ T) = <:-trans <:-∪-assocr (<:-trans (<:-union <:-refl <:-∪-symm) (<:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ R (G ∩ T)) <:-refl)))
∪-<:-∪ⁿ never (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ never T) <:-refl)
∪-<:-∪ⁿ (F ∩ S) (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ (F ∩ S) T) <:-refl)
∪-<:-∪ⁿ (R ∪ S) (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ (R ∪ S) T) <:-refl)

∪ᶜᶠ-<:-∪ (check S) (T ⇒ U) = function-∪-check-<:
∪ᶜᶠ-<:-∪ (check S) (G ∩ H) = <:-trans (<:-intersect (∪ᶜᶠ-<:-∪ (check S) G) (∪ᶜᶠ-<:-∪ (check S) H)) ∪-distl-∩-<:

∪ᶠᶜ-<:-∪ (R ⇒ S) (check T) = <:-trans function-∪-check-<: <:-∪-symm
∪ᶠᶜ-<:-∪ (E ∩ F) (check T) = <:-trans (<:-intersect (∪ᶠᶜ-<:-∪ E (check T)) (∪ᶠᶜ-<:-∪ F (check T))) ∪-distr-∩-<:

∪-<:-∪ᶜᶠ (check S) (T ⇒ U) = <:-function-∪-check
∪-<:-∪ᶜᶠ (check S) (G ∩ H) = <:-trans <:-∪-distl-∩ (<:-intersect (∪-<:-∪ᶜᶠ (check S) G) (∪-<:-∪ᶜᶠ (check S) H))

∪-<:-∪ᶠᶜ (R ⇒ S) (check T) = <:-trans <:-∪-symm <:-function-∪-check
∪-<:-∪ᶠᶜ (E ∩ F) (check T) = <:-trans <:-∪-distr-∩ (<:-intersect (∪-<:-∪ᶠᶜ E (check T)) (∪-<:-∪ᶠᶜ F (check T)))

normalize-<: : ∀ T → normalize T <: T
<:-normalize : ∀ T → T <: normalize T

<:-normalize (scalar T) = <:-∪-right
<:-normalize error = <:-∪-right
<:-normalize (S ⇒ T) = <:-∩-glb <:-refl <:-any
<:-normalize (check S) = <:-∩-glb check-<:-function <:-refl 
<:-normalize never = <:-refl
<:-normalize any = <:-everything
<:-normalize (S ∪ T) = <:-trans (<:-union (<:-normalize S) (<:-normalize T)) (∪-<:-∪ⁿ (normal S) (normal T))
<:-normalize (S ∩ T) = <:-trans (<:-intersect (<:-normalize S) (<:-normalize T)) (∩-<:-∩ⁿ (normal S) (normal T))

normalize-<: (scalar T) = <:-∪-lub <:-never <:-refl
normalize-<: error = <:-∪-lub <:-never <:-refl
normalize-<: (S ⇒ T) = <:-∩-left 
normalize-<: (check S) = <:-∩-right 
normalize-<: never = <:-refl
normalize-<: any = <:-any
normalize-<: (S ∪ T) = <:-trans (∪ⁿ-<:-∪ (normal S) (normal T)) (<:-union (normalize-<: S) (normalize-<: T))
normalize-<: (S ∩ T) = <:-trans (∩ⁿ-<:-∩ (normal S) (normal T)) (<:-intersect (normalize-<: S) (normalize-<: T))


