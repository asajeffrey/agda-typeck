{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nill; number; string; boolean; scalar; error; never; any; check; _⇒_; _∪_; _∩_; ⌊_⌋)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data Value : Set
data Arguments : Set
data Result : Set

data Value where

  scalar : Scalar → Value
  _↦_ : (s : Arguments) → (t : Result) → Value
  untyped : Value
  
data Arguments where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : Arguments
  ⟨_⟩ : Value → Arguments

data Result where

  diverge : Result
  error : Result
  ⟨_⟩ : Value → Result

data Language : Type → Value → Set
data ¬Language : Type → Value → Set
data RLanguage : Type → Result → Set
data ¬RLanguage : Type → Result → Set

data Language where

  scalar : ∀ T → Language (scalar T) (scalar T)
  function-nok : ∀ {T U t u} → (¬Language T t) → Language (T ⇒ U) (⟨ t ⟩ ↦ u)
  function-ok : ∀ {T U t u} → (RLanguage U u) → Language (T ⇒ U) (t ↦ u)
  function-none : ∀ {T U} → Language (T ⇒ U) (⟨⟩ ↦ error)
  check-ok : ∀ {T t u} → (Language ⌊ T ⌋ t) → Language (check T) (⟨ t ⟩ ↦ u)
  check-nok : ∀ {T t} → Language (check T) (t ↦ diverge)
  left : ∀ {T U t} → Language T t → Language (T ∪ U) t
  right : ∀ {T U u} → Language U u → Language (T ∪ U) u
  _,_ : ∀ {T U t} → Language T t → Language U t → Language (T ∩ U) t
  any : ∀ {t} → Language any t
  error : Language error untyped

data ¬Language where

  scalar-scalar : ∀ S T → (S ≢ T) → ¬Language (scalar T) (scalar S)
  scalar-function : ∀ S {t u} → ¬Language (scalar S) (t ↦ u)
  scalar-error : ∀ S → ¬Language (scalar S) untyped
  function-scalar : ∀ S {T U} → ¬Language (T ⇒ U) (scalar S)
  function-error : ∀ {T U} → ¬Language (T ⇒ U) untyped
  function-one : ∀ {T U t u} → (Language T t) → (¬RLanguage U u) → ¬Language (T ⇒ U) (⟨ t ⟩ ↦ u)
  function-none : ∀ {T U u} → (¬Language U u) → ¬Language (T ⇒ U) (⟨⟩ ↦ ⟨ u ⟩)
  check-scalar : ∀ {S T} → ¬Language (check T) (scalar S)
  check-error : ∀ {T} → ¬Language (check T) untyped
  check-one : ∀ {T t u} → (u ≢ diverge) → (¬Language ⌊ T ⌋ t) → ¬Language (check T) (⟨ t ⟩ ↦ u)
  check-none : ∀ {T u} → (u ≢ diverge) → ¬Language (check T) (⟨⟩ ↦ u)
  _,_ : ∀ {T U t} → ¬Language T t → ¬Language U t → ¬Language (T ∪ U) t
  left : ∀ {T U t} → ¬Language T t → ¬Language (T ∩ U) t
  right : ∀ {T U u} → ¬Language U u → ¬Language (T ∩ U) u
  never : ∀ {t} → ¬Language never t
  error : ∀ {t} → (t ≢ untyped) → ¬Language error t

data RLanguage where

  diverge : ∀ {T} → RLanguage T diverge
  one : ∀ {T t} → Language T t → RLanguage T ⟨ t ⟩

data ¬RLanguage where

  error : ∀ {T} → ¬RLanguage T error
  one : ∀ {T t} → ¬Language T t → ¬RLanguage T ⟨ t ⟩

-- Subtyping as language inclusion

_<:_ : Type → Type → Set
(T <: U) = ∀ {t} → (Language T t) → (Language U t)

-- For warnings, we are interested in failures of subtyping,
-- which is when there is a tree in T's language that isn't in U's.

data _≮:_ (T U : Type) : Set where

  witness : ∀ {t} →

    Language T t →
    ¬Language U t →
    -----------------
    T ≮: U
