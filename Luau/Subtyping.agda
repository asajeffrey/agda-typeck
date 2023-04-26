{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nill; number; string; boolean; scalar; error; never; any; check; _⇒_; _∪_; _∩_)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data TypedValue : Set
data Arguments : Set
data Result : Set
data Value : Set

data TypedValue where

  scalar : Scalar → TypedValue
  _↦_ : Arguments → Result → TypedValue

data Arguments where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : Arguments
  ⟨_⟩ : TypedValue → Arguments

data Result where

  -- The effects we're tracking are causing a runtime error, a "too few arguments" error,
  -- or diverging
  error : Result
  diverge : Result
  arity : Result
  ⟨_⟩ : TypedValue → Result

data Value where

  error : Value
  ⟨_⟩ : TypedValue → Value

data Language : Type → Value → Set
data ¬Language : Type → Value → Set
data RLanguage : Type → Result → Set
data ¬RLanguage : Type → Result → Set

data Language where

  scalar : ∀ T → Language (scalar T) ⟨ scalar T ⟩
  function-nok : ∀ {T U t u} → (¬Language T ⟨ t ⟩) → Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ u ⟩
  function-ok : ∀ {T U t u} → (RLanguage U u) → Language (T ⇒ U) ⟨ t ↦ u ⟩
  function-arity : ∀ {T U} → ¬Language T error → Language (T ⇒ U) ⟨ ⟨⟩ ↦ arity ⟩
  check-ok : ∀ {T t u} → (Language T ⟨ t ⟩) → Language (check T) ⟨ ⟨ t ⟩ ↦ ⟨ u ⟩ ⟩
  check-error : ∀ {T t} → Language (check T) ⟨ ⟨ t ⟩ ↦ error ⟩
  check-diverge : ∀ {T t} → Language (check T) ⟨ ⟨ t ⟩ ↦ diverge ⟩
  check-arity : ∀ {T} → Language (check T) ⟨ ⟨⟩ ↦ arity ⟩
  left : ∀ {T U t} → Language T t → Language (T ∪ U) t
  right : ∀ {T U u} → Language U u → Language (T ∪ U) u
  _,_ : ∀ {T U t} → Language T t → Language U t → Language (T ∩ U) t
  any : ∀ {t} → Language any t
  error : Language error error

data ¬Language where

  scalar-scalar : ∀ S T → (S ≢ T) → ¬Language (scalar T) ⟨ scalar S ⟩
  scalar-function : ∀ S {t u} → ¬Language (scalar S) ⟨ t ↦ u ⟩
  scalar-error : ∀ S → ¬Language (scalar S) error
  function-scalar : ∀ S {T U} → ¬Language (T ⇒ U) ⟨ scalar S ⟩
  function-function : ∀ {T U t u} → (Language T ⟨ t ⟩) → (¬RLanguage U u) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ u ⟩
  function-none : ∀ {T U t} → (¬RLanguage U ⟨ t ⟩) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩
  function-none-error : ∀ {T U} → (¬RLanguage U error) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ error ⟩
  function-arity : ∀ {T U} → Language T error → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ arity ⟩
  function-error : ∀ {T U} → ¬Language (T ⇒ U) error
  check-scalar : ∀ {S T} → ¬Language (check T) ⟨ scalar S ⟩
  check-error : ∀ {T} → ¬Language (check T) error
  check-ok : ∀ {T t u} → (¬Language T ⟨ t ⟩) → ¬Language (check T) ⟨ ⟨ t ⟩ ↦ ⟨ u ⟩ ⟩
  check-nok : ∀ {T} → ¬Language (check T) ⟨ ⟨⟩ ↦ error ⟩
  check-diverge : ∀ {T} → ¬Language (check T) ⟨ ⟨⟩ ↦ diverge ⟩
  check-arity : ∀ {T t} → ¬Language (check T) ⟨ ⟨ t ⟩ ↦ arity ⟩
  check-none : ∀ {T t} → ¬Language (check T) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩
  check-none-error : ∀ {T} → ¬Language (check T) ⟨ ⟨⟩ ↦ error ⟩
  _,_ : ∀ {T U t} → ¬Language T t → ¬Language U t → ¬Language (T ∪ U) t
  left : ∀ {T U t} → ¬Language T t → ¬Language (T ∩ U) t
  right : ∀ {T U u} → ¬Language U u → ¬Language (T ∩ U) u
  never : ∀ {t} → ¬Language never t
  error : ∀ {t} → ¬Language error ⟨ t ⟩

data RLanguage where

  error : ∀ {T} → Language T error → RLanguage T error
  diverge : ∀ {T} → RLanguage T diverge
  one : ∀ {T t} → Language T ⟨ t ⟩ → RLanguage T ⟨ t ⟩

data ¬RLanguage where

  error : ∀ {T} → ¬Language T error → ¬RLanguage T error
  arity : ∀ {T} → ¬RLanguage T arity
  one : ∀ {T t} → ¬Language T ⟨ t ⟩ → ¬RLanguage T ⟨ t ⟩

-- Subtyping as language inclusion

_<:_ : Type → Type → Set
(T <: U) = ∀ {t} → (Language T t) → (Language U t)

-- For warnings, we are interested in failures of subtyping,
-- which is whrn there is a tree in T's language that isn't in U's.

data _≮:_ (T U : Type) : Set where

  witness : ∀ {t} →

    Language T t →
    ¬Language U t →
    -----------------
    T ≮: U
