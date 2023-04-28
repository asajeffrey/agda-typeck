{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nill; number; string; boolean; scalar; error; never; any; check; _⇒_; _∪_; _∩_)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data TypedValue : Set
data Arguments : Set
data Result : Set
data Principal : Set
data Value : Set

data TypedValue where

  scalar : Scalar → TypedValue
  _↦_ : (s : Arguments) → (t : Result) → TypedValue

data Arguments where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : Arguments
  ⟨_⟩ : TypedValue → Arguments

data Result where

  -- The effects we're tracking are causing a runtime error, a "too few arguments" error,
  -- or diverging
  blame : Principal → Result
  diverge : Result
  ⟨_⟩ : TypedValue → Result

data Principal where

  callee : Principal
  caller : Principal
  
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
  function-arity : ∀ {T U} → (¬Language T error) → Language (T ⇒ U) ⟨ ⟨⟩ ↦ blame caller ⟩
  check-ok : ∀ {T t u} → (Language T ⟨ t ⟩) → Language (check T) ⟨ ⟨ t ⟩ ↦ u ⟩
  check-nok : ∀ {T t} → Language (check T) ⟨ t ↦ blame caller ⟩
  check-arity : ∀ {T u} → (Language T error) → Language (check T) ⟨ ⟨⟩ ↦ u ⟩
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
  function-error : ∀ {T U} → ¬Language (T ⇒ U) error
  function-one : ∀ {T U t u} → (Language T ⟨ t ⟩) → (¬RLanguage U u) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ u ⟩
  function-none : ∀ {T U u} → (u ≢ blame caller) → (¬RLanguage U u) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ u ⟩
  function-arity : ∀ {T U} → (Language T error) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ blame caller ⟩
  check-scalar : ∀ {S T} → ¬Language (check T) ⟨ scalar S ⟩
  check-error : ∀ {T} → ¬Language (check T) error
  check-one : ∀ {T t u} → (u ≢ blame caller) → (¬Language T ⟨ t ⟩) → ¬Language (check T) ⟨ ⟨ t ⟩ ↦ u ⟩
  check-none : ∀ {T u} → (u ≢ blame caller) → (¬Language T error) → ¬Language (check T) ⟨ ⟨⟩ ↦ u ⟩
  _,_ : ∀ {T U t} → ¬Language T t → ¬Language U t → ¬Language (T ∪ U) t
  left : ∀ {T U t} → ¬Language T t → ¬Language (T ∩ U) t
  right : ∀ {T U u} → ¬Language U u → ¬Language (T ∩ U) u
  never : ∀ {t} → ¬Language never t
  error : ∀ {t} → ¬Language error ⟨ t ⟩

data RLanguage where

  callee : ∀ {T} → Language T error → RLanguage T (blame callee)
  diverge : ∀ {T} → RLanguage T diverge
  one : ∀ {T t} → Language T ⟨ t ⟩ → RLanguage T ⟨ t ⟩

data ¬RLanguage where

  callee : ∀ {T} → ¬Language T error → ¬RLanguage T (blame callee)
  caller : ∀ {T} → ¬RLanguage T (blame caller)
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
