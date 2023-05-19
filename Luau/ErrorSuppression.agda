{-# OPTIONS --rewriting #-}

module Luau.ErrorSuppression where

open import Agda.Builtin.Unit using (⊤)
open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import Luau.Type using (Type; unknown; never; any; error; funktion; scalar; check; _⇒_; _∪_; _∩_)
open import Luau.Subtyping using (Value; Arguments; Result; Language; ¬Language; _<:_; _≮:_; ⟨_⟩; _↦_; witness; untyped; error; diverge; scalar; ⟨⟩)
open import Properties.Contradiction using (¬; ⊥)
open import Properties.Product using (_×_)

-- An (un) suppressed element of a type

SuppressedValue : Type → Value → Set
SuppressedArguments : Type → Arguments → Set
SuppressedResult : Type → Result → Set

SuppressedValue T untyped = Language T untyped
SuppressedValue (scalar S) t = ⊥
SuppressedValue (S ⇒ T) (scalar s) = ⊥
SuppressedValue (S ⇒ T) (s ↦ t) = Either (SuppressedArguments S s) (SuppressedResult T t)
SuppressedValue never t = ⊥
SuppressedValue any t = ⊤
SuppressedValue error t = ⊤
SuppressedValue (T ∪ U) t = Either (SuppressedValue T t) (SuppressedValue U t)
SuppressedValue (T ∩ U) t = (SuppressedValue T t) × (SuppressedValue U t)
SuppressedValue (check S) t = ⊥

SuppressedArguments T ⟨⟩ = ⊥
SuppressedArguments T ⟨ t ⟩ = SuppressedValue T t

SuppressedResult T diverge = ⊥
SuppressedResult T error = ⊥
SuppressedResult T ⟨ t ⟩ = SuppressedValue T t

-- A subtyping failure which should not be suppressed
Unsuppressed : ∀ {T U} → (T ≮: U) → Set
Unsuppressed {T} (witness {t} p q) = ¬(SuppressedValue T t)

-- An unsuppressed subtyping failure
data _≮:ᵘ_ T U : Set where

  _,_ :

    (p : T ≮: U) →
    Unsuppressed p →
    -------------------
    T ≮:ᵘ U
  
