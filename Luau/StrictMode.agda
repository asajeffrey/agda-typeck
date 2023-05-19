{-# OPTIONS --rewriting #-}

module Luau.StrictMode where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤)
open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (just; nothing)
open import Luau.Syntax using (Expr; Stat; Block; BinaryOperator; yes; nil; addr; var; binexp; var_∈_; _⟨_⟩∈_; function_is_end; _$_; block_is_end; local_←_; _∙_; done; return; name; +; -; *; /; <; >; <=; >=; ··)
open import Luau.Type using (Type; unknown; never; any; error; funktion; scalar; check; _⇒_; _∪_; _∩_; ⌊_⌋)
open import Luau.ResolveOverloads using (src; resolve)
open import Luau.SafeTypes using (Safe; Unsafe)
open import Luau.Subtyping using (_<:_; _≮:_)
open import Luau.ErrorSuppression using (_≮:ᵘ_)
open import Luau.Heap using (Heap; function_is_end) renaming (_[_] to _[_]ᴴ)
open import Luau.VarCtxt using (VarCtxt; ∅; _⋒_; _↦_; _⊕_↦_; _⊝_) renaming (_[_] to _[_]ⱽ)
open import Luau.TypeCheck using (_⊢ᴮ_∈_; _⊢ᴱ_∈_; ⊢ᴴ_; ⊢ᴼ_; _⊢ᴴᴱ_▷_∈_; _⊢ᴴᴮ_▷_∈_; var; addr; app; binexp; block; return; local; function; checked; srcBinOp)
open import Properties.Contradiction using (¬)
open import Properties.TypeCheck using (typeCheckᴮ)
open import Properties.Product using (_,_)

data Warningᴱ (H : Heap yes) {Γ} : ∀ {M T} → (Γ ⊢ᴱ M ∈ T) → Set
data Warningᴮ (H : Heap yes) {Γ} : ∀ {B T} → (Γ ⊢ᴮ B ∈ T) → Set

data Warningᴱ H {Γ} where

  UnallocatedAddress : ∀ {a T} →

    (H [ a ]ᴴ ≡ nothing) →
    ---------------------
    Warningᴱ H (addr {a} T)

  UnboundVariable : ∀ {x T p} →

    (Γ [ x ]ⱽ ≡ nothing) →
    ------------------------
    Warningᴱ H (var {x} {T} p)

  NotFunctionCall : ∀ {M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    (T ≮:ᵘ funktion) →
    -----------------
    Warningᴱ H (app D₁ D₂)

  FunctionCallMismatch : ∀ {M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    (error ≮: T) →
    (U ≮:ᵘ src T) →
    -----------------
    Warningᴱ H (app D₁ D₂)
  
  app₁ : ∀ {M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    Warningᴱ H D₁ →
    -----------------
    Warningᴱ H (app D₁ D₂)

  app₂ : ∀ {M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    Warningᴱ H D₂ →
    -----------------
    Warningᴱ H (app D₁ D₂)

  BinOpMismatch₁ : ∀ {op M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    (T ≮:ᵘ srcBinOp op) →
    ------------------------------
    Warningᴱ H (binexp {op} D₁ D₂)

  BinOpMismatch₂ : ∀ {op M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    (U ≮:ᵘ srcBinOp op) →
    ------------------------------
    Warningᴱ H (binexp {op} D₁ D₂)

  bin₁ : ∀ {op M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    Warningᴱ H D₁ →    
    ------------------------------
    Warningᴱ H (binexp {op} D₁ D₂)

  bin₂ : ∀ {op M N T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴱ N ∈ U} →

    Warningᴱ H D₂ →    
    ------------------------------
    Warningᴱ H (binexp {op} D₁ D₂)
    
  FunctionDefnMismatch : ∀ {f x B T U V} {D : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    (V ≮:ᵘ U) →
    -------------------------
    Warningᴱ H (function {f} {U = U} D)

  CheckedDefnMismatch : ∀ {f x B E S T U V} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} → {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ B ∈ E} →

    (V ≮:ᵘ U) →
    -------------------------
    Warningᴱ H (checked {f} {U = U} D₁ D₂)

  CheckedErrorMismatch : ∀ {f x B E S T U V} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} → {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ B ∈ E} →

    (E ≮: error) →
    -------------------------
    Warningᴱ H (checked {f} {U = U} D₁ D₂)

  function₁ : ∀ {f x B T U V} {D : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    Warningᴮ H D →
    -------------------------
    Warningᴱ H (function {f} {U = U} D)

  checked₁ : ∀ {f x B E S T U V} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ B ∈ E} →

    Warningᴮ H D₁ →
    -------------------------
    Warningᴱ H (checked {f} {U = U} D₁ D₂)

  BlockMismatch : ∀ {b B T U} {D : Γ ⊢ᴮ B ∈ U} →

    (U ≮:ᵘ T) →
    ------------------------------
    Warningᴱ H (block {b} {T = T} D)

  block₁ : ∀ {b B T U} {D : Γ ⊢ᴮ B ∈ U} →

    Warningᴮ H D →
    ------------------------------
    Warningᴱ H (block {b} {T = T} D)

  UnsafeBlock : ∀ {b B T U} {D : Γ ⊢ᴮ B ∈ U} →

    Unsafe T →
    ------------------------------
    Warningᴱ H (block {b} {T = T} D)

  UnsafeFunction : ∀ {f x B T U V} {D : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    Unsafe (T ⇒ U) →
    -------------------------
    Warningᴱ H (function {f} {T = T} {U = U} D)

  UnsafeChecked : ∀ {f x B E S T U V} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ B ∈ E} →

    Unsafe (T ⇒ U) →
    -------------------------
    Warningᴱ H (checked {f} {T = T} {U = U} D₁ D₂)

data Warningᴮ H {Γ} where

  return : ∀ {M B T U} {D₁ : Γ ⊢ᴱ M ∈ T} {D₂ : Γ ⊢ᴮ B ∈ U} →

    Warningᴱ H D₁ →
    ------------------
    Warningᴮ H (return D₁ D₂)

  LocalVarMismatch : ∀ {x M B T U V} {D₁ : Γ ⊢ᴱ M ∈ U} {D₂ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    (U ≮:ᵘ T) →
    --------------------
    Warningᴮ H (local D₁ D₂)

  local₁ : ∀ {x M B T U V} {D₁ : Γ ⊢ᴱ M ∈ U} {D₂ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    Warningᴱ H D₁ →
    --------------------
    Warningᴮ H (local D₁ D₂)

  local₂ : ∀ {x M B T U V} {D₁ : Γ ⊢ᴱ M ∈ U} {D₂ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    Warningᴮ H D₂ →
    --------------------
    Warningᴮ H (local D₁ D₂)

  FunctionDefnMismatch : ∀ {f x B C T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ f ↦ (T ⇒ U)) ⊢ᴮ B ∈ W} →

    (V ≮:ᵘ U) →
    -------------------------
    Warningᴮ H (function D₁ D₂)

  CheckedDefnMismatch : ∀ {f x B C E S T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ C ∈ E} {D₃ : (Γ ⊕ f ↦ ((T ⇒ U) ∩ check S)) ⊢ᴮ B ∈ W} →

    (V ≮:ᵘ U) →
    -------------------------
    Warningᴮ H (checked D₁ D₂ D₃)

  CheckedErrorMismatch : ∀ {f x B C E S T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ x ↦ ⌊ S ⌋) ⊢ᴮ C ∈ E} {D₃ : (Γ ⊕ f ↦ ((T ⇒ U) ∩ check S)) ⊢ᴮ B ∈ W} →

    (E ≮: error) →
    -------------------------
    Warningᴮ H (checked D₁ D₂ D₃)

  function₁ : ∀ {f x B C T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ f ↦ (T ⇒ U)) ⊢ᴮ B ∈ W} →

    Warningᴮ H D₁ →
    --------------------
    Warningᴮ H (function D₁ D₂)

  function₂ : ∀ {f x B C T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ f ↦ (T ⇒ U)) ⊢ᴮ B ∈ W} →

    Warningᴮ H D₂ →
    --------------------
    Warningᴮ H (function D₁ D₂)

  UnsafeLocal : ∀ {x M B T U V} {D₁ : Γ ⊢ᴱ M ∈ U} {D₂ : (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V} →

    Unsafe T →
    --------------------
    Warningᴮ H (local D₁ D₂)

  UnsafeFunction : ∀ {f x B C T U V W} {D₁ : (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V} {D₂ : (Γ ⊕ f ↦ (T ⇒ U)) ⊢ᴮ B ∈ W} →

    Unsafe (T ⇒ U) →
    --------------------
    Warningᴮ H (function D₁ D₂)
    
data Warningᴼ (H : Heap yes) : ∀ {V} → (⊢ᴼ V) → Set where

  FunctionDefnMismatch : ∀ {f x B T U V} {D : (x ↦ T) ⊢ᴮ B ∈ V} →

    (V ≮: U) →
    ---------------------------------
    Warningᴼ H (function {f} {U = U} D)

  FunctionErrorMismatch : ∀ {f x B E T U V} {D : (x ↦ T) ⊢ᴮ B ∈ V} →

    (E ≮: error) →
    ---------------------------------
    Warningᴼ H (function {f} {U = U} D)

  function₁ : ∀ {f x B T U V} {D : (x ↦ T) ⊢ᴮ B ∈ V} →

    Warningᴮ H D →
    ---------------------------------
    Warningᴼ H (function {f} {U = U} D)

  UnsafeFunction : ∀ {f x B T U V} {D : (x ↦ T) ⊢ᴮ B ∈ V} →

    Unsafe (T ⇒ U) →
    ---------------------------------
    Warningᴼ H (function {f} {U = U} D)

data Warningᴴ H (D : ⊢ᴴ H) : Set where

  addr : ∀ a {O} →

    (p : H [ a ]ᴴ ≡ O) →
    Warningᴼ H (D a p) →
    ---------------
    Warningᴴ H D

data Warningᴴᴱ H {Γ M T} : (Γ ⊢ᴴᴱ H ▷ M ∈ T) → Set where

  heap : ∀ {D₁ : ⊢ᴴ H} {D₂ : Γ ⊢ᴱ M ∈ T} →

    Warningᴴ H D₁ →
    -----------------
    Warningᴴᴱ H (D₁ , D₂)

  expr : ∀ {D₁ : ⊢ᴴ H} {D₂ : Γ ⊢ᴱ M ∈ T} →

    Warningᴱ H D₂ →
    ---------------------
    Warningᴴᴱ H (D₁ , D₂)

data Warningᴴᴮ H {Γ B T} : (Γ ⊢ᴴᴮ H ▷ B ∈ T) → Set where

  heap : ∀ {D₁ : ⊢ᴴ H} {D₂ : Γ ⊢ᴮ B ∈ T} →

    Warningᴴ H D₁ →
    -----------------
    Warningᴴᴮ H (D₁ , D₂)

  block : ∀ {D₁ : ⊢ᴴ H} {D₂ : Γ ⊢ᴮ B ∈ T} →

    Warningᴮ H D₂ →
    ---------------------
    Warningᴴᴮ H (D₁ , D₂)
