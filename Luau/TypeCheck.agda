{-# OPTIONS --rewriting #-}

module Luau.TypeCheck where

open import Agda.Builtin.Equality using (_≡_)
open import FFI.Data.Either using (Either; Left; Right)
open import FFI.Data.Maybe using (Maybe; just)
open import Luau.ResolveOverloads using (resolve)
open import Luau.Syntax using (Expr; Stat; Block; BinaryOperator; yes; nil; addr; num; bool; str; val; var; var_∈_; _⟨_⟩∈_; _⟨_∌_⟩∈_; function_is_end; _$_; block_is_end; binexp; local_←_; _∙_; done; return; name; +; -; *; /; <; >; ==; ~=; <=; >=; ··)
open import Luau.Var using (Var)
open import Luau.Addr using (Addr)
open import Luau.Heap using (Heap; Object; function_is_end) renaming (_[_] to _[_]ᴴ)
open import Luau.Type using (Type; nill; any; number; boolean; string; negate; error; _⇒_; _∩_)
open import Luau.VarCtxt using (VarCtxt; ∅; _⋒_; _↦_; _⊕_↦_; _⊝_) renaming (_[_] to _[_]ⱽ)
open import FFI.Data.Vector using (Vector)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Properties.DecSubtyping using (dec-subtyping)
open import Properties.Product using (_×_; _,_)

orAny : Maybe Type → Type
orAny nothing = any
orAny (just T) = T

srcBinOp : BinaryOperator → Type
srcBinOp + = number
srcBinOp - = number
srcBinOp * = number
srcBinOp / = number
srcBinOp < = number
srcBinOp > = number
srcBinOp == = any
srcBinOp ~= = any
srcBinOp <= = number
srcBinOp >= = number
srcBinOp ·· = string

tgtBinOp : BinaryOperator → Type
tgtBinOp + = number
tgtBinOp - = number
tgtBinOp * = number
tgtBinOp / = number
tgtBinOp < = boolean
tgtBinOp > = boolean
tgtBinOp == = boolean
tgtBinOp ~= = boolean
tgtBinOp <= = boolean
tgtBinOp >= = boolean
tgtBinOp ·· = string

data _⊢ᴮ_∈_ : VarCtxt → Block yes → Type → Set
data _⊢ᴱ_∈_ : VarCtxt → Expr yes → Type → Set

data _⊢ᴮ_∈_ where

  done : ∀ {Γ} →

    ---------------
    Γ ⊢ᴮ done ∈ nill

  return : ∀ {M B T U Γ} →

    Γ ⊢ᴱ M ∈ T →
    Γ ⊢ᴮ B ∈ U →
    ---------------------
    Γ ⊢ᴮ return M ∙ B ∈ T

  local : ∀ {x M B T U V Γ} →

    Γ ⊢ᴱ M ∈ U →
    (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V →
    --------------------------------
    Γ ⊢ᴮ local var x ∈ T ← M ∙ B ∈ V

  function : ∀ {f x B C E S T U V W Γ} →

    (Γ ⊕ x ↦ S) ⊢ᴮ C ∈ E →
    (Γ ⊕ x ↦ T) ⊢ᴮ C ∈ V →
    (Γ ⊕ f ↦ ((S ⇒ error) ∩ (T ⇒ U))) ⊢ᴮ B ∈ W →
    -------------------------------------------------
    Γ ⊢ᴮ function f ⟨ S ∌ var x ∈ T ⟩∈ U is C end ∙ B ∈ W

data _⊢ᴱ_∈_ where

  nil : ∀ {Γ} →

    --------------------
    Γ ⊢ᴱ (val nil) ∈ nill

  var : ∀ {x T Γ} →

    T ≡ orAny(Γ [ x ]ⱽ) →
    ----------------
    Γ ⊢ᴱ (var x) ∈ T

  addr : ∀ {a Γ} T →

    -----------------
    Γ ⊢ᴱ val(addr a) ∈ T

  num : ∀ {n Γ} →

    ---------------------------
    Γ ⊢ᴱ val(num n) ∈ number

  bool : ∀ {b Γ} →

    --------------------------
    Γ ⊢ᴱ val(bool b) ∈ boolean
  
  str : ∀ {x Γ} →

    ---------------------------
    Γ ⊢ᴱ val(str x) ∈ string

  app : ∀ {M N T U Γ} →

    Γ ⊢ᴱ M ∈ T →
    Γ ⊢ᴱ N ∈ U →
    ----------------------------
    Γ ⊢ᴱ (M $ N) ∈ (resolve T U)

  function : ∀ {f x B E S T U V Γ} →

    (Γ ⊕ x ↦ S) ⊢ᴮ B ∈ E →
    (Γ ⊕ x ↦ T) ⊢ᴮ B ∈ V →
    -----------------------------------------------------
    Γ ⊢ᴱ (function f ⟨ S ∌ var x ∈ T ⟩∈ U is B end) ∈ ((S ⇒ error) ∩ (T ⇒ U))

  block : ∀ {b B T U Γ} →

    Γ ⊢ᴮ B ∈ U →
    ------------------------------------
    Γ ⊢ᴱ (block var b ∈ T is B end) ∈ T

  binexp : ∀ {op Γ M N T U} →

    Γ ⊢ᴱ M ∈ T →
    Γ ⊢ᴱ N ∈ U →
    ----------------------------------
    Γ ⊢ᴱ (binexp M op N) ∈ tgtBinOp op

data ⊢ᴼ_ : Maybe(Object yes) → Set where

  nothing :

    ---------
    ⊢ᴼ nothing

  function : ∀ {f x E S T U V B} →

    (x ↦ S) ⊢ᴮ B ∈ E →
    (x ↦ T) ⊢ᴮ B ∈ V →
    ----------------------------------------------
    ⊢ᴼ (just function f ⟨ S ∌ var x ∈ T ⟩∈ U is B end)

⊢ᴴ_ : Heap yes → Set
⊢ᴴ H = ∀ a {O} → (H [ a ]ᴴ ≡ O) → (⊢ᴼ O)

_⊢ᴴᴱ_▷_∈_ : VarCtxt → Heap yes → Expr yes → Type → Set
(Γ ⊢ᴴᴱ H ▷ M ∈ T) = (⊢ᴴ H) × (Γ ⊢ᴱ M ∈ T)

_⊢ᴴᴮ_▷_∈_ : VarCtxt → Heap yes → Block yes → Type → Set
(Γ ⊢ᴴᴮ H ▷ B ∈ T) = (⊢ᴴ H) × (Γ ⊢ᴮ B ∈ T)
