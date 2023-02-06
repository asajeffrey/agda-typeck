{-# OPTIONS --rewriting #-}

module Properties.StrictMode where

import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Heap using (Heap; Object; function_is_end; defn; alloc; ok; next; lookup-not-allocated) renaming (_≡_⊕_↦_ to _≡ᴴ_⊕_↦_; _[_] to _[_]ᴴ; ∅ to ∅ᴴ)
open import Luau.ResolveOverloads using (Resolved; src; resolve; resolveⁿ; resolveᶠ; resolveˢ; resolveToˢ; srcⁿ; target; yes; no)
open import Luau.StrictMode using (Warningᴱ; Warningᴮ; Warningᴼ; Warningᴴ; Unsafe; Safe; UnallocatedAddress; UnboundVariable; FunctionCallMismatch; NotFunctionCall; app₁; app₂; BinOpMismatch₁; BinOpMismatch₂; bin₁; bin₂; BlockMismatch; block₁; return; LocalVarMismatch; local₁; local₂; FunctionDefnMismatch; function; function₁; function₂; heap; expr; block; addr; param; result; UnsafeBlock; UnsafeLocal; UnsafeFunction; any; error; scalar; never; ∪-left; ∪-right; ∩-left; ∩-right; _∩_; _∪_)
open import Luau.Substitution using (_[_/_]ᴮ; _[_/_]ᴱ; _[_/_]ᴮunless_; var_[_/_]ᴱwhenever_)
open import Luau.Subtyping using (_<:_; _≮:_; witness; any; never; scalar; scalar-function; scalar-error; scalar-scalar; function-scalar; function-ok; function-error; left; right; _,_; error; Language; ¬Language)
open import Luau.Syntax using (Expr; yes; var; val; var_∈_; _⟨_⟩∈_; _$_; addr; num; bool; str; binexp; nil; function_is_end; block_is_end; done; return; local_←_; _∙_; fun; arg; name; ==; ~=; +; -; *; /; <; >; <=; >=; ··)
open import Luau.Type using (Type; NIL; NUMBER; STRING; BOOLEAN; nill; number; string; boolean; scalar; error; unknown; funktion; _⇒_; never; any; _∩_; _∪_; _≡ᵀ_; _≡ᴹᵀ_; _≡ˢ_)
open import Luau.TypeCheck using (_⊢ᴮ_∈_; _⊢ᴱ_∈_; _⊢ᴴᴮ_▷_∈_; _⊢ᴴᴱ_▷_∈_; nil; var; addr; app; function; block; done; return; local; orAny; srcBinOp; tgtBinOp)
open import Luau.TypeNormalization using (normalize; _∩ⁿ_; _∪ⁿ_; _∪ⁿˢ_; _∩ⁿˢ_; _∪ᶠ_)
open import Luau.TypeSaturation using (saturate; ∩-saturate; ∪-saturate; _⋒_; _⋓_)
open import Luau.Var using (_≡ⱽ_)
open import Luau.Addr using (_≡ᴬ_)
open import Luau.VarCtxt using (VarCtxt; ∅; _↦_; _⊕_↦_; _⊝_; ⊕-lookup-miss; ⊕-swap; ⊕-over) renaming (_[_] to _[_]ⱽ)
open import Luau.VarCtxt using (VarCtxt; ∅)
open import Properties.Remember using (remember; _,_)
open import Properties.Equality using (_≢_; sym; cong; trans; subst₁; cong₂)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Contradiction using (CONTRADICTION; ¬)
open import Properties.Functions using (_∘_)
open import Properties.DecSubtyping using (dec-subtyping)
open import Properties.Subtyping using (any-≮:; ≡-trans-≮:; ≮:-trans-≡; ≮:-trans; ≮:-refl; scalar-≢-impl-≮:; function-≮:-scalar; scalar-≮:-function; function-≮:-never; error-≮:-never; error-≮:-function; scalar-<:-unknown; function-<:-unknown; any-≮:-scalar; scalar-≮:-never; any-≮:-never; <:-refl; <:-any; <:-impl-¬≮:; <:-never; <:-∪-lub; <:-∩-left; <:-∩-right; <:-∪-left; <:-∪-right)
open import Properties.ResolveOverloads using (src-any-≮:; any-src-≮:; <:-src; <:-srcᶠ; <:-resolve; resolve-<:-⇒; <:-resolve-⇒)
open import Properties.Subtyping using (any-≮:; ≡-trans-≮:; ≮:-trans-≡; ≮:-trans; <:-trans-≮:; ≮:-refl; scalar-≢-impl-≮:; function-≮:-scalar; scalar-≮:-function; function-≮:-never; any-≮:-scalar; scalar-≮:-never; any-≮:-never; error-≮:-scalar; ≡-impl-<:; ≡-trans-<:; <:-trans-≡; ≮:-trans-<:; <:-trans)
open import Properties.TypeCheck using (typeOfᴼ; typeOfᴹᴼ; typeOfⱽ; typeOfᴱ; typeOfᴮ; typeCheckᴱ; typeCheckᴮ; typeCheckᴼ; typeCheckᴴ)
open import Properties.TypeNormalization using (normal; Normal; FunType; ErrScalar; OptScalar; _⇒_; _∩_; _∪_; never; error; scalar; normalize-<:; normal-∩ⁿ; normal-∩ⁿˢ)
open import Properties.TypeSaturation using (Overloads; Saturated; _⊆ᵒ_; _<:ᵒ_; normal-saturate; normal-∩-saturate; normal-∪-saturate; saturated; <:-saturate; saturate-<:; defn; here; left; right)
open import Luau.OpSem using (_⟦_⟧_⟶_; _⊢_⟶*_⊣_; _⊢_⟶ᴮ_⊣_; _⊢_⟶ᴱ_⊣_; app₁; app₂; function; beta; return; block; done; local; subst; binOp₀; binOp₁; binOp₂; refl; step; +; -; *; /; <; >; ==; ~=; <=; >=; ··)
open import Luau.RuntimeError using (BinOpError; RuntimeErrorᴱ; RuntimeErrorᴮ; FunctionMismatch; BinOpMismatch₁; BinOpMismatch₂; UnboundVariable; SEGV; app₁; app₂; bin₁; bin₂; block; local; return; +; -; *; /; <; >; <=; >=; ··)
open import Luau.RuntimeType using (RuntimeType; valueType; num; str; bool; nil; function)

data _⊑_ (H : Heap yes) : Heap yes → Set where
  refl : (H ⊑ H)
  snoc : ∀ {H′ a O} → (H′ ≡ᴴ H ⊕ a ↦ O) → (H ⊑ H′)

rednᴱ⊑ : ∀ {H H′ M M′} → (H ⊢ M ⟶ᴱ M′ ⊣ H′) → (H ⊑ H′)
rednᴮ⊑ : ∀ {H H′ B B′} → (H ⊢ B ⟶ᴮ B′ ⊣ H′) → (H ⊑ H′)

rednᴱ⊑ (function a p) = snoc p
rednᴱ⊑ (app₁ s) = rednᴱ⊑ s
rednᴱ⊑ (app₂ p s) = rednᴱ⊑ s
rednᴱ⊑ (beta O v p q) = refl
rednᴱ⊑ (block s) = rednᴮ⊑ s
rednᴱ⊑ (return v) = refl
rednᴱ⊑ done = refl
rednᴱ⊑ (binOp₀ p) = refl
rednᴱ⊑ (binOp₁ s) = rednᴱ⊑ s
rednᴱ⊑ (binOp₂ s) = rednᴱ⊑ s

rednᴮ⊑ (local s) = rednᴱ⊑ s
rednᴮ⊑ (subst v) = refl
rednᴮ⊑ (function a p) = snoc p
rednᴮ⊑ (return s) = rednᴱ⊑ s

data LookupResult (H : Heap yes) a V : Set where
  just : (H [ a ]ᴴ ≡ just V) → LookupResult H a V
  nothing : (H [ a ]ᴴ ≡ nothing) → LookupResult H a V

lookup-⊑-nothing : ∀ {H H′} a → (H ⊑ H′) → (H′ [ a ]ᴴ ≡ nothing) → (H [ a ]ᴴ ≡ nothing)
lookup-⊑-nothing {H} a refl p = p
lookup-⊑-nothing {H} a (snoc defn) p with a ≡ᴬ next H 
lookup-⊑-nothing {H} a (snoc defn) p | yes refl = refl
lookup-⊑-nothing {H} a (snoc o) p | no q = trans (lookup-not-allocated o q) p

dec-Unsafe : ∀ T → Either (Unsafe T) (Safe T)
dec-Unsafe (scalar S) = Right (scalar S)
dec-Unsafe (S ⇒ T) = cond (Left ∘ param) (λ ¬Wˢ → mapLR result (function ¬Wˢ) (dec-Unsafe T)) (dec-Unsafe S)
dec-Unsafe never = Right never
dec-Unsafe any = Left any
dec-Unsafe error = Left error
dec-Unsafe (T ∪ U) = cond (Left ∘ ∪-left) (λ ¬Wᵀ → mapLR ∪-right (λ ¬Wᵁ → ¬Wᵀ ∪ ¬Wᵁ) (dec-Unsafe U)) (dec-Unsafe T)
dec-Unsafe (T ∩ U) = cond (Left ∘ ∩-left) (λ ¬Wᵀ → mapLR ∩-right (λ ¬Wᵁ → ¬Wᵀ ∩ ¬Wᵁ) (dec-Unsafe U)) (dec-Unsafe T)

-- warning-comp : ∀ {T} → Safe T → ¬(Unsafe T)
-- warning-comp V W = {!!}

<:-unknown : ∀ {T} → Safe T → (T <: unknown)
<:-unknown never = <:-never
<:-unknown (¬W ∪ ¬W′) = <:-∪-lub (<:-unknown ¬W) (<:-unknown ¬W′)
<:-unknown (¬W ∩ ¬W′) = <:-trans <:-∩-left (<:-unknown ¬W)
<:-unknown (function ¬W ¬W′) = function-<:-unknown
<:-unknown (scalar S) = scalar-<:-unknown

safe-¬error : ∀ {T} → Safe T → (¬Language T error)
safe-¬error never = never
safe-¬error (¬W ∩ ¬W′) = left (safe-¬error ¬W)
safe-¬error (¬W ∪ ¬W′) = safe-¬error ¬W , safe-¬error ¬W′
safe-¬error (function ¬W ¬W′) = function-error
safe-¬error (scalar S) = scalar-error S

≮:-error : ∀ {T} → Safe T → (error ≮: T)
≮:-error ¬W = witness error (safe-¬error ¬W)

data Warningⱽ (Γ : VarCtxt) : Set where

  UnsafeVar : ∀ x {T} →

    Γ [ x ]ⱽ ≡ just T →
    Unsafe T →
    -------------------
    Warningⱽ Γ
    
data Warningᴱ+ H Γ M : Set where

  expr : Warningᴱ H (typeCheckᴱ H Γ M) → Warningᴱ+ H Γ M
  heap : Warningᴴ H (typeCheckᴴ H) → Warningᴱ+ H Γ M
  ctxt : Warningⱽ Γ → Warningᴱ+ H Γ M

data Warningᴮ+ H Γ B : Set where

  block : Warningᴮ H (typeCheckᴮ H Γ B) → Warningᴮ+ H Γ B
  heap : Warningᴴ H (typeCheckᴴ H) → Warningᴮ+ H Γ B
  ctxt : Warningⱽ Γ → Warningᴮ+ H Γ B

mapᴱ+ : ∀ {H Γ M N} → (Warningᴱ H (typeCheckᴱ H Γ M) → Warningᴱ H (typeCheckᴱ H Γ N)) → Warningᴱ+ H Γ M → Warningᴱ+ H Γ N
mapᴱ+ f (expr W) = expr (f W)
mapᴱ+ f (heap W) = heap W
mapᴱ+ f (ctxt W) = ctxt W

mapᴮ+ : ∀ {H Γ B C} → (Warningᴮ H (typeCheckᴮ H Γ B) → Warningᴮ H (typeCheckᴮ H Γ C)) → Warningᴮ+ H Γ B → Warningᴮ+ H Γ C
mapᴮ+ f (block W) = block (f W)
mapᴮ+ f (heap W) = heap W
mapᴮ+ f (ctxt W) = ctxt W

mapᴱᴮ+ : ∀ {H Γ M C} → (Warningᴱ H (typeCheckᴱ H Γ M) → Warningᴮ H (typeCheckᴮ H Γ C)) → Warningᴱ+ H Γ M → Warningᴮ+ H Γ C
mapᴱᴮ+ f (expr W) = block (f W)
mapᴱᴮ+ f (heap W) = heap W
mapᴱᴮ+ f (ctxt W) = ctxt W

mapᴮᴱ+ : ∀ {H Γ B N} → (Warningᴮ H (typeCheckᴮ H Γ B) → Warningᴱ H (typeCheckᴱ H Γ N)) → Warningᴮ+ H Γ B → Warningᴱ+ H Γ N
mapᴮᴱ+ f (block W) = expr (f W)
mapᴮᴱ+ f (heap W) = heap W
mapᴮᴱ+ f (ctxt W) = ctxt W

data FoundSrcOverloadTo F G : Set where

  found : ∀ S T →

    Overloads F (S ⇒ T) →
    srcⁿ G <: S →
    --------------------
    FoundSrcOverloadTo F G

findSrcOverload : ∀ {F G} → (Gᶠ : FunType G) → (Fˢ : Saturated F) → (G ⊆ᵒ F) → FoundSrcOverloadTo F G
findSrcOverload (S ⇒ T) Fˢ G⊆F = found S T (G⊆F here) <:-refl
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) Fˢ G⊆F with findSrcOverload G₁ᶠ Fˢ (G⊆F ∘ left) | findSrcOverload G₂ᶠ Fˢ (G⊆F ∘ right)
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) (defn cap cup) G⊆F | found S₁ T₁ o₁ p₁ | found S₂ T₂ o₂ p₂ with cup o₁ o₂
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) (defn cap cup) G⊆F | found S₁ T₁ o₁ p₁ | found S₂ T₂ o₂ p₂ | defn {S = S₀} {T = T₀} o₀ p₀ _ = found S₀ T₀ o₀ (<:-trans (<:-∪-lub (<:-trans p₁ <:-∪-left) (<:-trans p₂ <:-∪-right)) p₀)

FoundSrcOverload : Type → Set
FoundSrcOverload F = FoundSrcOverloadTo F F

Unsafe-overload : ∀ {F S T} → Overloads F (S ⇒ T) → Unsafe (S ⇒ T) → Unsafe F
Unsafe-overload here W = W
Unsafe-overload (left o) W = ∩-left (Unsafe-overload o W)
Unsafe-overload (right o) W = ∩-right (Unsafe-overload o W)

Unsafe-⋒ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ⋒ G) → Unsafe (F ∩ G)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (param (∩-left W)) = ∩-left (param W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (param (∩-right W)) = ∩-right (param W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (result (∩-left W)) = ∩-left (result W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (result (∩-right W)) = ∩-right (result W)
Unsafe-⋒ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-⋒ (S ⇒ T) G W
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-left W) | ∩-left W′ = ∩-left W′
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-left W) | ∩-right W′ = ∩-right (∩-left W′)
Unsafe-⋒ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-⋒ (S ⇒ T) H W
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-right W) | ∩-left W′ = ∩-left W′
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-right W) | ∩-right W′ = ∩-right (∩-right W′)
Unsafe-⋒ (E ∩ F) (U ⇒ V) (∩-left W) with Unsafe-⋒ E (U ⇒ V) W
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-left W) | ∩-left W′ = ∩-left (∩-left W′)
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-left W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (U ⇒ V) (∩-right W) with Unsafe-⋒ F (U ⇒ V) W
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-right W) | ∩-left W′ = ∩-left (∩-right W′)
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-right W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) with Unsafe-⋒ E (G ∩ H) W
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) | ∩-left W′ = ∩-left (∩-left W′)
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) with Unsafe-⋒ F (G ∩ H) W
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) | ∩-left W′ = ∩-left (∩-right W′)
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) | ∩-right W′ = ∩-right W′

Unsafe-⋓ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ⋓ G) → Unsafe (F ∪ G)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (param (∪-left W)) = ∪-left (param W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (param (∪-right W)) = ∪-right (param W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (result (∪-left W)) = ∪-left (result W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (result (∪-right W)) = ∪-right (result W)
Unsafe-⋓ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-⋓ (S ⇒ T) G W
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left W′
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right (∩-left W′)
Unsafe-⋓ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-⋓ (S ⇒ T) H W
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left W′
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right (∩-right W′)
Unsafe-⋓ (E ∩ F) (U ⇒ V) (∩-left W) with Unsafe-⋓ E (U ⇒ V) W
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (U ⇒ V) (∩-right W) with Unsafe-⋓ F (U ⇒ V) W
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-right W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) with Unsafe-⋓ E (G ∩ H) W
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) with Unsafe-⋓ F (G ∩ H) W
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right W′

Unsafe-∩-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (∩-saturate F) → Unsafe F
Unsafe-∩-saturateᶠ (S ⇒ T) W = W
Unsafe-∩-saturateᶠ (F ∩ G) (∩-left (∩-left W)) = ∩-left (Unsafe-∩-saturateᶠ F W)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-left (∩-right W)) = ∩-right (Unsafe-∩-saturateᶠ G W)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) with Unsafe-⋒ (normal-∩-saturate F) (normal-∩-saturate G) W
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) | ∩-left W′ = ∩-left (Unsafe-∩-saturateᶠ F W′)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) | ∩-right W′ = ∩-right (Unsafe-∩-saturateᶠ G W′)

Unsafe-∪-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (∪-saturate F) → Unsafe F
Unsafe-∪-saturateᶠ (S ⇒ T) W = W
Unsafe-∪-saturateᶠ (F ∩ G) (∩-left (∩-left W)) = ∩-left (Unsafe-∪-saturateᶠ F W)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-left (∩-right W)) = ∩-right (Unsafe-∪-saturateᶠ G W)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) with Unsafe-⋓ (normal-∪-saturate F) (normal-∪-saturate G) W
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) | ∪-left W′ = ∩-left (Unsafe-∪-saturateᶠ F W′)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) | ∪-right W′ = ∩-right (Unsafe-∪-saturateᶠ G W′)

Unsafe-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (saturate F) → Unsafe F
Unsafe-saturateᶠ F W = Unsafe-∩-saturateᶠ F (Unsafe-∪-saturateᶠ (normal-∩-saturate F) W)

Unsafe-∪ᶠ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ∪ᶠ G) → Unsafe (F ∪ G)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (param (∩-left W)) = ∪-left (param W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (param (∩-right W)) = ∪-right (param W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (result (∪-left W)) = ∪-left (result W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (result (∪-right W)) = ∪-right (result W)
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-∪ᶠ (S ⇒ T) G W
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left W′
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right (∩-left W′)
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-∪ᶠ (S ⇒ T) H W
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left W′
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right (∩-right W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) with Unsafe-∪ᶠ E G W
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) with Unsafe-∪ᶠ F G W
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) | ∪-right W′ = ∪-right W′

Unsafe-∪ⁿ : ∀ {T U} → (Normal T) → (Normal U) → Unsafe (T ∪ⁿ U) → Unsafe (T ∪ U)
Unsafe-∪ⁿ (S ⇒ T) (U ⇒ V) W = Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) W
Unsafe-∪ⁿ (S ∩ T) (U ⇒ V) W = Unsafe-∪ᶠ (S ∩ T) (U ⇒ V) W
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) with Unsafe-∪ⁿ S (U ⇒ V) W
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) | ∪-left W₁ = ∪-left (∪-left W₁)
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) | ∪-right W₂ = ∪-right W₂
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-right W) = ∪-left (∪-right W)
Unsafe-∪ⁿ never (U ⇒ V) W = ∪-right W
Unsafe-∪ⁿ (S ⇒ T) (U ∩ V) W = Unsafe-∪ᶠ (S ⇒ T) (U ∩ V) W
Unsafe-∪ⁿ (S ∩ T) (U ∩ V) W = Unsafe-∪ᶠ (S ∩ T) (U ∩ V) W
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) with Unsafe-∪ⁿ S (U ∩ V) W
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) | ∪-left W₁ = ∪-left (∪-left W₁)
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) | ∪-right W₂ = ∪-right W₂
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-right W) = ∪-left (∪-right W)
Unsafe-∪ⁿ never (U ∩ V) W = ∪-right W
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) with Unsafe-∪ⁿ T U W
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) | ∪-left W₁ = ∪-left W₁
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) | ∪-right W₂ = ∪-right (∪-left W₂)
Unsafe-∪ⁿ T (U ∪ V) (∪-right W) = ∪-right (∪-right W)
Unsafe-∪ⁿ T never W = ∪-left W

Unsafe-∪ⁿˢ : ∀ {T U} → (Normal T) → (OptScalar U) → Unsafe (T ∪ⁿˢ U) → Unsafe (T ∪ U)
Unsafe-∪ⁿˢ T never W = ∪-left W
Unsafe-∪ⁿˢ T error W = ∪-right error
Unsafe-∪ⁿˢ (S ⇒ T) (scalar U) W = W
Unsafe-∪ⁿˢ (S ∩ T) (scalar U) W = W
Unsafe-∪ⁿˢ never (scalar U) W = W
Unsafe-∪ⁿˢ (S ∪ error) (scalar U) W = ∪-left (∪-right error)
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar U) W with T ≡ˢ U
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar T) W | yes refl = ∪-left W
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar U) (∪-left W) | no p with Unsafe-∪ⁿˢ S (scalar U) W
Unsafe-∪ⁿˢ (S ∪ scalar _) (scalar _) (∪-left W) | no p | ∪-left W′ = ∪-left (∪-left W′)

Unsafe-∩ⁿˢ : ∀ {T U} → (Normal T) → (ErrScalar U) → Unsafe (T ∩ⁿˢ U) → Unsafe (T ∩ U)
Unsafe-∩ⁿˢ (S ∪ error) error W = ∩-right W
Unsafe-∩ⁿˢ (S ∪ scalar T) error W with Unsafe-∩ⁿˢ S error W
Unsafe-∩ⁿˢ (S ∪ scalar _) error W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿˢ (S ∪ scalar _) error W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿˢ (S ∪ error) (scalar U) W with Unsafe-∩ⁿˢ S (scalar U) W
Unsafe-∩ⁿˢ (S ∪ error) (scalar _) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar U) W with T ≡ˢ U
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar T) W | yes refl = ∩-right W
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar U) W | no p with Unsafe-∩ⁿˢ S (scalar U) W
Unsafe-∩ⁿˢ (S ∪ scalar _) (scalar _) W | no p | ∩-left W′ = ∩-left (∪-left W′)

Unsafe-∩ⁿ : ∀ {T U} → (Normal T) → (Normal U) → Unsafe (T ∩ⁿ U) → Unsafe (T ∩ U)
Unsafe-∩ⁿ (S ⇒ T) (U ⇒ V) W = W
Unsafe-∩ⁿ (S ∩ T) (U ⇒ V) W = W
Unsafe-∩ⁿ (S ∪ T) (U ⇒ V) W with Unsafe-∩ⁿ S (U ⇒ V) W 
Unsafe-∩ⁿ (S ∪ T) (_ ⇒ _) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿ (S ∪ T) (_ ⇒ _) W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿ (S ⇒ T) (U ∩ V) W = W
Unsafe-∩ⁿ (S ∩ T) (U ∩ V) W = W
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W with Unsafe-∩ⁿ S (U ∩ V) W
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿ T (U ∪ V) W with Unsafe-∪ⁿˢ (normal-∩ⁿ T U) (normal-∩ⁿˢ T V) W
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ with Unsafe-∩ⁿ T U W′
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ | ∩-left W″ = ∩-left W″
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ | ∩-right W″ = ∩-right (∪-left W″)
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ with Unsafe-∩ⁿˢ T V W′
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ | ∩-left W″ = ∩-left W″
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ | ∩-right W″ = ∩-right (∪-right W″)
Unsafe-∩ⁿ T never ()

Unsafe-normalize : ∀ T → Unsafe (normalize T) → Unsafe T
Unsafe-normalize (scalar S) (∪-left ())
Unsafe-normalize (scalar S) (∪-right ())
Unsafe-normalize (S ⇒ T) W = W
Unsafe-normalize any W = any
Unsafe-normalize error W = error
Unsafe-normalize (T ∪ U) W with Unsafe-∪ⁿ (normal T) (normal U) W
Unsafe-normalize (T ∪ U) W | ∪-left W′ = ∪-left (Unsafe-normalize T W′)
Unsafe-normalize (T ∪ U) W | ∪-right W′ = ∪-right (Unsafe-normalize U W′)
Unsafe-normalize (T ∩ U) W with Unsafe-∩ⁿ (normal T) (normal U) W
Unsafe-normalize (T ∩ U) W | ∩-left W′ = ∩-left (Unsafe-normalize T W′)
Unsafe-normalize (T ∩ U) W | ∩-right W′ = ∩-right (Unsafe-normalize U W′)

Unsafe-resolvedˢ : ∀ {F} → (Fᶠ : FunType F) → (Fˢ : Saturated F) → (V : Type) → (FoundSrcOverload F) → (R : Resolved F V) → Unsafe(target R) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) R W  with dec-subtyping V S
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) R W | Left V≮:S = Left (≮:-trans-<: V≮:S p)
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) (yes Sʳ Tʳ oʳ V<:Sʳ r) W | Right V<:S = Right (Unsafe-overload oʳ (result W))
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) (no r) W | Right V<:S = CONTRADICTION (<:-impl-¬≮: V<:S (r o))

Unsafe-resolveˢ : ∀ {F} → (Fᶠ : FunType F) → (Fˢ : Saturated F) → (V : Type) → Unsafe(resolveˢ Fᶠ Fˢ V) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolveˢ Fᶠ Fˢ V W = Unsafe-resolvedˢ Fᶠ Fˢ V (findSrcOverload Fᶠ Fˢ (λ o → o)) (resolveToˢ Fᶠ Fˢ V (λ o → o)) W

Unsafe-resolveᶠ : ∀ {F} → (Fᶠ : FunType F) → ∀ V → Unsafe(resolveᶠ Fᶠ V) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolveᶠ Fᶠ V W = mapLR (λ p → ≮:-trans-<: p (<:-srcᶠ (normal-saturate Fᶠ) Fᶠ (saturate-<: Fᶠ))) (Unsafe-saturateᶠ Fᶠ) (Unsafe-resolveˢ (normal-saturate Fᶠ) (saturated Fᶠ) V W)

Unsafe-resolveⁿ : ∀ {F} → (Fⁿ : Normal F) → ∀ V → Unsafe(resolveⁿ Fⁿ V) → Either (F ≮: funktion) (Either (V ≮: srcⁿ F) (Unsafe F))
Unsafe-resolveⁿ (T ⇒ U) V W = Right (Unsafe-resolveᶠ (T ⇒ U) V W)
Unsafe-resolveⁿ (T ∩ U) V W = Right (Unsafe-resolveᶠ (T ∩ U) V W)
Unsafe-resolveⁿ (T ∪ error) V W = Right (Right (∪-right error))
Unsafe-resolveⁿ (T ∪ scalar S) V W = Left (<:-trans-≮: <:-∪-right (scalar-≮:-function S))

Unsafe-resolve : ∀ F V → Unsafe(resolve F V) → Either (F ≮: funktion) (Either (V ≮: src F) (Unsafe F))
Unsafe-resolve F V W with Unsafe-resolveⁿ (normal F) V W
Unsafe-resolve F V W | Left p = Left (<:-trans-≮: (normalize-<: F) p)
Unsafe-resolve F V W | Right (Left p) = Right (Left p)
Unsafe-resolve F V W | Right (Right W′) = Right (Right (Unsafe-normalize F W′))

Unsafe-impl-Warningᴱ : ∀ H Γ M → Unsafe (typeOfᴱ H Γ M) → (Warningᴱ+ H Γ M)
Unsafe-impl-Warningᴱ H Γ (var x) W with remember (Γ [ x ]ⱽ)
Unsafe-impl-Warningᴱ H Γ (var x) W | (nothing , p) = expr (UnboundVariable p)
Unsafe-impl-Warningᴱ H Γ (var x) W | (just T , p) = ctxt (UnsafeVar x p (subst₁ Unsafe (cong orAny p) W  ))
Unsafe-impl-Warningᴱ H Γ (val (addr a)) W with remember (H [ a ]ᴴ)
Unsafe-impl-Warningᴱ H Γ (val (addr a)) W | (nothing , p) = expr (UnallocatedAddress p)
Unsafe-impl-Warningᴱ H Γ (val (addr a)) W | (just (function f ⟨ var x ∈ T ⟩∈ U is B end) , p) = heap (addr a p (UnsafeFunction (subst₁ Unsafe (cong orAny (cong typeOfᴹᴼ p)) W)))
Unsafe-impl-Warningᴱ H Γ (M $ N) W with Unsafe-resolve (typeOfᴱ H Γ M) (typeOfᴱ H Γ N) W
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Left p with dec-Unsafe (typeOfᴱ H Γ M)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Left p | Left V = mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H Γ M V)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Left p | Right ¬V = expr (NotFunctionCall (≮:-error ¬V) p)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Right (Right V) = mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H Γ M V)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Right (Left p) with dec-Unsafe (typeOfᴱ H Γ M) | dec-Unsafe (typeOfᴱ H Γ N)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Right (Left p) | Right M✓ | Right N✓ = expr (FunctionCallMismatch (≮:-error M✓) (≮:-error N✓) p)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Right (Left p) | Left M× | _ = mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H Γ M M×)
Unsafe-impl-Warningᴱ H Γ (M $ N) W | Right (Left p) | _ | Left N× = mapᴱ+ app₂ (Unsafe-impl-Warningᴱ H Γ N N×)
Unsafe-impl-Warningᴱ H Γ (function f ⟨ var c ∈ T ⟩∈ U is B end) W = expr (UnsafeFunction W)
Unsafe-impl-Warningᴱ H Γ (block var b ∈ T is B end) W = expr (UnsafeBlock W)
Unsafe-impl-Warningᴱ H Γ (binexp M ·· N) ()

<:-heap-weakeningᴱ : ∀ Γ H M {H′} → (H ⊑ H′) → (typeOfᴱ H′ Γ M <: typeOfᴱ H Γ M)
<:-heap-weakeningᴱ Γ H (var x) h = <:-refl
<:-heap-weakeningᴱ Γ H (val nil) h = <:-refl
<:-heap-weakeningᴱ Γ H (val (addr a)) refl = <:-refl
<:-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = b} q) with a ≡ᴬ b
<:-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = a} defn) | yes refl = <:-any
<:-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = b} q) | no r = ≡-impl-<: (sym (cong orAny (cong typeOfᴹᴼ (lookup-not-allocated q r))))
<:-heap-weakeningᴱ Γ H (val (num n)) h = <:-refl
<:-heap-weakeningᴱ Γ H (val (bool b)) h = <:-refl
<:-heap-weakeningᴱ Γ H (val (str s)) h = <:-refl
<:-heap-weakeningᴱ Γ H (M $ N) h = <:-resolve (<:-heap-weakeningᴱ Γ H M h) (<:-heap-weakeningᴱ Γ H N h)
<:-heap-weakeningᴱ Γ H (function f ⟨ var x ∈ S ⟩∈ T is B end) h = <:-refl
<:-heap-weakeningᴱ Γ H (block var b ∈ T is N end) h = <:-refl
<:-heap-weakeningᴱ Γ H (binexp M op N) h = <:-refl

<:-heap-weakeningᴮ : ∀ Γ H B {H′} → (H ⊑ H′) → (typeOfᴮ H′ Γ B <: typeOfᴮ H Γ B)
<:-heap-weakeningᴮ Γ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) h = <:-heap-weakeningᴮ (Γ ⊕ f ↦ (T ⇒ U)) H B h
<:-heap-weakeningᴮ Γ H (local var x ∈ T ← M ∙ B) h = <:-heap-weakeningᴮ (Γ ⊕ x ↦ T) H B h
<:-heap-weakeningᴮ Γ H (return M ∙ B) h = <:-heap-weakeningᴱ Γ H M h
<:-heap-weakeningᴮ Γ H done h = <:-refl

≮:-heap-weakeningᴱ : ∀ Γ H M {H′ U} → (H ⊑ H′) → (typeOfᴱ H′ Γ M ≮: U) → (typeOfᴱ H Γ M ≮: U)
≮:-heap-weakeningᴱ Γ H M h p = <:-trans-≮: (<:-heap-weakeningᴱ Γ H M h) p

≮:-heap-weakeningᴮ : ∀ Γ H B {H′ U} → (H ⊑ H′) → (typeOfᴮ H′ Γ B ≮: U) → (typeOfᴮ H Γ B ≮: U)
≮:-heap-weakeningᴮ Γ H B h p = <:-trans-≮: (<:-heap-weakeningᴮ Γ H B h) p

≡-heap-weakeningᴱ : ∀ Γ H M {H′} → (H ⊑ H′) → Either (Warningᴱ H (typeCheckᴱ H Γ M)) (typeOfᴱ H′ Γ M ≡ typeOfᴱ H Γ M)
≡-heap-weakeningᴱ Γ H (var x) h = Right refl
≡-heap-weakeningᴱ Γ H (val nil) h = Right refl
≡-heap-weakeningᴱ Γ H (val (addr a)) refl = Right refl
≡-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = b} q) with a ≡ᴬ b
≡-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = a} defn) | yes refl = Left (UnallocatedAddress refl)
≡-heap-weakeningᴱ Γ H (val (addr a)) (snoc {a = b} q) | no r = Right (sym (cong orAny (cong typeOfᴹᴼ (lookup-not-allocated q r))))
≡-heap-weakeningᴱ Γ H (val (num n)) h = Right refl
≡-heap-weakeningᴱ Γ H (val (bool b)) h = Right refl
≡-heap-weakeningᴱ Γ H (val (str s)) h = Right refl
≡-heap-weakeningᴱ Γ H (M $ N) h with ≡-heap-weakeningᴱ Γ H M h | ≡-heap-weakeningᴱ Γ H N h
≡-heap-weakeningᴱ Γ H (M $ N) h | Left W | _ = Left (app₁ W)
≡-heap-weakeningᴱ Γ H (M $ N) h | _ | Left W = Left (app₂ W)
≡-heap-weakeningᴱ Γ H (M $ N) h | Right p | Right q = Right (cong₂ resolve p q)
≡-heap-weakeningᴱ Γ H (function f ⟨ var x ∈ S ⟩∈ T is B end) h = Right refl
≡-heap-weakeningᴱ Γ H (block var b ∈ T is N end) h = Right refl
≡-heap-weakeningᴱ Γ H (binexp M op N) h = Right refl

binOpPreservation : ∀ H {op v w x} → (v ⟦ op ⟧ w ⟶ x) → (tgtBinOp op ≡ typeOfᴱ H ∅ (val x))
binOpPreservation H (+ m n) = refl
binOpPreservation H (- m n) = refl
binOpPreservation H (/ m n) = refl
binOpPreservation H (* m n) = refl
binOpPreservation H (< m n) = refl
binOpPreservation H (> m n) = refl
binOpPreservation H (<= m n) = refl
binOpPreservation H (>= m n) = refl
binOpPreservation H (== v w) = refl
binOpPreservation H (~= v w) = refl
binOpPreservation H (·· v w) = refl

<:-substitutivityᴱ : ∀ {Γ T} H M v x → (typeOfᴱ H ∅ (val v) <: T) → (typeOfᴱ H Γ (M [ v / x ]ᴱ) <: typeOfᴱ H (Γ ⊕ x ↦ T) M)
<:-substitutivityᴱ-whenever : ∀ {Γ T} H v x y (r : Dec(x ≡ y)) → (typeOfᴱ H ∅ (val v) <: T) → (typeOfᴱ H Γ (var y [ v / x ]ᴱwhenever r) <: typeOfᴱ H (Γ ⊕ x ↦ T) (var y))
<:-substitutivityᴮ : ∀ {Γ T} H B v x → (typeOfᴱ H ∅ (val v) <: T) → (typeOfᴮ H Γ (B [ v / x ]ᴮ) <: typeOfᴮ H (Γ ⊕ x ↦ T) B)
<:-substitutivityᴮ-unless : ∀ {Γ T U} H B v x y (r : Dec(x ≡ y)) → (typeOfᴱ H ∅ (val v) <: T) → (typeOfᴮ H (Γ ⊕ y ↦ U) (B [ v / x ]ᴮunless r) <: typeOfᴮ H ((Γ ⊕ x ↦ T) ⊕ y ↦ U) B)
<:-substitutivityᴮ-unless-yes : ∀ {Γ Γ′} H B v x y (r : x ≡ y) → (Γ′ ≡ Γ) → (typeOfᴮ H Γ (B [ v / x ]ᴮunless yes r) <: typeOfᴮ H Γ′ B)
<:-substitutivityᴮ-unless-no : ∀ {Γ Γ′ T} H B v x y (r : x ≢ y) → (Γ′ ≡ Γ ⊕ x ↦ T) → (typeOfᴱ H ∅ (val v) <: T) → (typeOfᴮ H Γ (B [ v / x ]ᴮunless no r) <: typeOfᴮ H Γ′ B) 

<:-substitutivityᴱ H (var y) v x p = <:-substitutivityᴱ-whenever H v x y (x ≡ⱽ y) p
<:-substitutivityᴱ H (val w) v x p = <:-refl
<:-substitutivityᴱ H (binexp M op N) v x p = <:-refl
<:-substitutivityᴱ H (M $ N) v x p = <:-resolve (<:-substitutivityᴱ H M v x p) (<:-substitutivityᴱ H N v x p)
<:-substitutivityᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x p = <:-refl
<:-substitutivityᴱ H (block var b ∈ T is B end) v x p = <:-refl
<:-substitutivityᴱ-whenever H v x x (yes refl) p = p
<:-substitutivityᴱ-whenever H v x y (no o) p = (≡-impl-<: (cong orAny (⊕-lookup-miss x y _ _ o)))

<:-substitutivityᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x p = <:-substitutivityᴮ-unless H B v x f (x ≡ⱽ f) p
<:-substitutivityᴮ H (local var y ∈ T ← M ∙ B) v x p = <:-substitutivityᴮ-unless H B v x y (x ≡ⱽ y) p
<:-substitutivityᴮ H (return M ∙ B) v x p = <:-substitutivityᴱ H M v x p
<:-substitutivityᴮ H done v x p = <:-refl
<:-substitutivityᴮ-unless H B v x y (yes r) p = <:-substitutivityᴮ-unless-yes H B v x y r (⊕-over r)
<:-substitutivityᴮ-unless H B v x y (no r) p = <:-substitutivityᴮ-unless-no H B v x y r (⊕-swap r) p
<:-substitutivityᴮ-unless-yes H B v x y refl refl = <:-refl
<:-substitutivityᴮ-unless-no H B v x y r refl p = <:-substitutivityᴮ H B v x p

≮:-substitutivityᴱ : ∀ {Γ T U} H M v x → (typeOfᴱ H Γ (M [ v / x ]ᴱ) ≮: U) → Either (typeOfᴱ H (Γ ⊕ x ↦ T) M ≮: U) (typeOfᴱ H ∅ (val v) ≮: T)
≮:-substitutivityᴱ {T = T} H M v x p with dec-subtyping (typeOfᴱ H ∅ (val v)) T
≮:-substitutivityᴱ H M v x p | Left q = Right q
≮:-substitutivityᴱ H M v x p | Right q = Left (<:-trans-≮: (<:-substitutivityᴱ H M v x q) p)

≮:-substitutivityᴮ : ∀ {Γ T U} H B v x → (typeOfᴮ H Γ (B [ v / x ]ᴮ) ≮: U) → Either (typeOfᴮ H (Γ ⊕ x ↦ T) B ≮: U) (typeOfᴱ H ∅ (val v) ≮: T)
≮:-substitutivityᴮ {T = T} H M v x p with dec-subtyping (typeOfᴱ H ∅ (val v)) T
≮:-substitutivityᴮ H M v x p | Left q = Right q
≮:-substitutivityᴮ H M v x p | Right q = Left (<:-trans-≮: (<:-substitutivityᴮ H M v x q) p)

≮:-substitutivityᴮ-unless : ∀ {Γ T U V} H B v x y (r : Dec(x ≡ y)) → (typeOfᴮ H (Γ ⊕ y ↦ U) (B [ v / x ]ᴮunless r) ≮: V) → Either (typeOfᴮ H ((Γ ⊕ x ↦ T) ⊕ y ↦ U) B ≮: V) (typeOfᴱ H ∅ (val v) ≮: T)
≮:-substitutivityᴮ-unless {T = T} H B v x y r p with dec-subtyping (typeOfᴱ H ∅ (val v)) T
≮:-substitutivityᴮ-unless H B v x y r p | Left q = Right q
≮:-substitutivityᴮ-unless H B v x y r p | Right q = Left (<:-trans-≮: (<:-substitutivityᴮ-unless H B v x y r q) p)

<:-reductionᴱ : ∀ H M {H′ M′} → (H ⊢ M ⟶ᴱ M′ ⊣ H′) → Either (typeOfᴱ H′ ∅ M′ <: typeOfᴱ H ∅ M) (Warningᴱ+ H ∅ M)
<:-reductionᴮ : ∀ H B {H′ B′} → (H ⊢ B ⟶ᴮ B′ ⊣ H′) → Either (typeOfᴮ H′ ∅ B′ <: typeOfᴮ H ∅ B) (Warningᴮ+ H ∅ B)

<:-reductionᴱ H (M $ N) (app₁ s) = mapLR (λ p → <:-resolve (λ {t} → p {t}) (<:-heap-weakeningᴱ ∅ H N (rednᴱ⊑ s))) (mapᴱ+ app₁) (<:-reductionᴱ H M s)
<:-reductionᴱ H (M $ N) (app₂ q s) = mapLR (λ p → <:-resolve (<:-heap-weakeningᴱ ∅ H M (rednᴱ⊑ s)) (λ {t} → p {t})) (mapᴱ+ app₂) (<:-reductionᴱ H N s)
<:-reductionᴱ H (M $ N) (beta (function f ⟨ var y ∈ S ⟩∈ U is B end) v refl q) with dec-subtyping (typeOfᴱ H ∅ (val v)) S | dec-Unsafe (typeOfᴱ H ∅ M) | dec-Unsafe (typeOfᴱ H ∅ N)
<:-reductionᴱ H (M $ N) (beta (function f ⟨ var y ∈ S ⟩∈ U is B end) v refl q) | Left r | Right M✓ | Right N✓ = Right (expr (FunctionCallMismatch (≮:-error M✓) (≮:-error N✓) (≮:-trans-≡ r (cong src (cong orAny (cong typeOfᴹᴼ (sym q)))))))
<:-reductionᴱ H (M $ N) (beta (function f ⟨ var y ∈ S ⟩∈ U is B end) v refl q) | _ | _ | Left N× = Right (mapᴱ+ app₂ (Unsafe-impl-Warningᴱ H ∅ N N×))
<:-reductionᴱ H (M $ N) (beta (function f ⟨ var y ∈ S ⟩∈ U is B end) v refl q) | _ | Left M× | _ = Right (mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H ∅ M M×))
<:-reductionᴱ H (M $ N) (beta (function f ⟨ var y ∈ S ⟩∈ U is B end) v refl q) | Right r | _ | _ = Left (<:-trans-≡ (<:-resolve-⇒ r) (cong (λ F → resolve F (typeOfᴱ H ∅ N)) (cong orAny (cong typeOfᴹᴼ (sym q)))))
<:-reductionᴱ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a defn) = Left <:-refl
<:-reductionᴱ H (block var b ∈ T is B end) (block s) = Left <:-refl
<:-reductionᴱ H (block var b ∈ T is return (val v) ∙ B end) (return v) with dec-subtyping (typeOfᴱ H ∅ (val v)) T
<:-reductionᴱ H (block var b ∈ T is return (val v) ∙ B end) (return v) | Left p = Right (expr (BlockMismatch p))
<:-reductionᴱ H (block var b ∈ T is return (val v) ∙ B end) (return v) | Right p = Left p
<:-reductionᴱ H (block var b ∈ T is done end) done with dec-subtyping nill T
<:-reductionᴱ H (block var b ∈ T is done end) done | Left p = Right (expr (BlockMismatch p))
<:-reductionᴱ H (block var b ∈ T is done end) done | Right p = Left p
<:-reductionᴱ H (binexp M op N) (binOp₀ s) = Left (≡-impl-<: (sym (binOpPreservation H s)))
<:-reductionᴱ H (binexp M op N) (binOp₁ s) = Left <:-refl
<:-reductionᴱ H (binexp M op N) (binOp₂ s) = Left <:-refl

<:-reductionᴮ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a defn) = Left (<:-trans (<:-substitutivityᴮ _ B (addr a) f <:-refl) (<:-heap-weakeningᴮ (f ↦ (T ⇒ U)) H B (snoc defn)))
<:-reductionᴮ H (local var x ∈ T ← M ∙ B) (local s) = Left (<:-heap-weakeningᴮ (x ↦ T) H B (rednᴱ⊑ s))
<:-reductionᴮ H (local var x ∈ T ← M ∙ B) (subst v) with dec-subtyping (typeOfᴱ H ∅ (val v)) T
<:-reductionᴮ H (local var x ∈ T ← M ∙ B) (subst v) | Left p = Right (block (LocalVarMismatch p))
<:-reductionᴮ H (local var x ∈ T ← M ∙ B) (subst v) | Right p = Left (<:-substitutivityᴮ H B v x p)
<:-reductionᴮ H (return M ∙ B) (return s) = mapR (mapᴱᴮ+ return) (<:-reductionᴱ H M s)

≮:-reductionᴱ : ∀ H M {H′ M′ T} → (H ⊢ M ⟶ᴱ M′ ⊣ H′) → (typeOfᴱ H′ ∅ M′ ≮: T) → Either (typeOfᴱ H ∅ M ≮: T) (Warningᴱ+ H ∅ M)
≮:-reductionᴱ H M s p = mapL (λ q → <:-trans-≮: (λ {t} → q {t}) p) (<:-reductionᴱ H M s)

≮:-reductionᴮ : ∀ H B {H′ B′ T} → (H ⊢ B ⟶ᴮ B′ ⊣ H′) → (typeOfᴮ H′ ∅ B′ ≮: T) → Either (typeOfᴮ H ∅ B ≮: T) (Warningᴮ+ H ∅ B)
≮:-reductionᴮ H B s p = mapL (λ q → <:-trans-≮: (λ {t} → q {t}) p) (<:-reductionᴮ H B s)

reflect-substitutionᴱ : ∀ {Γ T} H M v x → Warningᴱ H (typeCheckᴱ H Γ (M [ v / x ]ᴱ)) → Either (Warningᴱ+ H (Γ ⊕ x ↦ T) M) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))
reflect-substitutionᴱ-whenever : ∀ {Γ T} H v x y (p : Dec(x ≡ y)) → Warningᴱ H (typeCheckᴱ H Γ (var y [ v / x ]ᴱwhenever p)) → Either (Warningᴱ+ H (Γ ⊕ x ↦ T) (var y)) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))
reflect-substitutionᴮ : ∀ {Γ T} H B v x → Warningᴮ H (typeCheckᴮ H Γ (B [ v / x ]ᴮ)) → Either (Warningᴮ+ H (Γ ⊕ x ↦ T) B) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))
reflect-substitutionᴮ-unless : ∀ {Γ T U} H B v x y (r : Dec(x ≡ y)) → Warningᴮ H (typeCheckᴮ H (Γ ⊕ y ↦ U) (B [ v / x ]ᴮunless r)) → Either (Warningᴮ+ H ((Γ ⊕ x ↦ T) ⊕ y ↦ U) B) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))
reflect-substitutionᴮ-unless-yes : ∀ {Γ Γ′ T} H B v x y (r : x ≡ y) → (Γ′ ≡ Γ) → Warningᴮ H (typeCheckᴮ H Γ (B [ v / x ]ᴮunless yes r)) → Either (Warningᴮ+ H Γ′ B) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))
reflect-substitutionᴮ-unless-no : ∀ {Γ Γ′ T} H B v x y (r : x ≢ y) → (Γ′ ≡ Γ ⊕ x ↦ T) → Warningᴮ H (typeCheckᴮ H Γ (B [ v / x ]ᴮunless no r)) → Either (Warningᴮ+ H Γ′ B) (Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (typeOfᴱ H ∅ (val v) ≮: T))

reflect-substitutionᴱ H (var y) v x W = reflect-substitutionᴱ-whenever H v x y (x ≡ⱽ y) W
reflect-substitutionᴱ H (val (addr a)) v x (UnallocatedAddress r) = Left (expr (UnallocatedAddress r))
reflect-substitutionᴱ H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) with ≮:-substitutivityᴱ H N v x p
reflect-substitutionᴱ H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Right W = Right (Right W)
reflect-substitutionᴱ H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q with ≮:-substitutivityᴱ H M v x (src-any-≮: q)
reflect-substitutionᴱ {Γ} {T} H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q | Left r with dec-Unsafe (typeOfᴱ H (Γ ⊕ x ↦ T) M) | dec-Unsafe (typeOfᴱ H (Γ ⊕ x ↦ T) N)
reflect-substitutionᴱ {Γ} {T} H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q | Left r | Left W | _ = Left (mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H (Γ ⊕ x ↦ T) M W))
reflect-substitutionᴱ {Γ} {T} H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q | Left r | _ | Left W = Left (mapᴱ+ app₂ (Unsafe-impl-Warningᴱ H (Γ ⊕ x ↦ T) N W))
reflect-substitutionᴱ H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q | Left r | Right ¬W | Right ¬V = Left (expr (FunctionCallMismatch (≮:-error ¬W) (≮:-error ¬V) (any-src-≮: q (<:-unknown ¬W) r)))
reflect-substitutionᴱ H (M $ N) v x (FunctionCallMismatch M✓ N✓ p) | Left q | Right W = Right (Right W)
reflect-substitutionᴱ {Γ} {T} H (M $ N) v x (NotFunctionCall M✓ p) with ≮:-substitutivityᴱ H M v x p | dec-Unsafe (typeOfᴱ H (Γ ⊕ x ↦ T) M)
reflect-substitutionᴱ {Γ} {T} H (M $ N) v x (NotFunctionCall M✓ p) | Left q | Left W = Left (mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H (Γ ⊕ x ↦ T) M W))
reflect-substitutionᴱ H (M $ N) v x (NotFunctionCall M✓ p) | Left q | Right ¬W = Left (expr (NotFunctionCall (≮:-error ¬W) q))
reflect-substitutionᴱ H (M $ N) v x (NotFunctionCall M✓ p) | Right W | _ = Right (Right W)
reflect-substitutionᴱ H (M $ N) v x (app₁ W) = mapL (mapᴱ+ app₁) (reflect-substitutionᴱ H M v x W)
reflect-substitutionᴱ H (M $ N) v x (app₂ W) = mapL (mapᴱ+ app₂) (reflect-substitutionᴱ H N v x W)
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (FunctionDefnMismatch q) = mapLR (expr ∘ FunctionDefnMismatch) Right (≮:-substitutivityᴮ-unless H B v x y (x ≡ⱽ y) q)
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (UnsafeFunction W′) = Left (expr (UnsafeFunction W′))
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) with reflect-substitutionᴮ-unless H B v x y (x ≡ⱽ y) W
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Left (block W′) = Left (expr (function₁ W′))
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Left (heap W′) = Left (heap W′)
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Left (ctxt (UnsafeVar z p W′)) with y ≡ⱽ z
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Left (ctxt (UnsafeVar y refl W′)) | yes refl = Left (expr (UnsafeFunction (param W′)))
reflect-substitutionᴱ {Γ} {S} H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Left (ctxt (UnsafeVar z p W′)) | no y≠z = Left (ctxt (UnsafeVar z (trans (⊕-lookup-miss y z T (Γ ⊕ x ↦ S) y≠z) p) W′))
reflect-substitutionᴱ H (function f ⟨ var y ∈ T ⟩∈ U is B end) v x (function₁ W) | Right W′ = Right W′
reflect-substitutionᴱ H (block var b ∈ T is B end) v x (BlockMismatch q) = mapLR (expr ∘ BlockMismatch) Right (≮:-substitutivityᴮ H B v x q)
reflect-substitutionᴱ H (block var b ∈ T is B end) v x (UnsafeBlock W′) = Left (expr (UnsafeBlock W′))
reflect-substitutionᴱ H (block var b ∈ T is B end) v x (block₁ W′) = mapL (mapᴮᴱ+ block₁) (reflect-substitutionᴮ H B v x W′)
reflect-substitutionᴱ {Γ} {T} H (binexp M op N) v x (BinOpMismatch₁ _ q) with dec-Unsafe (typeOfᴱ H (Γ ⊕ x ↦ T) M)
reflect-substitutionᴱ {Γ} {T} H (binexp M op N) v x (BinOpMismatch₁ _ q) | Left W = Left (mapᴱ+ bin₁ (Unsafe-impl-Warningᴱ H (Γ ⊕ x ↦ T) M W))
reflect-substitutionᴱ H (binexp M op N) v x (BinOpMismatch₁ _ q) | Right ¬W = mapLR (expr ∘ BinOpMismatch₁ (≮:-error ¬W)) Right (≮:-substitutivityᴱ H M v x q)
reflect-substitutionᴱ {Γ} {T} H (binexp M op N) v x (BinOpMismatch₂ _ q) with dec-Unsafe (typeOfᴱ H (Γ ⊕ x ↦ T) N)
reflect-substitutionᴱ {Γ} {T} H (binexp M op N) v x (BinOpMismatch₂ _ q) | Left W = Left (mapᴱ+ bin₂ (Unsafe-impl-Warningᴱ H (Γ ⊕ x ↦ T) N W))
reflect-substitutionᴱ H (binexp M op N) v x (BinOpMismatch₂ _ q) | Right ¬W = mapLR (expr ∘ BinOpMismatch₂ (≮:-error ¬W)) Right (≮:-substitutivityᴱ H N v x q)
reflect-substitutionᴱ H (binexp M op N) v x (bin₁ W) = mapL (mapᴱ+ bin₁) (reflect-substitutionᴱ H M v x W)
reflect-substitutionᴱ H (binexp M op N) v x (bin₂ W) = mapL (mapᴱ+ bin₂) (reflect-substitutionᴱ H N v x W)

reflect-substitutionᴱ-whenever H a x x (yes refl) (UnallocatedAddress p) = Right (Left (UnallocatedAddress p))
reflect-substitutionᴱ-whenever H v x y (no p) (UnboundVariable q) = Left (expr (UnboundVariable (trans (sym (⊕-lookup-miss x y _ _ p)) q)))

reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (FunctionDefnMismatch q) = mapLR (block ∘ FunctionDefnMismatch) Right (≮:-substitutivityᴮ-unless H C v x y (x ≡ⱽ y) q)
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (UnsafeFunction W) = Left (block (UnsafeFunction W))
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) with reflect-substitutionᴮ-unless H C v x y (x ≡ⱽ y) W
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Left (block W′) = Left (block (function₁ W′))
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Left (heap W′) = Left (heap W′)
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Left (ctxt (UnsafeVar z p W′)) with y ≡ⱽ z
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Left (ctxt (UnsafeVar y refl W′)) | yes refl = Left (block (UnsafeFunction (param W′)))
reflect-substitutionᴮ {Γ} {S} H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Left (ctxt (UnsafeVar z p W′)) | no y≠z = Left (ctxt (UnsafeVar z (trans (⊕-lookup-miss y z T (Γ ⊕ x ↦ S) y≠z) p) W′))
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₁ W) | Right W′ = Right W′
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) with reflect-substitutionᴮ-unless H B v x f (x ≡ⱽ f) W
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Left (block W′) = Left (block (function₂ W′))
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Left (heap W′) = Left (heap W′)
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Left (ctxt (UnsafeVar z p W′)) with f ≡ⱽ z
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Left (ctxt (UnsafeVar f refl W′)) | yes refl = Left (block (UnsafeFunction W′))
reflect-substitutionᴮ {Γ} {S} H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Left (ctxt (UnsafeVar z p W′)) | no f≠z = Left (ctxt (UnsafeVar z (trans (⊕-lookup-miss f z (T ⇒ U) (Γ ⊕ x ↦ S) f≠z) p) W′))
reflect-substitutionᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) v x (function₂ W) | Right W′ = Right W′
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (LocalVarMismatch q) = mapLR (block ∘ LocalVarMismatch) Right (≮:-substitutivityᴱ H M v x q)
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (UnsafeLocal W) = Left (block (UnsafeLocal W))
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₁ W) = mapL (mapᴱᴮ+ local₁) (reflect-substitutionᴱ H M v x W)
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) with reflect-substitutionᴮ-unless H B v x y (x ≡ⱽ y) W
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Left (block W′) = Left (block (local₂ W′))
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Left (heap W′) = Left (heap W′)
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Left (ctxt (UnsafeVar z p W′)) with y ≡ⱽ z
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Left (ctxt (UnsafeVar y refl W′)) | yes refl = Left (block (UnsafeLocal W′))
reflect-substitutionᴮ {Γ} {S} H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Left (ctxt (UnsafeVar z p W′)) | no y≠z = Left (ctxt (UnsafeVar z (trans (⊕-lookup-miss y z T (Γ ⊕ x ↦ S) y≠z) p) W′))
reflect-substitutionᴮ H (local var y ∈ T ← M ∙ B) v x (local₂ W) | Right W′ = Right W′
reflect-substitutionᴮ H (return M ∙ B) v x (return W) = mapL (mapᴱᴮ+ return) (reflect-substitutionᴱ H M v x W)

reflect-substitutionᴮ-unless H B v x y (yes p) W = reflect-substitutionᴮ-unless-yes H B v x y p (⊕-over p) W
reflect-substitutionᴮ-unless H B v x y (no p) W = reflect-substitutionᴮ-unless-no H B v x y p (⊕-swap p) W
reflect-substitutionᴮ-unless-yes H B v x x refl refl W = Left (block W)
reflect-substitutionᴮ-unless-no H B v x y p refl W = reflect-substitutionᴮ H B v x W

reflect-weakeningᴱ : ∀ Γ H M {H′} → (H ⊑ H′) → Warningᴱ H′ (typeCheckᴱ H′ Γ M) → Warningᴱ H (typeCheckᴱ H Γ M)
reflect-weakeningᴮ : ∀ Γ H B {H′} → (H ⊑ H′) → Warningᴮ H′ (typeCheckᴮ H′ Γ B) → Warningᴮ H (typeCheckᴮ H Γ B)

reflect-weakeningᴱ Γ H (var x) h (UnboundVariable p) = (UnboundVariable p)
reflect-weakeningᴱ Γ H (val (addr a)) h (UnallocatedAddress p) = UnallocatedAddress (lookup-⊑-nothing a h p)
reflect-weakeningᴱ Γ H (M $ N) h W′ with ≡-heap-weakeningᴱ Γ H M h | ≡-heap-weakeningᴱ Γ H N h
reflect-weakeningᴱ Γ H (M $ N) h W′ | Left W | _ = app₁ W
reflect-weakeningᴱ Γ H (M $ N) h W′ | _ | Left W = app₂ W
reflect-weakeningᴱ Γ H (M $ N) h (NotFunctionCall M✓ p) | Right q | Right r = NotFunctionCall (≮:-trans-≡ M✓ q) (≡-trans-≮: (sym q) p)
reflect-weakeningᴱ Γ H (M $ N) h (FunctionCallMismatch M✓ N✓ p) | Right q | Right r = FunctionCallMismatch (≮:-trans-≡ M✓ q) (≮:-trans-≡ N✓ r) (≡-trans-≮: (sym r) (≮:-trans-≡ p (cong src q)))
reflect-weakeningᴱ Γ H (M $ N) h (app₁ W′) | Right q | Right r = app₁ (reflect-weakeningᴱ Γ H M h W′)
reflect-weakeningᴱ Γ H (M $ N) h (app₂ W′) | Right q | Right r = app₂ (reflect-weakeningᴱ Γ H N h W′)
reflect-weakeningᴱ Γ H (binexp M op N) h W′ with ≡-heap-weakeningᴱ Γ H M h | ≡-heap-weakeningᴱ Γ H N h
reflect-weakeningᴱ Γ H (binexp M op N) h W′ | Left W | _ = bin₁ W
reflect-weakeningᴱ Γ H (binexp M op N) h W′ | _ | Left W = bin₂ W
reflect-weakeningᴱ Γ H (binexp M op N) h (BinOpMismatch₁ M✓ p) | Right q | Right r = BinOpMismatch₁ (≮:-trans-≡ M✓ q) (≮:-heap-weakeningᴱ Γ H M h p)
reflect-weakeningᴱ Γ H (binexp M op N) h (BinOpMismatch₂ N✓ p) | Right q | Right r = BinOpMismatch₂ (≮:-trans-≡ N✓ r) (≮:-heap-weakeningᴱ Γ H N h p)
reflect-weakeningᴱ Γ H (binexp M op N) h (bin₁ W′) | Right q | Right r = bin₁ (reflect-weakeningᴱ Γ H M h W′)
reflect-weakeningᴱ Γ H (binexp M op N) h (bin₂ W′) | Right q | Right r = bin₂ (reflect-weakeningᴱ Γ H N h W′)
reflect-weakeningᴱ Γ H (function f ⟨ var y ∈ T ⟩∈ U is B end) h (FunctionDefnMismatch p) = FunctionDefnMismatch (≮:-heap-weakeningᴮ (Γ ⊕ y ↦ T) H B h p)
reflect-weakeningᴱ Γ H (function f ⟨ var y ∈ T ⟩∈ U is B end) h (UnsafeFunction W) = UnsafeFunction W
reflect-weakeningᴱ Γ H (function f ⟨ var y ∈ T ⟩∈ U is B end) h (function₁ W) = function₁ (reflect-weakeningᴮ (Γ ⊕ y ↦ T) H B h W)
reflect-weakeningᴱ Γ H (block var b ∈ T is B end) h (BlockMismatch p) = BlockMismatch (≮:-heap-weakeningᴮ Γ H B h p)
reflect-weakeningᴱ Γ H (block var b ∈ T is B end) h (UnsafeBlock W) = UnsafeBlock W
reflect-weakeningᴱ Γ H (block var b ∈ T is B end) h (block₁ W) = block₁ (reflect-weakeningᴮ Γ H B h W)

reflect-weakeningᴮ Γ H (return M ∙ B) h (return W) = return (reflect-weakeningᴱ Γ H M h W)
reflect-weakeningᴮ Γ H (local var y ∈ T ← M ∙ B) h (LocalVarMismatch p) = LocalVarMismatch (≮:-heap-weakeningᴱ Γ H M h p)
reflect-weakeningᴮ Γ H (local var y ∈ T ← M ∙ B) h (UnsafeLocal W) = UnsafeLocal W
reflect-weakeningᴮ Γ H (local var y ∈ T ← M ∙ B) h (local₁ W) = local₁ (reflect-weakeningᴱ Γ H M h W)
reflect-weakeningᴮ Γ H (local var y ∈ T ← M ∙ B) h (local₂ W) = local₂ (reflect-weakeningᴮ (Γ ⊕ y ↦ T) H B h W)
reflect-weakeningᴮ Γ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) h (FunctionDefnMismatch p) = FunctionDefnMismatch (≮:-heap-weakeningᴮ (Γ ⊕ x ↦ T) H C h p)
reflect-weakeningᴮ Γ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) h (UnsafeFunction W) = UnsafeFunction W
reflect-weakeningᴮ Γ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) h (function₁ W) = function₁ (reflect-weakeningᴮ (Γ ⊕ x ↦ T) H C h W)
reflect-weakeningᴮ Γ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) h (function₂ W) = function₂ (reflect-weakeningᴮ (Γ ⊕ f ↦ (T ⇒ U)) H B h W)

reflect-weakeningᴼ : ∀ H O {H′} → (H ⊑ H′) → Warningᴼ H′ (typeCheckᴼ H′ O) → Warningᴼ H (typeCheckᴼ H O)
reflect-weakeningᴼ H (just function f ⟨ var x ∈ T ⟩∈ U is B end) h (FunctionDefnMismatch p) = FunctionDefnMismatch (≮:-heap-weakeningᴮ (x ↦ T) H B h p)
reflect-weakeningᴼ H (just function f ⟨ var x ∈ T ⟩∈ U is B end) h (UnsafeFunction W) = UnsafeFunction W
reflect-weakeningᴼ H (just function f ⟨ var x ∈ T ⟩∈ U is B end) h (function₁ W) = function₁ (reflect-weakeningᴮ (x ↦ T) H B h W)

reflectᴱ : ∀ H M {H′ M′} → (H ⊢ M ⟶ᴱ M′ ⊣ H′) → Warningᴱ H′ (typeCheckᴱ H′ ∅ M′) → Warningᴱ+ H ∅ M
reflectᴮ : ∀ H B {H′ B′} → (H ⊢ B ⟶ᴮ B′ ⊣ H′) → Warningᴮ H′ (typeCheckᴮ H′ ∅ B′) → Warningᴮ+ H ∅ B

reflectᴱ H (M $ N) s W′ with dec-Unsafe (typeOfᴱ H ∅ M) | dec-Unsafe (typeOfᴱ H ∅ N)
reflectᴱ H (M $ N) s W′ | Left W | _ = mapᴱ+ app₁ (Unsafe-impl-Warningᴱ H ∅ M W)
reflectᴱ H (M $ N) s W′ | _ | Left W = mapᴱ+ app₂ (Unsafe-impl-Warningᴱ H ∅ N W)
reflectᴱ H (M $ N) (app₁ s) (FunctionCallMismatch M✓ N✓ p) | Right ¬W | Right ¬V = cond (expr ∘ FunctionCallMismatch (≮:-error ¬W) (≮:-error ¬V) ∘ ≮:-heap-weakeningᴱ ∅ H N (rednᴱ⊑ s) ∘ any-src-≮: p (<:-unknown ¬W)) (mapᴱ+ app₁) (≮:-reductionᴱ H M s (src-any-≮: p))
reflectᴱ H (M $ N) (app₁ s) (NotFunctionCall M✓  p) | Right ¬W | Right ¬V = cond (expr ∘ NotFunctionCall (≮:-error ¬W)) (mapᴱ+ app₁) (≮:-reductionᴱ H M s p)
reflectᴱ H (M $ N) (app₁ s) (app₁ W′) | Right ¬W | Right ¬V = mapᴱ+ app₁ (reflectᴱ H M s W′)
reflectᴱ H (M $ N) (app₁ s) (app₂ W′) | Right ¬W | Right ¬V = expr (app₂ (reflect-weakeningᴱ ∅ H N (rednᴱ⊑ s) W′))
reflectᴱ H (M $ N) (app₂ p s) (FunctionCallMismatch M✓ N✓ q) | Right ¬W | Right ¬V with (≮:-reductionᴱ H N s q)
reflectᴱ H (M $ N) (app₂ p s) (FunctionCallMismatch M✓ N✓ q) | Right ¬W | Right ¬V | Left r = expr (FunctionCallMismatch (≮:-error ¬W) (≮:-error ¬V) (any-src-≮: r (<:-unknown ¬W) (≮:-heap-weakeningᴱ ∅ H M (rednᴱ⊑ s) (src-any-≮: r))))
reflectᴱ H (M $ N) (app₂ p s) (FunctionCallMismatch M✓ N✓ q) | Right ¬W | Right ¬V | Right W = mapᴱ+ app₂ W
reflectᴱ H (M $ N) (app₂ p s) (NotFunctionCall M✓ q) | Right ¬W | Right ¬V = expr (NotFunctionCall (≮:-error ¬W) (≮:-heap-weakeningᴱ ∅ H M (rednᴱ⊑ s) q))
reflectᴱ H (M $ N) (app₂ p s) (app₁ W′) | Right ¬W | Right ¬V = expr (app₁ (reflect-weakeningᴱ ∅ H M (rednᴱ⊑ s) W′))
reflectᴱ H (M $ N) (app₂ p s) (app₂ W′) | Right ¬W | Right ¬V = mapᴱ+ app₂ (reflectᴱ H N s W′)
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (BlockMismatch q) | Right ¬W | Right ¬V with ≮:-substitutivityᴮ H B v x q 
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (BlockMismatch q) | Right ¬W | Right ¬V | Left r = heap (addr a p (FunctionDefnMismatch r))
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (BlockMismatch q) | Right ¬W | Right ¬V | Right r = expr (FunctionCallMismatch (≮:-error ¬W) (≮:-error ¬V) (≮:-trans-≡ r ((cong src (cong orAny (cong typeOfᴹᴼ (sym p)))))))
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (UnsafeBlock q) | Right ¬W | Right ¬V = heap (addr a p (UnsafeFunction (result q)))
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V with reflect-substitutionᴮ _ B v x W′
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Left (block W) = heap (addr a p (function₁ W))
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Left (heap W) = heap W
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Left (ctxt (UnsafeVar y q W)) with x ≡ⱽ y
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Left (ctxt (UnsafeVar x refl W)) | yes refl = heap (addr a p (UnsafeFunction (param W)))
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Left (ctxt (UnsafeVar y q W)) | no x≠y = ctxt (UnsafeVar y (trans (⊕-lookup-miss x y T ∅ x≠y) q) W)
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Right (Left W) = expr (app₂ W)
reflectᴱ H (val (addr a) $ N) (beta (function f ⟨ var x ∈ T ⟩∈ U is B end) v refl p) (block₁ W′) | Right ¬W | Right ¬V | Right (Right q) = expr (FunctionCallMismatch (≮:-error ¬W) (≮:-error ¬V) (≮:-trans-≡ q (cong src (cong orAny (cong typeOfᴹᴼ (sym p))))))
reflectᴱ H (block var b ∈ T is B end) (block s) (BlockMismatch p) = cond (expr ∘ BlockMismatch) (mapᴮᴱ+ block₁) (≮:-reductionᴮ H B s p)
reflectᴱ H (block var b ∈ T is B end) (block s) (UnsafeBlock p) = expr (UnsafeBlock p)
reflectᴱ H (block var b ∈ T is B end) (block s) (block₁ W′) = mapᴮᴱ+ block₁ (reflectᴮ H B s W′)
reflectᴱ H (block var b ∈ T is B end) (return v) W′ = expr (block₁ (return W′))
reflectᴱ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a defn) (UnallocatedAddress ())
reflectᴱ H (binexp M op N) s W′ with dec-Unsafe (typeOfᴱ H ∅ M) | dec-Unsafe (typeOfᴱ H ∅ N)
reflectᴱ H (binexp M op N) s W′ | Left W | _ = mapᴱ+ bin₁ (Unsafe-impl-Warningᴱ H ∅ M W)
reflectᴱ H (binexp M op N) s W′ | _ | Left W = mapᴱ+ bin₂ (Unsafe-impl-Warningᴱ H ∅ N W)
reflectᴱ H (binexp M op N) (binOp₀ ()) (UnallocatedAddress p) | Right ¬W | Right ¬V 
reflectᴱ H (binexp M op N) (binOp₁ s) (BinOpMismatch₁ M✓ p) | Right ¬W | Right ¬V  = cond (expr ∘ BinOpMismatch₁ (≮:-error ¬W)) (mapᴱ+ bin₁) (≮:-reductionᴱ H M s p)
reflectᴱ H (binexp M op N) (binOp₁ s) (BinOpMismatch₂ N✓ p) | Right ¬W | Right ¬V  = expr (BinOpMismatch₂ (≮:-error ¬V) (≮:-heap-weakeningᴱ ∅ H N (rednᴱ⊑ s) p))
reflectᴱ H (binexp M op N) (binOp₁ s) (bin₁ W′) | Right ¬W | Right ¬V  = mapᴱ+ bin₁ (reflectᴱ H M s W′)
reflectᴱ H (binexp M op N) (binOp₁ s) (bin₂ W′) | Right ¬W | Right ¬V  = expr (bin₂ (reflect-weakeningᴱ ∅ H N (rednᴱ⊑ s) W′))
reflectᴱ H (binexp M op N) (binOp₂ s) (BinOpMismatch₁ M✓ p) | Right ¬W | Right ¬V  = expr (BinOpMismatch₁ (≮:-error ¬W) (≮:-heap-weakeningᴱ ∅ H M (rednᴱ⊑ s) p))
reflectᴱ H (binexp M op N) (binOp₂ s) (BinOpMismatch₂ N✓ p) | Right ¬W | Right ¬V  = cond (expr ∘ BinOpMismatch₂ (≮:-error ¬V)) (mapᴱ+ bin₂) (≮:-reductionᴱ H N s p)
reflectᴱ H (binexp M op N) (binOp₂ s) (bin₁ W′) | Right ¬W | Right ¬V  = expr (bin₁ (reflect-weakeningᴱ ∅ H M (rednᴱ⊑ s) W′))
reflectᴱ H (binexp M op N) (binOp₂ s) (bin₂ W′) | Right ¬W | Right ¬V  = mapᴱ+ bin₂ (reflectᴱ H N s W′)

reflectᴮ H (local var x ∈ T ← M ∙ B) (local s) (LocalVarMismatch p) = cond (block ∘ LocalVarMismatch) (mapᴱᴮ+ local₁) (≮:-reductionᴱ H M s p)
reflectᴮ H (local var x ∈ T ← M ∙ B) (local s) (local₁ W′) = mapᴱᴮ+ local₁ (reflectᴱ H M s W′)
reflectᴮ H (local var x ∈ T ← M ∙ B) (local s) (local₂ W′) = block (local₂ (reflect-weakeningᴮ (x ↦ T) H B (rednᴱ⊑ s) W′))
reflectᴮ H (local var x ∈ T ← M ∙ B) (local s) (UnsafeLocal W′) = block (UnsafeLocal W′)
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ with reflect-substitutionᴮ H B v x W′
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Left (block W) = block (local₂ W)
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Left (heap W) = heap W
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Left (ctxt (UnsafeVar y p W)) with x ≡ⱽ y
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Left (ctxt (UnsafeVar x refl W)) | yes refl = block (UnsafeLocal W)
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Left (ctxt (UnsafeVar y p W)) | no x≠y = ctxt (UnsafeVar y (trans (⊕-lookup-miss x y T ∅ x≠y) p) W)
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Right (Left W) = block (local₁ W)
reflectᴮ H (local var x ∈ T ← M ∙ B) (subst v) W′ | Right (Right W) = block (LocalVarMismatch W)
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ with reflect-substitutionᴮ _ B (addr a) f W′
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (block W) = block (function₂ (reflect-weakeningᴮ (f ↦ (T ⇒ U)) H B (snoc defn) W))
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (heap (addr b p W)) with b ≡ᴬ a
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (heap (addr a refl (FunctionDefnMismatch W))) | yes refl = block (FunctionDefnMismatch (≮:-heap-weakeningᴮ (y ↦ T) H C (snoc defn) W))
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (heap (addr a refl (function₁ W))) | yes refl = block (function₁ (reflect-weakeningᴮ (y ↦ T) H C (snoc defn) W))
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (heap (addr a refl (UnsafeFunction W))) | yes refl = block (UnsafeFunction W)
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (heap (addr b p W)) | no a≠b = heap (addr b (trans (lookup-not-allocated {H = H} defn a≠b) p) (reflect-weakeningᴼ H _ (snoc defn) W))
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (ctxt (UnsafeVar x p W)) with f ≡ⱽ x
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (ctxt (UnsafeVar x refl W)) | yes refl = block (UnsafeFunction W)
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Left (ctxt (UnsafeVar x p W)) | no f≠x = ctxt (UnsafeVar x (trans (⊕-lookup-miss f x (T ⇒ U) ∅ f≠x) p) W)
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Right (Left (UnallocatedAddress ()))
reflectᴮ H (function f ⟨ var y ∈ T ⟩∈ U is C end ∙ B) (function a defn) W′ | Right (Right p) = CONTRADICTION (≮:-refl p)
reflectᴮ H (return M ∙ B) (return s) (return W′) = mapᴱᴮ+ return (reflectᴱ H M s W′)

reflectᴱ+ : ∀ H M {H′ M′} → (H ⊢ M ⟶ᴱ M′ ⊣ H′) → Warningᴱ+ H′ ∅ M′ → Warningᴱ+ H ∅ M
reflectᴮ+ : ∀ H B {H′ B′} → (H ⊢ B ⟶ᴮ B′ ⊣ H′) → Warningᴮ+ H′ ∅ B′ → Warningᴮ+ H ∅ B

reflectᴱ+ H M S (expr W′) = reflectᴱ H M S W′
reflectᴱ+ H (M $ N) (app₁ s) (heap W) = mapᴱ+ app₁ (reflectᴱ+ H M s (heap W))
reflectᴱ+ H (M $ N) (app₂ v s) (heap W) = mapᴱ+ app₂ (reflectᴱ+ H N s (heap W))
reflectᴱ+ H (M $ N) (beta O v refl p) (heap W) = heap W
reflectᴱ+ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a p) (heap (addr b refl W)) with b ≡ᴬ a
reflectᴱ+ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a defn) (heap (addr b refl (FunctionDefnMismatch p))) | yes refl = expr (FunctionDefnMismatch (≮:-heap-weakeningᴮ (x ↦ T) H B (snoc defn) p))
reflectᴱ+ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a defn) (heap (addr b refl (function₁ W))) | yes refl = expr (function₁ (reflect-weakeningᴮ (x ↦ T) H B (snoc defn) W))
reflectᴱ+ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a defn) (heap (addr b refl (UnsafeFunction W))) | yes refl = expr (UnsafeFunction W)
reflectᴱ+ H (function f ⟨ var x ∈ T ⟩∈ U is B end) (function a p) (heap (addr b refl W)) | no q = heap (addr b (lookup-not-allocated p q) (reflect-weakeningᴼ H _ (snoc p) W))
reflectᴱ+ H (block var b ∈ T is B end) (block s) (heap W) = mapᴮᴱ+ block₁ (reflectᴮ+ H B s (heap W))
reflectᴱ+ H (block var b ∈ T is return (val v) ∙ B end) (return v) (heap W) = heap W
reflectᴱ+ H (block var b ∈ T is done end) done (heap W) = heap W
reflectᴱ+ H (binexp M op N) (binOp₀ s) (heap W) = heap W
reflectᴱ+ H (binexp M op N) (binOp₁ s) (heap W) = mapᴱ+ bin₁ (reflectᴱ+ H M s (heap W))
reflectᴱ+ H (binexp M op N) (binOp₂ s) (heap W) = mapᴱ+ bin₂ (reflectᴱ+ H N s (heap W))
reflectᴱ+ H M S (ctxt (UnsafeVar x () W′))

reflectᴮ+ H B S (block W′) = reflectᴮ H B S W′
reflectᴮ+ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a p) (heap (addr b refl W)) with b ≡ᴬ a
reflectᴮ+ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a defn) (heap (addr b refl (FunctionDefnMismatch p))) | yes refl = block (FunctionDefnMismatch (≮:-heap-weakeningᴮ (x ↦ T) H C (snoc defn) p))
reflectᴮ+ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a defn) (heap (addr b refl (function₁ W))) | yes refl = block (function₁ (reflect-weakeningᴮ (x ↦ T) H C (snoc defn) W))
reflectᴮ+ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a defn) (heap (addr b refl (UnsafeFunction W))) | yes refl = block (UnsafeFunction W)
reflectᴮ+ H (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function a p) (heap (addr b refl W)) | no q = heap (addr b (lookup-not-allocated p q) (reflect-weakeningᴼ H _ (snoc p) W))
reflectᴮ+ H (local var x ∈ T ← M ∙ B) (local s) (heap W) = mapᴱᴮ+ local₁ (reflectᴱ+ H M s (heap W))
reflectᴮ+ H (local var x ∈ T ← M ∙ B) (subst v) (heap W) = heap W
reflectᴮ+ H (return M ∙ B) (return s) (heap W) = mapᴱᴮ+ return (reflectᴱ+ H M s (heap W))
reflectᴮ+ H B S (ctxt (UnsafeVar x () W′))

reflect* : ∀ H B {H′ B′} → (H ⊢ B ⟶* B′ ⊣ H′) → Warningᴮ+ H′ ∅ B′ → Warningᴮ+ H ∅ B
reflect* H B refl W = W
reflect* H B (step s t) W = reflectᴮ+ H B s (reflect* _ _ t W)

isntNumber : ∀ H v → (valueType v ≢ num) → (typeOfᴱ H ∅ (val v) ≮: number)
isntNumber H nil p = scalar-≢-impl-≮: NIL NUMBER (λ ())
isntNumber H (addr a) p with remember (H [ a ]ᴴ)
isntNumber H (addr a) p | (just (function f ⟨ var x ∈ T ⟩∈ U is B end) , q) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ q)) (function-≮:-scalar NUMBER)
isntNumber H (addr a) p | (nothing , q) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ q)) (any-≮:-scalar NUMBER)
isntNumber H (num x) p = CONTRADICTION (p refl)
isntNumber H (bool x) p = scalar-≢-impl-≮: BOOLEAN NUMBER (λ ())
isntNumber H (str x) p = scalar-≢-impl-≮: STRING NUMBER (λ ())

isntString : ∀ H v → (valueType v ≢ str) → (typeOfᴱ H ∅ (val v) ≮: string)
isntString H nil p = scalar-≢-impl-≮: NIL STRING (λ ())
isntString H (addr a) p with remember (H [ a ]ᴴ)
isntString H (addr a) p | (just (function f ⟨ var x ∈ T ⟩∈ U is B end) , q) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ q)) (function-≮:-scalar STRING)
isntString H (addr a) p | (nothing , q) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ q)) (any-≮:-scalar STRING)
isntString H (num x) p = scalar-≢-impl-≮: NUMBER STRING (λ ())
isntString H (bool x) p = scalar-≢-impl-≮: BOOLEAN STRING (λ ())
isntString H (str x) p = CONTRADICTION (p refl)

isntFunction : ∀ H v {T U} → (valueType v ≢ function) → (typeOfᴱ H ∅ (val v) ≮: (T ⇒ U))
isntFunction H nil p = scalar-≮:-function NIL
isntFunction H (addr a) p = CONTRADICTION (p refl)
isntFunction H (num x) p = scalar-≮:-function NUMBER
isntFunction H (bool x) p = scalar-≮:-function BOOLEAN
isntFunction H (str x) p = scalar-≮:-function STRING

isntEmpty : ∀ H v → (typeOfᴱ H ∅ (val v) ≮: never)
isntEmpty H nil = scalar-≮:-never NIL
isntEmpty H (addr a) with remember (H [ a ]ᴴ)
isntEmpty H (addr a) | (just (function f ⟨ var x ∈ T ⟩∈ U is B end) , p) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ p)) function-≮:-never
isntEmpty H (addr a) | (nothing , p) = ≡-trans-≮: (cong orAny (cong typeOfᴹᴼ p)) any-≮:-never
isntEmpty H (num x) = scalar-≮:-never NUMBER
isntEmpty H (bool x) = scalar-≮:-never BOOLEAN
isntEmpty H (str x) = scalar-≮:-never STRING

isntError : ∀ H v → Either (Warningᴱ H (typeCheckᴱ H ∅ (val v))) (error ≮: typeOfᴱ H ∅ (val v))
isntError H nil = Right (error-≮:-scalar NIL)
isntError H (addr a) with remember (H [ a ]ᴴ)
isntError H (addr a) | (nothing , q) = Left (UnallocatedAddress q)
isntError H (addr a) | (just (function f ⟨ var x ∈ T ⟩∈ U is B end) , q) = Right (≮:-trans-≡ error-≮:-function (cong orAny (cong typeOfᴹᴼ (sym q))))
isntError H (num x) = Right (error-≮:-scalar NUMBER)
isntError H (bool x) = Right (error-≮:-scalar BOOLEAN)
isntError H (str x) = Right (error-≮:-scalar STRING)

runtimeBinOpWarning : ∀ H {op} v → BinOpError op (valueType v) → (typeOfᴱ H ∅ (val v) ≮: srcBinOp op)
runtimeBinOpWarning H v (+ p) = isntNumber H v p
runtimeBinOpWarning H v (- p) = isntNumber H v p
runtimeBinOpWarning H v (* p) = isntNumber H v p
runtimeBinOpWarning H v (/ p) = isntNumber H v p
runtimeBinOpWarning H v (< p) = isntNumber H v p
runtimeBinOpWarning H v (> p) = isntNumber H v p
runtimeBinOpWarning H v (<= p) = isntNumber H v p
runtimeBinOpWarning H v (>= p) = isntNumber H v p
runtimeBinOpWarning H v (·· p) = isntString H v p

runtimeWarningᴱ : ∀ H M → RuntimeErrorᴱ H M → Warningᴱ H (typeCheckᴱ H ∅ M)
runtimeWarningᴮ : ∀ H B → RuntimeErrorᴮ H B → Warningᴮ H (typeCheckᴮ H ∅ B)

runtimeWarningᴱ H (var x) UnboundVariable = UnboundVariable refl
runtimeWarningᴱ H (val (addr a)) (SEGV p) = UnallocatedAddress p
runtimeWarningᴱ H (M $ N) (FunctionMismatch v w p) with isntError H v
runtimeWarningᴱ H (M $ N) (FunctionMismatch v w p) | Left W = app₁ W
runtimeWarningᴱ H (M $ N) (FunctionMismatch v w p) | Right r = NotFunctionCall r (isntFunction H v p)
runtimeWarningᴱ H (M $ N) (app₁ err) = app₁ (runtimeWarningᴱ H M err)
runtimeWarningᴱ H (M $ N) (app₂ err) = app₂ (runtimeWarningᴱ H N err)
runtimeWarningᴱ H (block var b ∈ T is B end) (block err) = block₁ (runtimeWarningᴮ H B err)
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₁ v w p) with isntError H v
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₁ v w p) | Left W = bin₁ W
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₁ v w p) | Right r = BinOpMismatch₁ r (runtimeBinOpWarning H v p)
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₂ v w p) with isntError H w
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₂ v w p) | Left W = bin₂ W
runtimeWarningᴱ H (binexp M op N) (BinOpMismatch₂ v w p) | Right r = BinOpMismatch₂ r (runtimeBinOpWarning H w p)
runtimeWarningᴱ H (binexp M op N) (bin₁ err) = bin₁ (runtimeWarningᴱ H M err)
runtimeWarningᴱ H (binexp M op N) (bin₂ err) = bin₂ (runtimeWarningᴱ H N err)

runtimeWarningᴮ H (local var x ∈ T ← M ∙ B) (local err) = local₁ (runtimeWarningᴱ H M err)
runtimeWarningᴮ H (return M ∙ B) (return err) = return (runtimeWarningᴱ H M err)

wellTypedProgramsDontGoWrong : ∀ H′ B B′ → (∅ᴴ ⊢ B ⟶* B′ ⊣ H′) → (RuntimeErrorᴮ H′ B′) → Warningᴮ ∅ᴴ (typeCheckᴮ ∅ᴴ ∅ B)
wellTypedProgramsDontGoWrong H′ B B′ t err with reflect* ∅ᴴ B t (block (runtimeWarningᴮ H′ B′ err))
wellTypedProgramsDontGoWrong H′ B B′ t err | heap (addr a refl ())
wellTypedProgramsDontGoWrong H′ B B′ t err | ctxt (UnsafeVar x () p)
wellTypedProgramsDontGoWrong H′ B B′ t err | block W = W
