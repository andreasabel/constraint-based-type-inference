{-# OPTIONS --postfix-projections #-}

module _ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Substitution as Sub

module Vec where
  open import Data.Vec public
  open import Data.Vec.Properties public
open Vec using (Vec; []; _∷_; lookup)

open import Function using (id)

import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; refl; cong₂; module ≡-Reasoning)
open ≡-Reasoning

infix   4 _↘_
infixl  6 _∙_
infix   8 _≐_
infixr 10 _⇒_

variable
  n m : ℕ

------------------------------------------------------------------------
-- Data structures.

-- Well-scoped terms.

data Exp : ℕ → Set where
  var : (x : Fin n) → Exp n
  abs : (e : Exp (suc n)) → Exp n
  app : (f e : Exp n) → Exp n

-- Type variables.

TyCxt = ℕ

TyVar : (Ξ : TyCxt) → Set
TyVar = Fin

-- Types.

data Ty (Ξ : TyCxt) : Set where
  tyvar : (X : TyVar Ξ) → Ty Ξ
  _⇒_   : (A B : Ty Ξ) → Ty Ξ

-- Typing contexts.

Cxt : (Ξ : TyCxt) (n : ℕ) → Set
Cxt Ξ n = Vec (Ty Ξ) n

variable
  Ξ Ξ' Ξ′ Ξ₁ Ξ₂ : TyCxt
  X Y Z         : TyVar Ξ
  A A′ B B′ C   : Ty Ξ
  Γ Γ' Γ′ Γ₁ Γ₂ : Cxt Ξ n
  x             : Fin n
  e f           : Exp n

-- Well-typed terms.

data Tm (Γ : Cxt Ξ n) : (e : Exp n) → Ty Ξ → Set where
  var :  Tm Γ (var x) (lookup Γ x)
  app : (t : Tm Γ f (A ⇒ B)) (u : Tm Γ e A) → Tm Γ (app f e) B
  abs : (t : Tm (A ∷ Γ) e B) → Tm Γ (abs e) (A ⇒ B)

-- Constraints (equations)

data Eqs Ξ : Set where
  ε   : Eqs Ξ
  _≐_ : (A B : Ty Ξ) → Eqs Ξ
  _∙_ : (E F : Eqs Ξ) → Eqs Ξ

variable
  E E′ F G : Eqs Ξ

------------------------------------------------------------------------
-- Renamings and substitutions.

-- Renamings.

_⊆_ : (Ξ Ξ₁ : TyCxt) → Set
Ξ ⊆ Ξ₁ = Sub.Sub TyVar Ξ Ξ₁

module R = Sub.VarSubst

variable
  η η' η′ η₁ η₂ : Ξ ⊆ Ξ₁

-- Substitutions.

Subst : (Ξ Ξ₁ : TyCxt) → Set
Subst Ξ Ξ₁ = Sub.Sub Ty Ξ Ξ₁

module ApplySubstitution {T : TyCxt → Set} (l : Sub.Lift T Ty) (open Sub.Lift l) where

  infixl 9 _/_

  _/_ : Ty Ξ → Sub.Sub T Ξ Ξ₁ → Ty Ξ₁
  tyvar x / ρ = lift (Vec.lookup ρ x)
  t₁ ⇒ t₂ / ρ = (t₁ / ρ) ⇒ (t₂ / ρ)

  -- module A = Sub.Application (record { _/_ = _/_ })
  -- open A public hiding (_/_)

tySubst : Sub.TermSubst Ty
tySubst .Sub.TermSubst.var = tyvar
tySubst .Sub.TermSubst.app = ApplySubstitution._/_

module S = Sub.TermSubst tySubst

-- Applications of renamings.

wkTyVar : Ξ ⊆ Ξ₁ → TyVar Ξ → TyVar Ξ₁
wkTyVar = Vec.lookup

wkTy : (η : Ξ ⊆ Ξ₁) → Ty Ξ → Ty Ξ₁
wkTy η A = A S./Var η

wkTy1 : Ty Ξ → Ty (suc Ξ)
wkTy1 = wkTy R.wk

wkCxt : (η : Ξ ⊆ Ξ₁) → Cxt Ξ n → Cxt Ξ₁ n
wkCxt η [] = []
wkCxt η (A ∷ Γ) = wkTy η A ∷ wkCxt η Γ

wkCxt1 : Cxt Ξ n → Cxt (suc Ξ) n
wkCxt1 = wkCxt R.wk

wkEqs : (η : Ξ ⊆ Ξ₁) → Eqs Ξ → Eqs Ξ₁
wkEqs η ε = ε
wkEqs η (A ≐ B) = wkTy η A ≐ wkTy η B
wkEqs η (E ∙ F) = wkEqs η E ∙ wkEqs η F

wkEqs1 : Eqs Ξ → Eqs (suc Ξ)
wkEqs1 = wkEqs R.wk

-- Application of substitutions.

variable
  σ τ : Subst Ξ Ξ₁

subTyVar : Subst Ξ Ξ₁ → TyVar Ξ → Ty Ξ₁
subTyVar σ = Vec.lookup σ

subTy : Subst Ξ Ξ₁ → Ty Ξ → Ty Ξ₁
subTy σ A = A S./ σ

subCxt : Subst Ξ Ξ₁ → Cxt Ξ n → Cxt Ξ₁ n
subCxt σ = Vec.map (subTy σ)

subEqs : Subst Ξ Ξ₁ → Eqs Ξ → Eqs Ξ₁
subEqs σ ε = ε
subEqs σ (A ≐ B) = subTy σ A ≐ subTy σ B
subEqs σ (E ∙ F) = subEqs σ E ∙ subEqs σ F

subSub : Subst Ξ₁ Ξ₂ → Subst Ξ Ξ₁ → Subst Ξ Ξ₂
subSub σ σ′ = σ′ S.⊙ σ

-- Constructions of substitutions.

emptySub : Subst zero zero
emptySub = []

wkSub : Ξ₁ ⊆ Ξ₂ → Subst Ξ Ξ₁ → Subst Ξ Ξ₂
wkSub η σ = Vec.map (wkTy η) σ

wkSub1 : Subst Ξ Ξ₁ → Subst Ξ (suc Ξ₁)
wkSub1 = wkSub R.wk

liftSub : Subst Ξ Ξ₁ → Subst (suc Ξ) (suc Ξ₁)
liftSub σ = σ S.↑

idSub : Subst Ξ Ξ
idSub = S.id

renSub : Ξ ⊆ Ξ₁ → Subst Ξ Ξ₁
renSub = Vec.map tyvar

------------------------------------------------------------------------
-- Laws of renaming and substitution.

-- Identity laws.
-- Get these laws from the Substitution library?

wkTyVar-id : wkTyVar R.id X ≡ X
wkTyVar-id {X = zero} = refl
wkTyVar-id {X = suc X} rewrite Vec.lookup-map X Fin.suc R.id = ≡.cong suc wkTyVar-id

wkTy-id : wkTy R.id A ≡ A
wkTy-id {A = tyvar X} = ≡.cong tyvar wkTyVar-id
wkTy-id {A = A ⇒ B} = ≡.cong₂ _⇒_ wkTy-id wkTy-id

wkCxt-id : wkCxt R.id Γ ≡ Γ
wkCxt-id {Γ = []} = refl
wkCxt-id {Γ = A ∷ Γ} = ≡.cong₂ _∷_ wkTy-id wkCxt-id

subTyVar-id : subTyVar idSub X ≡ tyvar X
subTyVar-id {X = zero} = refl
subTyVar-id {X = suc X}
  rewrite Vec.lookup-map X (wkTy R.wk) idSub
        | subTyVar-id {X = X}
        | Vec.lookup-map X Fin.suc R.id
        | wkTyVar-id {X = X}
        = refl

subTy-id : subTy idSub A ≡ A
subTy-id {A = tyvar X} = subTyVar-id
subTy-id {A = A ⇒ B} = ≡.cong₂ _⇒_ subTy-id subTy-id

subCxt-id : subCxt idSub Γ ≡ Γ
subCxt-id {Γ = []} = refl
subCxt-id {Γ = A ∷ Γ} = ≡.cong₂ _∷_ subTy-id subCxt-id

-- Composition laws.

-- Renaming-renaming.

wkTyVar-wkTyVar : wkTyVar η (wkTyVar η′ X) ≡ wkTyVar (η′ R.⊙ η) X
wkTyVar-wkTyVar         {η′ = _ ∷ η′} {X = zero}  = refl
wkTyVar-wkTyVar {η = η} {η′ = _ ∷ η′} {X = suc X} = wkTyVar-wkTyVar {η = η} {η′ = η′} {X = X}

wkTy-wkTy : wkTy η (wkTy η′ A) ≡ wkTy (η′ R.⊙ η) A
wkTy-wkTy {η = η} {η′ = η′} {A = tyvar X} = ≡.cong tyvar (wkTyVar-wkTyVar {η = η} {η′ = η′} {X = X})
wkTy-wkTy {A = A ⇒ B} = ≡.cong₂ _⇒_ (wkTy-wkTy {A = A}) (wkTy-wkTy {A = B})

wkCxt-wkCxt : wkCxt η (wkCxt η′ Γ) ≡ wkCxt (η′ R.⊙ η) Γ
wkCxt-wkCxt {Γ = []} = refl
wkCxt-wkCxt {Γ = A ∷ Γ} = ≡.cong₂ _∷_ (wkTy-wkTy {A = A}) wkCxt-wkCxt

-- Substitution-renaming.

subTyVar-wkTyVar : subTyVar σ (wkTyVar η X) ≡ subTyVar (renSub η S.⊙ σ) X
subTyVar-wkTyVar {η = Y ∷ η} {X = zero} = refl
subTyVar-wkTyVar {η = Y ∷ η} {X = suc X} = subTyVar-wkTyVar {η = η} {X = X}

subTy-wkTy : subTy σ (wkTy η A) ≡ subTy (renSub η S.⊙ σ) A
subTy-wkTy {σ = σ} {η = η} {A = tyvar X} = subTyVar-wkTyVar {σ = σ} {η = η}
subTy-wkTy {σ = σ} {η = η} {A = A ⇒ B} = cong₂ _⇒_ (subTy-wkTy {A = A}) (subTy-wkTy {A = B})

-- Substitution-substitution.

subTy-subTyVar : subTy σ (subTyVar τ X) ≡ subTyVar (τ S.⊙ σ) X
subTy-subTyVar {τ = _ ∷ τ} {X = zero} = refl
subTy-subTyVar {τ = _ ∷ τ} {X = suc X} = subTy-subTyVar {τ = τ} {X = X}

subTy-subTy : subTy σ (subTy τ A) ≡ subTy (τ S.⊙ σ) A
subTy-subTy {σ = σ} {τ = τ} {A = tyvar X} = subTy-subTyVar {σ = σ} {τ = τ}
subTy-subTy {σ = σ} {τ = τ} {A = A ⇒ B} = cong₂ _⇒_ (subTy-subTy {A = A}) (subTy-subTy {A = B})

-- A substitution that is just a renaming.

subTyVar-renSub : ∀ (η : Ξ ⊆ Ξ′) (X : TyVar Ξ) →

  subTyVar (renSub η) X ≡ tyvar (wkTyVar η X)

subTyVar-renSub (Y ∷ η) zero    = refl
subTyVar-renSub (Y ∷ η) (suc X) = subTyVar-renSub η X

-- Looking up a variable in a substituted context.

subTy-lookup : lookup (subCxt σ Γ) x ≡ subTy σ (lookup Γ x)
subTy-lookup {σ = σ} {Γ = Γ} {x = x} = Vec.lookup-map x (subTy σ) Γ

------------------------------------------------------------------------
-- Constraint-based type inference.

data Inf : (Γ : Cxt Ξ n) (e : Exp n) (η : Ξ ⊆ Ξ₁) (A : Ty Ξ₁) (E : Eqs Ξ₁) → Set where
  var : Inf Γ (var x) R.id (lookup Γ x) ε

  abs : let X =  tyvar zero
     in Inf (X ∷ wkCxt1 Γ) e η A E
      → Inf Γ (abs e) (R.wk R.⊙ η) (wkTy η X ⇒ A) E

  app : Inf Γ f η₁ C E
      → Inf (wkCxt η₁ Γ) e η₂ A F
      → let X   = tyvar zero
            η₂′ = η₂ R.⊙ R.wk
     in Inf Γ (app f e) (η₁ R.⊙ η₂′) X (wkEqs η₂′ E ∙ (wkEqs1 F ∙ (wkTy η₂′ C ≐ wkTy1 A ⇒ X)))

-- Constraint satisfaction σ ⊧ E.

data _⊧_ (σ : Subst Ξ Ξ₁) : Eqs Ξ → Set where
  ε  : σ ⊧ ε
  sg : subTy σ A ≡ subTy σ B → σ ⊧ (A ≐ B)
  _∙_ : σ ⊧ E → σ ⊧ F → σ ⊧ (E ∙ F)

-- Laws of satisfaction.

sat-arr : σ ⊧ (A ≐ A′ ∙ B ≐ B′) → σ ⊧ (A ⇒ B ≐ A′ ⇒ B′)
sat-arr (sg eqA ∙ sg eqB) = sg (≡.cong₂ _⇒_ eqA eqB)

-- We can compose a substitution on the constraints onto the solution of the unsubstituted constraints.

sat-wk : σ ⊧ wkEqs η E → (renSub η S.⊙ σ) ⊧ E
sat-wk {E = ε} ε = ε
sat-wk {η = η} {E = A ≐ B} (sg eq) = sg (≡.subst₂ _≡_ (subTy-wkTy {η = η} {A = A}) (subTy-wkTy {η = η} {A = B}) eq)
sat-wk {E = E ∙ E₁} (s ∙ s₁) = sat-wk s ∙ sat-wk s₁

sat-sub : σ ⊧ subEqs τ E → (τ S.⊙ σ) ⊧ E
sat-sub {E = ε} ε = ε
sat-sub {τ = τ} {E = A ≐ B} (sg eq) = sg (≡.subst₂ _≡_ (subTy-subTy {τ = τ} {A = A}) (subTy-subTy {τ = τ} {A = B}) eq)
sat-sub {E = E ∙ E₁} (s ∙ s₁) = sat-sub s ∙ sat-sub s₁

-- We can specialize each solution further.

sat-spec : σ ⊧ E → subSub τ σ ⊧ E
sat-spec {E = ε} ε = ε
sat-spec {E = E ∙ E₁} (s ∙ s₁) = sat-spec s ∙ sat-spec s₁
sat-spec {σ = σ} {E = A ≐ B} {τ = τ} (sg eq) = sg (begin
  subTy (subSub τ σ) A ≡⟨ ≡.sym (subTy-subTy {A = A}) ⟩
  subTy τ (subTy σ A)  ≡⟨ ≡.cong (subTy τ) eq ⟩
  subTy τ (subTy σ B)  ≡⟨ subTy-subTy {A = B} ⟩
  subTy (subSub τ σ) B ∎)

------------------------------------------------------------------------
-- Soundness of inference.

-- Variable case.

idSub-lookup : ∀{Γ : Cxt Ξ n} → Tm (subCxt idSub (wkCxt R.id Γ)) (var x) (subTy idSub (lookup Γ x))
idSub-lookup {x = x} {Γ = Γ} rewrite wkCxt-id {Γ = Γ} | subCxt-id {Γ = Γ} | subTy-id {A = lookup Γ x} = var

var-sub-lookup : Tm (subCxt σ Γ) (var x) (subTy σ (lookup Γ x))
var-sub-lookup {Γ = Γ} = ≡.subst (Tm (subCxt _ _) (var _)) (subTy-lookup {Γ = Γ}) var

-- Lambda case.

lam : Tm (subCxt σ (tyvar (Vec.lookup η zero) ∷ wkCxt η (wkCxt1 Γ)))        e (subTy σ A)
    → Tm (subTyVar σ (Vec.lookup η zero) ∷ subCxt σ (wkCxt (R.wk R.⊙ η) Γ)) e (subTy σ A)
lam {σ = σ} {η = η} {e = e} {A = A} =
  ≡.subst (λ Γ → Tm (subCxt σ (tyvar (wkTyVar η zero) ∷ Γ)) e (subTy σ A))
    (wkCxt-wkCxt {η = η} {η′ = R.wk})

-- Application case.

appl : Tm (subCxt (renSub R.wk S.⊙ σ) (wkCxt η₂ (wkCxt η₁ Γ))) e (subTy (renSub R.wk S.⊙ σ) A)
     → Tm (subCxt σ (wkCxt (η₁ R.⊙ (η₂ R.⊙ R.wk)) Γ))          e (subTy σ (wkTy1 A))
appl {σ = σ} {η₂ = η₂} {η₁ = η₁} {Γ = Γ} {e = e} {A = A} = ≡.subst₂ (λ Γ A → Tm Γ e A)
  (begin
     subCxt (renSub R.wk S.⊙ σ) (wkCxt η₂ (wkCxt η₁ Γ)) ≡⟨ {!!} ⟩
     subCxt σ (wkCxt (η₁ R.⊙ (η₂ R.⊙ R.wk)) Γ)          ∎)
  (begin
     subTy (renSub R.wk S.⊙ σ) A  ≡⟨ {!!} ⟩
     subTy σ (wkTy1 A)            ∎)

appr : subTy σ (wkTy (η₂ R.⊙ R.wk) C) ≡ subTy σ (wkTy1 A ⇒ tyvar zero)
     → Tm (subCxt (renSub (η₂ R.⊙ R.wk) S.⊙ σ) (wkCxt η₁ Γ)) f (subTy (renSub (η₂ R.⊙ R.wk) S.⊙ σ) C)
     → Tm (subCxt σ (wkCxt (η₁ R.⊙ (η₂ R.⊙ R.wk)) Γ))        f (subTy σ (wkTy1 A) ⇒ subTyVar σ zero)
appr = {!!}

-- Theorem: Soundness of inference.

sound-inf : Inf Γ e η A E
          → σ ⊧ E
          → Tm (subCxt σ (wkCxt η Γ)) e (subTy σ A)

sound-inf {Γ = Γ} var _ rewrite wkCxt-id {Γ = Γ} = var-sub-lookup

sound-inf {A = X ⇒ A} (abs d) s = abs (lam {A = A} (sound-inf d s))

sound-inf (app {C = C} {A = A} d d₁) (s ∙ (s₁ ∙ sg eq)) =
  app (appr {C = C} {A = A} eq (sound-inf d (sat-wk s)))
      (appl {A = A} (sound-inf d₁ (sat-wk s₁)))

------------------------------------------------------------------------
-- Strengthening (occurrence check).

-- Dropping a type variable.

delete : (X : TyVar Ξ) → TyCxt
delete {Ξ = suc Ξ} zero = Ξ
delete (suc X) = suc (delete X)

-- Strengthening a type variable StrTyVar X Y Z: A "subtraction" Z = Y - X.

data StrTyVar : (X : TyVar Ξ) (Y : TyVar Ξ) (Z : TyVar (delete X)) → Set where

  zero-suc : StrTyVar zero (suc Y) Y
  suc-zero : StrTyVar (suc X) zero zero
  suc-suc  : StrTyVar X Y Z → StrTyVar (suc X) (suc Y) (suc Z)

-- Strengthening a type.

data StrTy : (X : TyVar Ξ) (A : Ty Ξ) (A' : Ty (delete X)) → Set where

  tyvar : StrTyVar X Y Z
        → StrTy X (tyvar Y) (tyvar Z)

  _⇒_   : StrTy X A A′
        → StrTy X B B′
        → StrTy X (A ⇒ B) (A′ ⇒ B′)

-- Singleton substitution from successful occurrence check.

sgSub : (X : TyVar Ξ) (η : delete X ⊆ Ξ') (A : Ty Ξ') → Subst Ξ Ξ'
sgSub (zero)  η       A = A ∷ renSub η
sgSub (suc X) (Y ∷ η) A = tyvar Y ∷ sgSub X η A

-- Lemmata for sgSub.

subTyVar-sgSub : subTyVar (sgSub X η A) X ≡ A
subTyVar-sgSub {X = zero} = refl
subTyVar-sgSub {X = suc X} {η = _ ∷ η} = subTyVar-sgSub {X = X}

nocc-subTyVar : StrTyVar X Y Z → subTyVar (sgSub X η A) Y ≡ tyvar (wkTyVar η Z)
nocc-subTyVar {η = η}     zero-suc    = subTyVar-renSub η _
nocc-subTyVar {η = _ ∷ η} suc-zero    = refl
nocc-subTyVar {η = _ ∷ η} (suc-suc s) = nocc-subTyVar s

nocc-subTy :  StrTy X A A′ → subTy (sgSub X η B) A ≡ wkTy η A′
nocc-subTy (tyvar s) = nocc-subTyVar s
nocc-subTy (s ⇒ s₁)  = ≡.cong₂ _⇒_ (nocc-subTy s) (nocc-subTy s₁)

-- If X ∉ A then X[X ↦ A] = A[X ↦ A].

nocc-idem : StrTy X A A′ → subTyVar (sgSub X R.id A′) X ≡ subTy (sgSub X R.id A′) A
nocc-idem {X = X} {A = A} {A′ = A′} s = begin

  subTyVar (sgSub X R.id A′) X    ≡⟨ subTyVar-sgSub {X = X} {η = R.id} ⟩
  A′                              ≡⟨ ≡.sym wkTy-id ⟩
  wkTy R.id A′                    ≡⟨ ≡.sym (nocc-subTy s) ⟩
  subTy (sgSub X R.id A′) A       ∎

------------------------------------------------------------------------
-- Solving constraints.

data _↘_ : Eqs Ξ → Subst Ξ Ξ₁ → Set where

  ε    : ε ↘ idSub {Ξ = Ξ}

  ⇒E   : A ≐ A′ ∙ B ≐ B′ ↘ σ
       → A ⇒ B ≐ A′ ⇒ B′ ↘ σ

  X≐   : StrTy X A A′
       → tyvar X ≐ A ↘ sgSub X R.id A′

  ≐X   : StrTy X A A′
       → A ≐ tyvar X ↘ sgSub X R.id A′

  _∙_  : E ↘ σ
       → subEqs σ F ↘ τ
       → E ∙ F ↘ subSub τ σ

-- Soundness of solving.

sound-solve : E ↘ σ → σ ⊧ E
sound-solve ε        = ε
sound-solve (⇒E s)   = sat-arr (sound-solve s)
sound-solve (X≐ str) = sg (nocc-idem str)
sound-solve (≐X str) = sg (≡.sym (nocc-idem str))
sound-solve (s ∙ s₁) = sat-spec (sound-solve s) ∙ sat-sub (sound-solve s₁)

------------------------------------------------------------------------
-- Soundness of inference followed by constraint solving.

sound-type-inference : ∀{Γ : Cxt Ξ n} {η : Ξ ⊆ Ξ₁} {σ : Subst Ξ₁ Ξ₂}
  → Inf Γ e η A E
  → E ↘ σ
  → Tm (subCxt σ (wkCxt η Γ)) e (subTy σ A)
sound-type-inference d s = sound-inf d (sound-solve s)

-- Q.E.D.

-- It remains to show completeness of solving and inference.

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
