open import Data.Nat renaming (pred to pre; _≟_ to _≟ₙ_)
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ₒ_)
open import Data.Sum
open import Data.String
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable hiding (True; False)

data Type : Set where
  Nat : Type
  Bool : Type
  _⇒_ : Type -> Type -> Type

Name : Set
Name = String

data Exp : Set where
  Zero : Exp
  Succ_ : Exp -> Exp
  Pred_ : Exp -> Exp
  True : Exp
  False : Exp
  IsZero_ : Exp -> Exp
  Var_ : Name -> Exp
  If_Then_Else_ : Exp -> Exp -> Exp -> Exp
  Fn_∶_·_ : Name -> Type -> Exp -> Exp
  _·_ : Exp -> Exp -> Exp
  Fix_ : Exp -> Exp

data Env : Set where
  ∅ : Env
  _,_∶_ : Env -> Name -> Type -> Env

data _∶_∈_ : Name -> Type -> Env -> Set where
  here : ∀ {x τ Γ} -> x ∶ τ ∈ (Γ , x ∶ τ)
  there : ∀ {x y τ τ′ Γ} -> x ≢ y -> x ∶ τ ∈ Γ -> x ∶ τ ∈ (Γ , y ∶ τ′)

infix 10 _⊢_∶_
data _⊢_∶_ : Env -> Exp -> Type -> Set where
  zero : ∀ {Γ : Env} -> Γ ⊢ Zero ∶ Nat
  succ : ∀ {Γ : Env} {m : Exp} -> Γ ⊢ m ∶ Nat -> Γ ⊢ Succ m ∶ Nat
  pred : ∀ {Γ : Env} {m : Exp} -> Γ ⊢ m ∶ Nat -> Γ ⊢ Pred m ∶ Nat
  isZero : ∀ {Γ : Env} {m : Exp} -> Γ ⊢ m ∶ Nat -> Γ ⊢ IsZero m ∶ Bool
  true : ∀ {Γ : Env} -> Γ ⊢ True ∶ Bool
  false : ∀ {Γ : Env} -> Γ ⊢ False ∶ Bool
  var : ∀ {Γ n τ} -> n ∶ τ ∈ Γ -> Γ ⊢ Var n ∶ τ
  ifThenElse : ∀ {Γ m₁ m₂ m₃ τ} -> Γ ⊢ m₁ ∶ Bool -> Γ ⊢ m₂ ∶ τ -> Γ ⊢ m₃ ∶ τ -> Γ ⊢ If m₁ Then m₂ Else m₃ ∶ τ
  fn : ∀ {Γ x τ τ′ m} -> (Γ , x ∶ τ) ⊢ m ∶ τ′ -> Γ ⊢ (Fn x ∶ τ · m) ∶ (τ ⇒ τ′)
  app : ∀ {Γ m₁ m₂ τ τ′} -> Γ ⊢ m₁ ∶ (τ ⇒ τ′) -> Γ ⊢ m₂ ∶ τ -> Γ ⊢ m₁ · m₂ ∶ τ′
  fix : ∀ {Γ m τ} -> Γ ⊢ m ∶ (τ ⇒ τ) -> Γ ⊢ Fix m ∶ τ

data Bot : Set where
  ⊥ : Bot

⟦_⟧Type : Type -> Set
⟦ Nat ⟧Type = ℕ ⊎ Bot
⟦ Bool ⟧Type = 𝔹 ⊎ Bot
⟦ A ⇒ B ⟧Type = (⟦ A ⟧Type → ⟦ B ⟧Type) ⊎ Bot

⟦_⟧Env : Env -> Set
⟦ ∅ ⟧Env = Bot
⟦ Γ , x ∶ τ ⟧Env = ⟦ Γ ⟧Env × ⟦ τ ⟧Type

_[_↦_] : ∀ {Γ x τ} -> ⟦ Γ ⟧Env -> (x : Name) -> ⟦ τ ⟧Type -> ⟦ Γ , x ∶ τ ⟧Env
ρ [ x ↦ τ ] = (ρ , τ)


⟦_⟧Var : ∀ {x τ Γ} -> (x ∶ τ ∈ Γ) -> ⟦ Γ ⟧Env -> ⟦ τ ⟧Type
⟦ here ⟧Var (Γ , τ) = τ
⟦ there _ x ⟧Var (Γ , τ) = ⟦ x ⟧Var Γ

⟦_⟧ : ∀ {Γ m τ} -> (Γ ⊢ m ∶ τ) -> ⟦ Γ ⟧Env -> ⟦ τ ⟧Type
⟦ zero ⟧ ρ = inj₁ 0
⟦ true ⟧ ρ = inj₁ true
⟦ false ⟧ ρ = inj₁ false
⟦ var x ⟧ ρ = ⟦ x ⟧Var ρ
⟦ succ m ⟧ ρ = [ (λ { x → inj₁ (suc x) }) , (λ { _ → inj₂ ⊥ }) ]′ (⟦ m ⟧ ρ)
⟦ pred m ⟧ ρ = [ (λ { x → if ⌊ x ≟ₙ 0 ⌋ then inj₂ ⊥ else inj₁ (pre x) }) , (λ { _ → inj₂ ⊥ }) ]′ (⟦ m ⟧ ρ)
⟦ isZero m ⟧ ρ = [ (λ { x → if ⌊ x ≟ₙ 0 ⌋ then inj₁ true else inj₁ false }) , (λ { _ → inj₂ ⊥ }) ]′ (⟦ m ⟧ ρ)
⟦ ifThenElse m₁ m₂ m₃ ⟧ ρ = [ (λ { x → if ⌊ x ≟ₒ true ⌋ then ⟦ m₂ ⟧ ρ else ⟦ m₃ ⟧ ρ }) , (λ { _ → {!!} }) ]′ (⟦ m₁ ⟧ ρ)
--⟦ app m₁ m₂ ⟧ ρ = [ (λ { x → ⟦ m₂ ⟧ ρ }) , (λ { x → ? }) ]′ (⟦ m₁ ⟧ ρ)
⟦_⟧ {m = Fn x ∶ τ · n} (fn x₁) ρ = inj₁ (λ { d → ⟦ x₁ ⟧ (ρ [ x ↦ d ]) })
--⟦⟧
