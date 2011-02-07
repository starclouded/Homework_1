module Terms where

open import NonDependentTypes

-- Unit type
term-⊤ : ⊤
term-⊤ = tt

-- Polymorphic type: _×_
term-× : ⊤ × ⊤
term-× = term-⊤ , term-⊤

-- Record Type: _R_
term-R : R ⊤ (⊤ × ⊤) ℕ
term-R = record {
  f₁ = term-⊤
  ; f₂ = term-×
  ; f₃ = (succ zero)
  }

-- Sum Type: _+_
term-+₁ : ⊤ + ℕ
term-+₁ = inj₁ term-⊤

term-+₂ : ⊤ +  ℕ
term-+₂ = inj₂ (succ zero)

-- Enumeration type
term-Wd₁ : WeekDay
term-Wd₁ = monday

-- Function type
isEven : ℕ → Set
isEven zero = ⊤
isEven (succ zero) = ⊥
isEven (succ (succ n)) = isEven n

-- Maybe
term-May : Maybe (List ⊤)
term-May = just (term-⊤ ∷ nil)

-- Cannonical type
one : ℕ
one = succ zero

-- List type
term-L : List ℕ
term-L = (succ zero) ∷ (succ (succ zero) ∷ nil)

-- Tree type
term-T : Tree (List ℕ)
term-T = node (leaf term-L) empty
