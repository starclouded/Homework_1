open import NonDependentTypes

module Terms where 

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

-- Enumerated type
term-Wd₁ : WeekDay
term-Wd₁ = monday

term-Wd₂ : WeekDay
term-Wd₂ = tuesday

term-Wd₃ : WeekDay
term-Wd₃ = wednesday

term-Wd₄ : WeekDay
term-Wd₄ = thursday

term-Wd₅ : WeekDay
term-Wd₅ = friday

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
