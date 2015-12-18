--Importing Nat
open import Data.Nat
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; trans; cong)

module NatOpr where

--Proving left and right identity over + operation
leftId : (a : ℕ) → 0 + a ≡ a
leftId a = refl

rightId : (a : ℕ) → a + 0 ≡ a
rightId zero = refl
rightId (suc a) = cong suc (rightId a)

--proving left and right identity over * operation
leftId* : (a : ℕ) → (0 * a) ≡ 0
leftId* a = refl

rightId* : (a : ℕ) → (a * 0) ≡ 0
rightId* zero = refl
rightId* (suc a) = rightId* a

--proving associativity over + opr 
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

--proving associativity over * opr
*-assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
*-assoc zero b c = refl
*-assoc (suc a) b c = trans (dist-*+ b (a * b) c) (cong (λ x → (b * c) + x) (*-assoc a b c))

--Proving below thm, this will be used in commutative operation. 
helper : ∀ a b → suc a + b ≡ a + suc b
helper zero b = refl
helper (suc a) b = cong suc (helper a b)

--Proving commutativity over +
--see here is a special thing happen, if you observe it closely you get that we want to proof (b ≡ b + 0). so to proof 
--this we are doing it backwards by symmetric property that if (a ≡ b) then (b ≡ a).
-- so sym (b ≡ b + 0) will give proof of (b + 0 ≡ b).
comm-+ : ∀ a b → a + b ≡ b + a
comm-+ zero b = sym (rightId b)
comm-+ (suc a) b = trans (cong suc (comm-+ a b)) (helper b a)

--proving distributivity of * over +
dist-*+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
dist-*+ zero b c = refl
dist-*+ (suc a) b c = trans (cong (λ x → c + x) (dist-*+ a b c)) (sym (+-assoc c (a * c) (b * c))) 

--writing infix notation, now we dont need to write parenthesis.
infixr 5 _~_
_~_ = trans

--This is alraedy defined in library.
m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

--On proving on paper I required to proof this theorem which will shorter the proof of commutativity over * operation.
-- This was the trickiest, gave me insight that there are many ways to proof theorem.  
lemma-+swap1 : ∀ a b c → a + (b + c) ≡ b + (a + c)
lemma-+swap1 a b c = begin
`3  a + (b + c) ≡⟨ sym (+-assoc a b c) ⟩
  (a + b) + c ≡⟨ cong (λ x → x + c) (comm-+ a b) ⟩
  (b + a) + c ≡⟨ +-assoc b a c ⟩
  b + (a + c) ∎
    where
      open PropEq.≡-Reasoning

--I am still trying to proof this.
lemma*-swap : ∀ a b → a + a * b ≡ a * suc b
lemma*-swap zero b = refl
lemma*-swap (suc a) b = {!!}

--proving comm over *, will be proved only if above was proved.
--*comm : ∀ a b → (a * b) ≡ (b * a)
--*comm zero b = sym (rightId* b)
--*comm (suc a) b = {!!} 

--seems that most of natural properties are proved.
--I am thinking to proof properties over Integer but it will take time, and I am not sure about how will i proceed. 
--Sir, I need your suggestion should i proceed further or these are sufficient to claim our thesis.
--The above proofs took most of the time as they were not easy cake.

