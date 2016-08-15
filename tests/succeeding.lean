
import ..firstorder

open nat bool

-- some tests from Coq (https://github.com/coq/coq/blob/trunk/test-suite/success/Tauto.v),
-- from http://www.lix.polytechnique.fr/coq/pylons/contribs/files/ATBR/v8.4/ATBR.BoolView.html,
-- and from old blast tests
section tauto_tests

variables (a b c d e f : Prop)
variable even : ℕ → Prop
variable P : ℕ → Prop


--Problem tests

--example : (∀ x, P x) ∧ b → (∀ y, P y) ∧ P 0 ∨ b ∧ P 0 := by tauto
--example : (∀ A, A ∨ ¬A) → ∀ x y : ℕ, x = y ∨ x ≠ y := by tauto
--example : ∀ b1 b2, b1 = b2 ↔ (b1 = tt ↔ b2 = tt) := by tauto
--example : ∀ (P Q : nat → Prop), (∀n, Q n → P n) → (∀n, Q n) → P 2 := by tauto
--example (a b c : Prop) : ¬ true ∨ false ∨ b ↔ b := by tauto  -- should be taken care of by general ind-arrow tactic



--Successful tests


example : true := by tauto
example : false → a := by tauto
example : a → a := by tauto
example : (a → b) → a → b := by tauto
example : ¬ a → ¬ a := by tauto
example : a → (false ∨ a) := by tauto
example : (a → b → c) → (a → b) → a → c := by tauto
example : a → ¬ a → (a → b) → (a ∨ b) → (a ∧ b) → a → false := by tauto
example : ((a ∧ b) ∧ c) → b := by tauto
example : ((a → b) → c) → b → c := by tauto
example : (a ∨ b) → (b ∨ a) := by tauto
example : (a → b ∧ c) → (a → b) ∨ (a → c) := by tauto
example : ∀ (x0 : a ∨ b) (x1 : b ∧ c), a → b := by tauto
example : a → b → (c ∨ b) := by tauto
example : (a ∧ b → c) → b → a → c := by tauto
example : (a ∨ b → c) → a → c := by tauto
example : (a ∨ b → c) → b → c := by tauto
example : (a ∧ b) → (b ∧ a) := by tauto
example : (a ↔ b) → a → b := by tauto
example : a → ¬¬a := by tauto
example : ¬¬(a ∨ ¬a) := by tauto
example : ¬¬(a ∨ b → a ∨ b) := by tauto
example : ¬¬((∀ n, even n) ∨ ¬(∀ m, even m)) := by tauto
example : (¬¬b → b) → (a → b) → ¬¬a → b := by tauto
example : (¬¬b → b) → (¬b → ¬ a) → ¬¬a → b := by tauto
example : ((a → b → false) → false) → (b → false) → false := by tauto
example : ((((c → false) → a) → ((b → false) → a) → false) → false) → (((c → b → false) → false) → false) → ¬a → a := by tauto
example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by tauto
example : ∀ (F F' : Prop), F ∧ F' → F := by tauto
example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 := by tauto
example : ∀ (f : nat → Prop), f 2 → ∃ x, f x := by tauto
example : true ∧ true ∧ true ∧ true ∧ true ∧ true ∧ true := by tauto
example : ∀ (P : nat → Prop), P 0 → (P 0 → P 1) → (P 1 → P 2) → (P 2) := by tauto
example : ¬¬¬¬¬a → ¬¬¬¬¬¬¬¬a → false := by tauto
example : ∀ n, ¬¬(even n ∨ ¬even n) := by tauto
example : ∀ (p q r s : Prop) (a b : nat), r ∨ s → p ∨ q → a = b → q ∨ p := by tauto
example : (∀ x, P x) → (∀ y, P y) := by tauto
--example : ((a ↔ b) → (b ↔ c)) → ((b ↔ c) → (c ↔ a)) → ((c ↔ a) → (a ↔ b)) → (a ↔ b) := by tauto
--example : ((¬a ∨ b) ∧ (¬b ∨ b) ∧ (¬a ∨ ¬b) ∧ (¬b ∨ ¬b) → false) → ¬((a → b) → b) → false := by tauto
--example : ¬((a → b) → b) → ((¬b ∨ ¬b) ∧ (¬b ∨ ¬a) ∧ (b ∨ ¬b) ∧ (b ∨ ¬a) → false) → false := by tauto
--example : (¬ a ↔ b) → (¬ (c ∨ e) ↔ d ∧ f) → (¬ (c ∨ a ∨ e) ↔ d ∧ b ∧ f) := by tauto
example : (¬a ↔ b) → (¬b ↔ a) → (¬¬a ↔ a) := by tauto
example {A : Type} (p q : A → Prop) (a b : A) : q a → p b → ∃ x, (p x ∧ x = b) ∨ q x := by tauto
example {A : Type} (p q : A → Prop) (a b : A) : p b → ∃ x, q x ∨ (p x ∧ x = b) := by tauto
example : ¬ a → b → a → c := by tauto
example : a → b → b → ¬ a → c := by tauto
example (a b : nat) : a = b → b = a := by tauto
example (a b c : nat) : a = b → a = c → b = c := by tauto
example (p : nat → Prop) (a b c : nat) : a = b → a = c → p b → p c := by tauto
example (p : Prop) (a b : nat) : a = b → p → p := by tauto
example (a : nat) : zero = succ a → a = a → false := by tauto
example (a b c : nat) : succ (succ a) = succ (succ b) → c = c := by tauto
example (p : Prop) (a b c : nat) : [a, b, c] = [] → p := by tauto
example (p : Prop) (a b : nat) : a = b → b ≠ a → p := by tauto
example : (a ↔ b) → ((b ↔ a) ↔ (a ↔ b)) := by tauto
example (a b c : nat) : b = c → (a = b ↔ c = a) := by tauto
example : ¬¬¬¬¬¬¬¬a → ¬¬¬¬¬a → false := by tauto
example (a b c : Prop) : a ∧ b ∧ c ↔ c ∧ b ∧ a := by tauto
example (a b c : Prop) : a ∧ false ∧ c ↔ false := by tauto
example (a b c : Prop) : a ∨ false ∨ b ↔ b ∨ a := by tauto
example : a ∧ not a ↔ false := by tauto
example : a ∧ b ∧ true → b ∧ a := by tauto
example (A : Type₁) (a₁ a₂ : A) : a₁ = a₂ → (λ (B : Type₁) (f : A → B), f a₁) = (λ (B : Type₁) (f : A → B), f a₂) := by tauto
example (a : nat) : ¬ a = a → false := by tauto
example (A : Type) (p : Prop) (a b c : A) : a = b → ¬ b = a → p := by tauto
example (A : Type) (p : Prop) (a b c : A) : a = b → b ≠ a → p := by tauto
example (p q r s : Prop) : r ∧ s → p ∧ q → q ∧ p := by tauto
example (p q : Prop) : p ∧ p ∧ q ∧ q → q ∧ p := by tauto
example (p : nat → Prop) (q : nat → nat → Prop) : (∃ x y, p x ∧ q x y) → q 0 0 ∧ q 1 1 → (∃ x, p x) := by tauto
example (p q r s : Prop) (a b : nat) : r ∨ s → p ∨ q → a = b → q ∨ p := by tauto
example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by tauto
example (a b : Prop) : a → b → a := by tauto
example (p q : nat → Prop) (a b : nat) : p a → q b → ∃ x, p x := by tauto

example : ∀ b1 b2, b1 && b2 = ff ↔ (b1 = ff ∨ b2 = ff) := by tauto
example : ∀ b1 b2, b1 && b2 = tt ↔ (b1 = tt ∧ b2 = tt) := by tauto
example : ∀ b1 b2, b1 || b2 = ff ↔ (b1 = ff ∧ b2 = ff) := by tauto
example : ∀ b1 b2, b1 || b2 = tt ↔ (b1 = tt ∨ b2 = tt) := by tauto
example : ∀ b, bnot b = tt ↔ b = ff := by tauto
example : ∀ b, bnot b = ff ↔ b = tt := by tauto
example : ∀ b c, b = c ↔ ¬ (b = bnot c) := by tauto

inductive and3 (a b c : Prop) : Prop :=
| mk : a → b → c → and3 a b c

example (h : and3 a b c) : and3 b c a := by tauto

inductive or3 (a b c : Prop) : Prop :=
| in1 : a → or3 a b c
| in2 : b → or3 a b c
| in3 : c → or3 a b c
example (h : a) : or3 a b c := by tauto
example (h : b) : or3 a b c := by tauto
example (h : c) : or3 a b c := by tauto



variables (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop)
-- H first, all pos

example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) : B₄ := by tauto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄) : B₃ := by tauto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄) : B₂ := by tauto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : B₁ := by tauto

example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₃ := by tauto
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₂ := by tauto
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₁ := by tauto

-- H last, all pos
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₄ := by tauto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₃ := by tauto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₂ := by tauto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₁ := by tauto

example (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₃ := by tauto
example (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₂ := by tauto
example (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₁ := by tauto

-- H first, all neg
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) : ¬B₄ := by tauto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) : ¬B₃ := by tauto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) : ¬B₂ := by tauto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬B₁ := by tauto

example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₃ := by tauto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₂ := by tauto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₁ := by tauto

-- H last, all neg
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₄ := by tauto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₃ := by tauto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₂ := by tauto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₁ := by tauto

example (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₃ := by tauto
example (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₂ := by tauto
example (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₁ := by tauto

section club
variables Scottish RedSocks WearKilt Married GoOutSunday : Prop
lemma NoMember : (¬Scottish → RedSocks) → (WearKilt ∨ ¬RedSocks) → (Married → ¬GoOutSunday) →
                 (GoOutSunday ↔ Scottish) → (WearKilt → Scottish ∧ Married) → (Scottish → WearKilt) → false := by tauto
end club

end tauto_tests
