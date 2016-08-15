
open tactic expr list environment nat bool

meta_definition intro' (n : name) : tactic unit := intro n >> skip

meta_definition cond_intros : tactic unit := do
t ← target,
when (is_pi t = ff) (fail "intros: not a pi type"),
intro' `h

--example (a b : Prop) : a → b := by do cond_intros
--example (a b : Prop) : b := by do cond_intros

meta_definition axioms' : tactic unit := do
solve [triv, assumption, contradiction]

private meta_definition unit_prop' (ctx : list expr) (h : expr) : tactic unit := do
t ← infer_type h,
match t with
| (pi _ _ a b) := 
  do { assert `ab b,
       apply h,
       assumption,
       clear h }
| _ := fail "unit propagation not possible because not a pi type"
end

meta_definition unit_prop (e : expr) : tactic unit := do
ctx ← local_context,
unit_prop' ctx e

private meta_definition get_constructors_for (e : expr) : tactic (list name) :=
do env ← get_env,
   I   ← return $ expr.const_name (expr.get_app_fn e),
   when (environment.is_inductive env I = ff) (fail "constructor tactic failed, target is not an inductive datatype"),
   return $ environment.constructors_of env I

meta_definition induction (e : expr) : tactic unit := do
env ← get_env,
t ← infer_type e,
I   ← return $ expr.const_name (expr.get_app_fn t),
when (is_inductive env I = ff) (fail "constructor tactic failed; target is not an inductive datatype"),
induction_core semireducible e (I <.> "rec") []

-- non-branching induction
meta_definition nb_induction (e : expr) : tactic unit := do
env ← get_env,
t ← infer_type e,
I   ← return $ expr.const_name (expr.get_app_fn t),
when (is_inductive env I = ff) (fail "constructor tactic failed; target is not an inductive datatype"),
when (length (constructors_of env I) > 1) (fail "we are only allowing non-branching induction"),
induction_core semireducible e (I <.> "rec") []

--example (T : Type) (l : list T) : length l ≥ 0 := by do get_local `l >>= induction
--example (a b : Prop) (hab : a ∨ b) : b ∨ a := by do get_local `hab >>= induction
--example (a b : Prop) (hab : a ∧ b) : b ∧ a := by do get_local `hab >>= induction, constructor; assumption

definition ar (a b : expr) := pi `h_ binder_info.default a b

meta_definition disj_ar (h : expr) : tactic unit := do
t ← infer_type h,
or ← mk_const `or,
when ((app_fn (app_fn (binding_domain t))) ≠ or) (fail "not or"),
let a := (app_arg (app_fn (binding_domain t))) in
let b := (app_arg (binding_domain t)) in
let c := (binding_body t) in
do { assert `hac (ar a c), intro `ha, apply h, left;  assumption,
     assert `hbc (ar b c), intro `hb, apply h, right; assumption },
clear h
--example (a b c g : Prop) (h : a ∨ b → c) : g := by do get_local `h >>= disj_ar
/-
inductive comb (a b c d e f : Prop) : Prop :=
| c1 : a → b → c → comb a b c d e f
| c2 : d → e → f → comb a b c d e f

example (a b c d g : Type) (h1 : a → b → c) (h2 : c → d) : g := by do
h1 ← get_local `h1,
h2 ← get_local `h2,
a ← get_local `a,
b ← get_local `b,
c ← get_local `c,
d ← get_local `d,
assert `h (ar a (ar b d)), intros >> skip, apply h2, apply h1; assumption
/-
example (a b c d e f g r : Prop) (h : comb a b c d e f → r) : g := by do 
h ← get_local `h,
a ← get_local `a,
b ← get_local `b,
c ← get_local `c,
d ← get_local `d,
e ← get_local `e,
f ← get_local `f,
r ← get_local `r,
c1 ← mk_const `comb.c1,
c2 ← mk_const `comb.c2,
t ← infer_type c1,
trace (app_fn t),
assert `h1 (ar a (ar b (ar c r))), intros >> skip, apply h, apply c1; assumption,
assert `h2 (ar d (ar e (ar f r))), intros >> skip, apply h, apply c2; assumption,
clear h
-/
meta_definition helper : list expr → tactic unit
| [] := skip
| (c::cs) := skip--do assert `h (ar

meta_definition LIf (h : expr) : tactic unit := do
ty ← infer_type h,
match ty with
| (pi _ _ a b) := do 
  env ← get_env,
  trace a,
  I   ← return $ const_name (get_app_fn a),
  trace I,
  when (environment.is_inductive env I = ff) (fail "constructor tactic failed, target is not an inductive datatype"),
  cs ← get_constructors_for (get_app_fn a),
  trace cs
| _ := fail "LIf failed"
end

--example (a b c g : Prop) (h : a ∨ b → c) : g := by do get_local `h >>= LIf 
-/
meta_definition conj_ar (h : expr) : tactic unit := do
t ← infer_type h,
and ← mk_const `and,
when ((app_fn (app_fn (binding_domain t))) ≠ and) (fail "not and"),
assert `habc (ar (app_arg (app_fn (binding_domain t))) (ar (app_arg (binding_domain t)) (binding_body t))), 
intro' `ha, intro' `hb, apply h, split; assumption, 
clear h

--example (a b c g : Prop) (h : a ∧ b → c) : g := by do get_local `h >>= conj_ar
--example (a b c : Prop) (P : ℕ → Prop) (hP : ∀ n, P n) : P 0 := by do get_local `hP >>= conj_ar

meta_definition unfold_one_at (u : list name) (h : expr) : tactic unit := do 
num_reverted : ℕ ← revert h,
(expr.pi n bi d b : expr) ← target | failed,
new_H : expr ← unfold_expr_core ff (occurrences.pos [1]) u d,
change $ expr.pi n bi new_H b,
intron num_reverted,
when (new_H = d) (fail "nothing unfolded")

--example (a : Prop) (h : ¬a) : ¬a := by do get_local `h >>= unfold_one_at [`not]
--example (a : Prop) (h :  a) : ¬a := by do get_local `h >>= unfold_one_at [`not]

meta_definition unfold_one (u : list name) : tactic unit := do
goal ← target,
new_goal ← unfold_expr_core ff (occurrences.pos [1]) u goal,
when (goal = new_goal) (fail "nothing unfolded"),
change new_goal

--example (a : Prop) (h : ¬a) : ¬a := by do unfold_one [`not]
--example (a : Prop) (h :  a) :  a := by do unfold_one [`not]

meta_definition cleanup_true (e : expr) : tactic unit := do
tru ← mk_const `true,
t ← infer_type e,
when (t ≠ tru) (fail "no true to clean up"),
clear e

meta_definition cleanup_false (e : expr) : tactic unit := do
fal ← mk_const `false,
t ← infer_type e,
match t with
| (pi _ _ a _) := when (a ≠ fal) (fail " pi, but no false to clean up")
| _ := fail "no false to clean up"
end,
clear e

meta_definition cleanup (e : expr) : tactic unit := do
cleanup_true e <|> cleanup_false e

--example (a : Prop) (h : true) : a := by do get_local `h >>= cleanup
--example (a : Prop) (h : false → a) : a := by do get_local `h >>= cleanup
--example (a b : Prop) (h : b → a) : a := by do get_local `h >>= cleanup

private meta_definition simplif_aux : list expr → tactic unit
| [] := fail "simplif failed"
| (h::hs) := do t ← infer_type h, trace t,
             (trace " nb_induction"; nb_induction h; trace " nb_induction succeeded") <|>
             (trace " unfold_one_at iff"; unfold_one_at [`iff] h; trace " unfold_one_at iff succeeded") <|> 
             (trace " unfold_one_at not"; unfold_one_at [`not] h; trace " unfold_one_at not succeeded") <|> 
             (trace " unit prop"; unit_prop h; trace " unit prop succeeded") <|> 
             (trace " conj arrow"; conj_ar h; trace " conj arrow succeeded") <|>
             (trace " disj arrow"; disj_ar h; trace " disj arrow succeeded") <|> 
             (trace " cleanup"; cleanup h; trace " cleanup succeeded") <|>
             simplif_aux hs

meta_definition simplif : tactic unit := do local_context >>= simplif_aux

meta_definition Lff (H : expr) : tactic unit :=
do t ← infer_type H,
   G ← target,
   match t with
   | pi _ _ (pi _ _ A B) C := 
   do assert `h₁ (ar A (ar (ar B C) B)), rotate 1,
      assert `h₂ (ar C G),
      h₁ ← get_local `h₁, clear h₁, rotate 1,
      h₂ ← get_local `h₂, apply h₂,
      apply H, intro `ha,
      apply h₁, assumption, 
      intro `hb, apply H,
      intro `ha1, assumption, clear H,
      intro `ha, intro `hbc, rotate 1, clear H,
      intro `hc, rotate 1
   | _ := fail "not right form to Lff"
   end

meta_definition tauto' : ℕ → tactic unit
| 0 := fail "tauto failed"
| (n+1) := do trace "", trace "TAUTO TOP LEVEL", trace (n+1), trace_state, trace "",
        (trace "trying axioms"; axioms') <|>
        (trace "trying cond_intros"; cond_intros; trace "cond_intros succeeded"; tauto' (n+1)) <|>
        (trace "trying simplif"; simplif; trace "simplif succeeded"; tauto' (n+1)) <|>
        (trace "trying single-constructor"; solve [split; trace "single-constructor succeeded"; tauto' (n+1)]) <|> 
        (trace "trying unfolding iff in goal"; unfold_one [`iff]; tauto' (n+1)) <|> 
        (trace "trying unfolding not in goal"; unfold_one [`not]; tauto' (n+1)) <|> 
        (trace "trying Lff"; 
          (do ctx ← local_context, solve (map (λ h, do Lff h; trace "Lff applied"; tauto' n) ctx))) <|>
        (trace "trying branching induction"; 
          (do ctx ← local_context, solve (map (λ h, do induction h; trace "branching induction applied"; tauto' n) ctx))) <|>
        (trace "trying multi_constructor"; 
          (do t ← target, cs ← get_constructors_for t, solve (map (λ c, mk_const c >>= apply; (do trace "branch applied:", trace c); tauto' n) cs))) <|>
        (trace "END OF BRANCH"; trace ""; fail "tauto failed")

definition tauto_max_depth : ℕ := 4
meta_definition tauto : tactic unit := do tauto' tauto_max_depth


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

/-
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
example : ((a ↔ b) → (b ↔ c)) → ((b ↔ c) → (c ↔ a)) → ((c ↔ a) → (a ↔ b)) → (a ↔ b) := by tauto
example : ((¬a ∨ b) ∧ (¬b ∨ b) ∧ (¬a ∨ ¬b) ∧ (¬b ∨ ¬b) → false) → ¬((a → b) → b) → false := by tauto
example : ¬((a → b) → b) → ((¬b ∨ ¬b) ∧ (¬b ∨ ¬a) ∧ (b ∨ ¬b) ∧ (b ∨ ¬a) → false) → false := by tauto
example : (¬a ↔ b) → (¬b ↔ a) → (¬¬a ↔ a) := by tauto
example : (¬ a ↔ b) → (¬ (c ∨ e) ↔ d ∧ f) → (¬ (c ∨ a ∨ e) ↔ d ∧ b ∧ f) := by tauto
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
-/
end tauto_tests
