import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false
set_option linter.flexible false

inductive Arity
| unary
| binary
deriving DecidableEq, Repr

structure Signature where
  Func : Type
  Const : Type
  arityFunc : Func → Arity

abbrev Var := String
instance : DecidableEq Var := String.decEq

inductive Term (τ : Signature) where
| var   : Var → Term τ
| const : τ.Const → Term τ
| app1  : (f : τ.Func) → (Term τ) → Term τ
| app2  : (f : τ.Func) → (Term τ) → (Term τ) → Term τ

inductive Formula (τ : Signature) where
| eq   : Term τ → Term τ → Formula τ
| neg  : Formula τ → Formula τ
| imp  : Formula τ → Formula τ → Formula τ
| forAll : Var → Formula τ → Formula τ

namespace Formula

infixr:70 " ⇒ " => imp
infixr:70 " =ₚ " => eq

prefix:100 "∼" => neg

prefix:max "∀ₚ" => forAll

-- ∃xϕ := ¬∀x¬ϕ
def exist {τ : Signature} (x : Var) (φ : Formula τ ) : Formula τ  := ∼ (∀ₚ x ( ∼ φ))
prefix:max "∃ₚ" => exist

def disj {τ : Signature} (φ ψ : Formula τ) : Formula τ := (∼ φ) ⇒ ψ
infixl:80 " ⋁ " => disj

def conj {τ : Signature} (φ ψ : Formula τ) : Formula τ := ∼ (φ ⇒ (∼ ψ))
infixl:80 " ⋀ " => conj

def iff {τ : Signature} (φ ψ : Formula τ) : Formula τ := (φ ⇒ ψ) ⋀ (ψ ⇒ φ)
infixl:70 "↔" => iff

end Formula


structure Structure (τ : Signature) where
  U : Type
  constInterp : τ.Const → U
  funcInterp1 : τ.Func → U → U
  funcInterp2 : τ.Func → U → U → U

def Env (U : Type) := Var → U

def evalTerm {τ : Signature} (M : Structure τ) (ρ : Env M.U) : Term τ → M.U
| Term.var x     => ρ x
| Term.const c   => M.constInterp c
| Term.app1 f t    => M.funcInterp1 f (evalTerm M ρ t)
| Term.app2 f t u  => M.funcInterp2 f (evalTerm M ρ t) (evalTerm M ρ u)

def updateEnv {A : Type} (e : Var → A) (x : Var) (a : A) : Var → A :=
  fun v => if v = x then a else e v


def evalFormula {τ : Signature} (M : Structure τ) (ρ : Env M.U) : Formula τ → Prop
| Formula.eq t1 t2   => evalTerm M ρ t1 = evalTerm M ρ t2
| Formula.neg φ      => ¬ evalFormula M ρ φ
| Formula.imp φ ψ    => evalFormula M ρ φ → evalFormula M ρ ψ
| Formula.forAll x φ => ∀ a : M.U, evalFormula M (updateEnv ρ x a)  φ


theorem evalFormula_neg {τ : Signature} (M : Structure τ) (ρ : Env M.U) (ψ: Formula τ): evalFormula  M ρ (∼ ψ) ↔ ¬ evalFormula  M ρ (ψ) := by
  rfl

theorem evalFormula_imp {τ : Signature} (M : Structure τ) (ρ : Env M.U) (ψ φ: Formula τ): evalFormula M ρ (φ ⇒ ψ ) ↔ evalFormula  M ρ φ → evalFormula  M ρ ψ  := by
  rfl

theorem evalFormula_forAll {τ : Signature } {x:Var} (M : Structure τ) (ρ : Env M.U) ( φ: Formula τ): evalFormula M ρ (∀ₚ x φ ) ↔ (∀ a : M.U, evalFormula M (updateEnv ρ x a)  φ) := by
  rfl
--  (∼ φ) ⇒ ψ
theorem evalFormula_disj {τ : Signature} (M : Structure τ) (ρ : Env M.U) (ψ φ: Formula τ): evalFormula M ρ (φ ⋁ ψ ) ↔ evalFormula  M ρ φ ∨ evalFormula  M ρ ψ  := by
  apply Iff.intro
  . intros h
    unfold Formula.disj at h
    rw [evalFormula_imp] at h
    rw [evalFormula_neg] at h
    by_cases ip : (evalFormula M ρ φ)
    . exact Or.inl ip
    . have j := h ip
      exact Or.inr j
  . intros h
    unfold Formula.disj
    unfold evalFormula
    rw [evalFormula_neg]
    intros ip
    cases h
    . contradiction
    . assumption

theorem evalFormula_conj {τ : Signature} (M : Structure τ) (ρ : Env M.U) (ψ φ: Formula τ): evalFormula M ρ (φ ⋀ ψ ) ↔ evalFormula  M ρ φ ∧ evalFormula  M ρ ψ  := by
  apply Iff.intro
  . intros h
    unfold Formula.conj at h
    rw [evalFormula_neg] at h
    rw [evalFormula_imp] at h
    rw [evalFormula_neg] at h
    rw [Classical.not_imp] at h
    rw [Classical.not_not] at h
    assumption
  . intros h
    unfold Formula.conj
    unfold evalFormula
    rw [evalFormula_imp]
    rw [evalFormula_neg]
    rw [Classical.not_imp]
    rw [Classical.not_not]
    assumption

theorem evalFormula_exists {τ : Signature } {x:Var} (M : Structure τ) (ρ : Env M.U) ( φ: Formula τ): evalFormula M ρ (∃ₚ x φ ) ↔ (∃ a : M.U, evalFormula M (updateEnv ρ x a) φ) := by
  apply Iff.intro
  . intros ip
    unfold Formula.exist at ip
    rw [evalFormula_neg] at ip
    rw [evalFormula_forAll] at ip
    rw [Classical.not_forall] at ip
    obtain ⟨y, ip_y⟩ := ip
    rw [evalFormula_neg] at ip_y
    rw [Classical.not_not] at ip_y
    exists y
  . intros ip
    unfold Formula.exist
    rw [evalFormula_neg]
    rw [evalFormula_forAll]
    rw [Classical.not_forall]
    obtain ⟨y, ip_y⟩ := ip
    exists y
    rw [evalFormula_neg]
    rw [Classical.not_not]
    assumption



-- def satisfiable {τ : Signature} (φ : Formula τ) : Prop :=
--   ∃ (M : Structure τ) (ρ : Env M.U), evalFormula M ρ φ


def satisfiable {τ : Signature} (φ : Formula τ) : Prop :=
  ∃ M : Structure τ, ∀ ρ : Env M.U, evalFormula M ρ φ

------------------------------------------

inductive PA_Const
| zero
deriving Repr, DecidableEq

inductive PA_Func
| succ  -- S(x)
| add   -- x + y
| mul   -- x * y
deriving Repr, DecidableEq


def PA_Sig : Signature :=
{ Const := PA_Const,
  Func  := PA_Func,
  arityFunc := fun f =>
    match f with
    | PA_Func.succ => Arity.unary
    | PA_Func.add  => Arity.binary
    | PA_Func.mul  => Arity.binary
}

def zero : Term PA_Sig := Term.const PA_Const.zero

def S (t : Term PA_Sig) : Term PA_Sig :=
  Term.app1 PA_Func.succ t

def addT (t1 t2 : Term PA_Sig) : Term PA_Sig :=
  Term.app2 PA_Func.add t1 t2


def mulT (t1 t2 : Term PA_Sig) : Term PA_Sig :=
  Term.app2 PA_Func.mul t1 t2


def eqT (t1 t2 : Term PA_Sig) : Formula PA_Sig :=
  Formula.eq t1 t2

notation "S(" t ")" => S t
notation t₁ " +ₚ " t₂ => addT t₁ t₂
notation t₁ " ×ₚ " t₂ => mulT t₁ t₂
notation t₁ " =ₚ " t₂ => eqT t₁ t₂


def PA_ax1 (x:Var): Formula PA_Sig :=
  Formula.forAll x (Formula.neg (Formula.eq (S(Term.var x)) zero))

def PA_ax2 (x y: Var): Formula PA_Sig :=
  Formula.forAll x (Formula.forAll y (Formula.imp (Formula.eq (S(Term.var x)) (S(Term.var y))) (Formula.eq (Term.var x) (Term.var y))))

def PA_ax3 (x:Var): Formula PA_Sig :=
  Formula.forAll x (Formula.eq (addT (Term.var x) zero) (Term.var x))

def PA_ax4 (x y: Var): Formula PA_Sig :=
  Formula.forAll x (Formula.forAll y (Formula.eq (addT (Term.var x) (S(Term.var y))) (S(addT (Term.var x) (Term.var y)))))

def PA_ax5 (x:Var) : Formula PA_Sig :=
  Formula.forAll x (Formula.eq (mulT (Term.var x) zero) zero)

def PA_ax6 (x y:Var): Formula PA_Sig :=
  Formula.forAll x (Formula.forAll y (Formula.eq (mulT (Term.var x) (S(Term.var y))) (addT (mulT (Term.var x) (Term.var y)) (Term.var x))))




def PA_Std : Structure PA_Sig :=
{ U := Nat,
  constInterp := fun c =>
    match c with
    | PA_Const.zero => 0,
  funcInterp1 := fun f t =>
    match f with
    | PA_Func.succ => Nat.succ t
    | _ => t,
  funcInterp2 := fun f t1 t2 =>
    match f with
    | PA_Func.add => t1 + t2
    | PA_Func.mul => t1 * t2
    | _ => t1
}


def t5 : Term PA_Sig :=
  S (S (S (S (S zero))))

#eval evalTerm PA_Std (fun _ => Nat.zero) (S t5)


theorem eval_zero (ρ) : evalTerm PA_Std ρ (Term.const PA_Const.zero) = (0 : ℕ) := by
  rfl

theorem eval_succ (ρ) (x) : evalTerm PA_Std ρ (S x) = (Nat.succ (evalTerm _ ρ x)) := by
  rfl

theorem eval_add (ρ) (x y) :
  evalTerm PA_Std ρ (addT x y) = Nat.add (evalTerm _ ρ x) (evalTerm _ ρ y) := by rfl

theorem eval_mul (ρ) (x y) :
  evalTerm PA_Std ρ (mulT x y) = Nat.mul (evalTerm _ ρ x) (evalTerm _ ρ y ):= by rfl


theorem eval_eq (ρ) (x y : Term PA_Sig) :
  evalFormula PA_Std ρ (eqT x y) = (evalTerm PA_Std ρ x = evalTerm PA_Std ρ y) := by rfl

theorem PA_ax1_satisfiable (x : Var) : satisfiable (PA_ax1 x) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax1, evalFormula, zero]
  intros a
  rw [eval_zero]
  rw [eval_succ]
  intro h
  contradiction

theorem PA_ax1_satisfiable2 (x: Var) : ∀ ρ : Env ℕ, evalFormula PA_Std ρ (PA_ax1 x):=by
    intros ρ
    simp [PA_ax1]
    simp [evalFormula]
    simp [zero]
    intro a
    rw [eval_zero]
    rw [eval_succ]
    intros h
    contradiction

theorem PA_ax2_satisfiable (x y: Var): satisfiable (PA_ax2 x y) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax2]
  simp [evalFormula]
  intros a k o
  rw [eval_succ] at o
  rw [eval_succ] at o
  apply Nat.succ.inj
  assumption

theorem PA_ax3_satisfiable (x : Var): satisfiable (PA_ax3 x ) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax3]
  simp [evalFormula]
  intros h
  rw [eval_add]
  rw [zero]
  apply Nat.add_zero


theorem PA_ax4_satisfiable (x y: Var): satisfiable (PA_ax4 x y) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax4]
  simp [evalFormula]
  intros h p
  rw [eval_add]
  rw [eval_succ]
  rw [eval_succ]
  rw [eval_add]
  exact Nat.add_succ _ _


theorem PA_ax5_satisfiable (x : Var): satisfiable (PA_ax5 x ) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax5]
  simp [evalFormula]
  intros h
  rw [eval_mul]
  rw [zero]
  apply Nat.mul_zero



theorem PA_ax6_satisfiable (x y: Var): satisfiable (PA_ax6 x y ) := by
  unfold satisfiable
  use PA_Std
  intro ρ
  simp [PA_ax6]
  simp [evalFormula]
  intros h p
  rw [eval_mul]
  rw [eval_add]
  rw [eval_mul]
  rw [eval_succ]
  apply Nat.mul_succ


def PA_ax7 (x y : Var) (A : Formula PA_Sig) : Formula PA_Sig :=
  ((A zero) ⋀ ∀ₚ x (A (Term.var x) ⇒ A (S (Term.var x)))) ⇒ ∀ₚ y (A (Term.var y))


theorem PA_induction_satisfiable (x y: Var): ∀ A : Term PA_Sig → Formula PA_Sig, satisfiable (PA_ax7 x y A  ) := by
  unfold satisfiable
  intros A
  use PA_Std
  intros ρ
  simp [PA_ax7]
  simp [evalFormula]
  intros h
  rw [evalFormula_conj] at h
  have h₀ := h.left
  have hᵢ := h.right
  rw [zero] at h₀
  rw [evalFormula_forAll] at hᵢ
  intros k
  specialize hᵢ k
  rw [evalFormula_imp] at hᵢ
  induction k with
  | zero =>
      exact h₀

theorem A_base (x : Var)(ρ : Env ℕ) : evalFormula PA_Std (updateEnv ρ x Nat.zero) (eqT (addT (Term.var x) zero) (Term.var x)) :=
by rfl


-- theorem PA_ax7_satisfiable (x : Var) (A : Term PA_Sig → Formula PA_Sig)
--   (h0 : ∀ ρ : Env ℕ, evalFormula PA_Std (updateEnv ρ x Nat.zero) (A (Term.var x)))
--   (hS : ∀ ρ : Env ℕ, ∀ n : ℕ,
--           evalFormula PA_Std (updateEnv ρ x n) (A (Term.var x)) →
--           evalFormula PA_Std (updateEnv ρ x n.succ) (A (Term.var x))) :
--   ∀ ρ : Env ℕ, evalFormula PA_Std ρ (PA_ax7 x A) := by
--   intro ρ
--   simp [PA_ax7, evalFormula]
--   intro h_conj y
--   induction y with
--   | zero =>
--     specialize h0 ρ
--     simp
--     exact h0
--   | succ n ih =>
--     have h_step := hS ρ n ih
--     exact h_step


def hasFreeVarTerm : Term PA_Sig → Var → Prop
| Term.var y, x => y = x
| Term.const _, _ => False
| Term.app1 _ ts, x => 

def hasFreeVar : Formula PA_Sig → Var → Prop
| Formula.eq t1 t2, x => hasFreeVarTerm t1 x ∨ hasFreeVarTerm t2 x
| Formula.rel _ ts, x => ∃ i, hasFreeVarTerm (ts i) x
| Formula.neg φ, x => hasFreeVar φ x
| Formula.imp φ ψ, x => hasFreeVar φ x ∨ hasFreeVar ψ x
| Formula.forAll y φ, x => hasFreeVar φ x ∧ x ≠ y



def substTerm (t : Term PA_Sig) (x : Var) (s : Term PA_Sig) : Term PA_Sig :=
  match t with
  | Term.var y => if y = x then s else Term.var y
  | Term.const c => Term.const c
  | Term.func f args => Term.func f (fun i => substTerm (args i) x s)


def renameTerm : Term PA_Sig → Var → Var → Term PA_Sig
| Term.var x, y, z =>
    if x = y then Term.var z else Term.var x
| Term.const c, _, _ =>
    Term.const c
| Term.func f ts, y, z =>
    Term.func f (fun i => renameTerm (ts i) y z)

def renameVar : Formula PA_Sig → Var → Var → Formula PA_Sig
| Formula.eq t1 t2, y, z =>
    Formula.eq (renameTerm t1 y z) (renameTerm t2 y z)
| Formula.rel r ts, y, z =>
    Formula.rel r (fun i => renameTerm (ts i) y z)
| Formula.neg φ, y, z =>
    Formula.neg (renameVar φ y z)
| Formula.imp φ ψ, y, z =>
    Formula.imp (renameVar φ y z) (renameVar ψ y z)
| Formula.forAll x φ, y, z =>
    if x = y then
      -- variabila bound x = y → nu renumim
      Formula.forAll x φ
    else
      Formula.forAll x (renameVar φ y z)


def freshVar (x : Var) : Var :=
  x ++ "_1"



def substFormula (φ : Formula PA_Sig) (x : Var) (s : Term PA_Sig) : Formula PA_Sig :=
  match φ with
  | Formula.eq t1 t2 => Formula.eq (substTerm t1 x s) (substTerm t2 x s)
  | Formula.rel r args => Formula.rel r (fun i => substTerm (args i) x s)
  | Formula.neg ψ => Formula.neg (substFormula ψ x s)
  | Formula.imp ψ ξ => Formula.imp (substFormula ψ x s) (substFormula ξ x s)
  | Formula.forAll y ψ =>
      if h1 : y = x then
        -- cazul 1: x este legată -> nu substituim în ψ
        Formula.forAll y ψ
      else if h2 : hasFreeVarTerm s y = True then
        -- cazul 2: variabila y apare liber în s -> risc de captură
        let z := freshVar (y)  -- trebuie implementat
        Formula.forAll z (substFormula (renameVar ψ y z) x s)
      else
        -- cazul 3: y ≠ x și y nu apare în s -> safe substitution
        Formula.forAll y (substFormula ψ x s)
