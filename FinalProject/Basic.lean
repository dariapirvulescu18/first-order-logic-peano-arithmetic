import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false
set_option linter.flexible false

--SINTAX

/-define the arity of the functions for the FOL, because we need it for Peano, we can
define it for the functions that we need (plus and mult (binary) and succ(unary))
-/

inductive Arity
| unary
| binary
deriving DecidableEq, Repr

--FOL signature
structure Signature where
  Func : Type
  Const : Type
  arityFunc : Func → Arity

abbrev Var := String
instance : DecidableEq Var := String.decEq

--FOL definition of a Term
inductive Term (τ : Signature) where
| var   : Var → Term τ
| const : τ.Const → Term τ
| app1  : (f : τ.Func) → (Term τ) → Term τ
| app2  : (f : τ.Func) → (Term τ) → (Term τ) → Term τ

--FOL definition of a Formula
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

-- (¬ϕ)→ψ
def disj {τ : Signature} (φ ψ : Formula τ) : Formula τ := (∼ φ) ⇒ ψ
infixl:80 " ⋁ " => disj

-- ¬(ϕ→(¬ψ))
def conj {τ : Signature} (φ ψ : Formula τ) : Formula τ := ∼ (φ ⇒ (∼ ψ))
infixl:80 " ⋀ " => conj

-- (ϕ→ψ)∧(ψ→ϕ)
def iff {τ : Signature} (φ ψ : Formula τ) : Formula τ := (φ ⇒ ψ) ⋀ (ψ ⇒ φ)
infixl:70 "↔" => iff

end Formula

--SEMATICS
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

def hasFreeVarTerm : Term PA_Sig → Var → Prop
| Term.var y, x => y = x
| Term.const _, _ => False
| Term.app1 _ t1, x => hasFreeVarTerm t1 x
| Term.app2 _ t1 t2, x => hasFreeVarTerm t1 x ∨ hasFreeVarTerm t2 x

def hasFreeVar : Formula PA_Sig → Var → Prop
| Formula.eq t1 t2, x => hasFreeVarTerm t1 x ∨ hasFreeVarTerm t2 x
| Formula.neg φ, x => hasFreeVar φ x
| Formula.imp φ ψ, x => hasFreeVar φ x ∨ hasFreeVar ψ x
| Formula.forAll y φ, x => hasFreeVar φ x ∧ x ≠ y

def substTerm (t : Term PA_Sig) (x : Var) (s : Term PA_Sig) : Term PA_Sig :=
  match t with
  | Term.var y => if y = x then s else Term.var y
  | Term.const c => Term.const c
  | Term.app1 f t1 => Term.app1 f (substTerm t1 x s)
  | Term.app2 f t1 t2 => Term.app2 f (substTerm t1 x s) (substTerm t2 x s)

def varsOfTerm : Term PA_Sig → Set Var
| Term.var y => {y}
| Term.const _ => ∅
| Term.app1 _ t1 => varsOfTerm t1
| Term.app2 _ t1 t2 => varsOfTerm t1 ∪ varsOfTerm t2

def varsOfFormula : Formula PA_Sig → Set Var
| Formula.eq t1 t2 => varsOfTerm t1 ∪ varsOfTerm t2
| Formula.neg φ => varsOfFormula φ
| Formula.imp φ ψ => (varsOfFormula φ) ∪ (varsOfFormula ψ)
| Formula.forAll x φ => {x} ∪ (varsOfFormula φ)

def boundedVars : Formula PA_Sig → Set Var
| Formula.eq _ _ => ∅
| Formula.neg φ => boundedVars φ
| Formula.imp φ ψ => (boundedVars φ) ∪ (boundedVars ψ)
| Formula.forAll x φ => {x} ∪ (boundedVars φ)


  -- def isFreeSubstitution (φ : Formula PA_Sig) (x : Var) (s : Term PA_Sig) : Prop :=
  -- match φ with
  -- | Formula.eq t1 t2 => (hasFreeVarTerm t1 x) ∧ (hasFreeVarTerm t2 x)
  -- | Formula.neg ψ => isFreeSubstitution ψ x s
    -- have varsOfS := varsOfTerm s
    -- have condition1 := (varsOfS = ∅) = True
    -- have varsOfΦ := varsOfFormula φ
    -- have condition2 := ((varsOfS ∩ varsOfΦ) = ∅) = True
    -- have boundedVarsOfφ := boundedVars φ
    -- have condition3 := ((varsOfS ∩ boundedVarsOfφ) = ∅) = True
    -- have condition4 := ((x ∈ varsOfΦ) = False) = True
    -- have condition5 := hasFreeVar φ x
    -- condition1 ∨ condition2 ∨ condition3 ∨ condition4 ∨ condition5

  -- def freshVar (x : Var) : Var :=
  --   x ++ "_1"

def freshVarTerm : Term PA_Sig → Var
| Term.var y => y ++ "_1"
| Term.const _ => "_"
| Term.app1 _ t1 => (freshVarTerm t1) ++ "_"
| Term.app2 _ t1 t2 => freshVarTerm t1 ++ freshVarTerm t2

def freshVar : Formula PA_Sig → Var
| Formula.eq t1 t2 => freshVarTerm t1 ++ freshVarTerm t2 ++ "_"
| Formula.neg φ => (freshVar φ) ++ "_"
| Formula.imp φ ψ => (freshVar φ) ++ (freshVar ψ) ++ "_"
| Formula.forAll x φ => x ++ (freshVar φ) ++ "_"

def renameVarInTerm (t : Term PA_Sig) (x : Var) (y : Var) : Term PA_Sig :=
match t with
| Term.var z => if z = x then Term.var y else (Term.var z)
| Term.const c => Term.const c
| Term.app1 f t1 => Term.app1 f (renameVarInTerm t1 x y)
| Term.app2 f t1 t2 => Term.app2 f (renameVarInTerm t1 x y) (renameVarInTerm t2 x y)

def rename (φ : Formula PA_Sig) (x : Var) (y : Var) : Formula PA_Sig :=
match φ with
| Formula.eq t1 t2 => Formula.eq (renameVarInTerm t1 x y) (renameVarInTerm t2 x y)
| Formula.neg ψ => Formula.neg (rename ψ x y)
| Formula.imp ψ χ => Formula.imp (rename ψ x y) (rename χ x y)
| Formula.forAll z ψ =>
    if x = z then
      Formula.forAll y (rename ψ x y)
    else
      Formula.forAll z (rename ψ x y)


@[simp]
def Formula.size (φ : Formula PA_Sig) : Nat :=
  match φ with
  | .eq _ _ => 1
  | .neg φ => φ.size + 1
  | .imp φ₁ φ₂ => φ₁.size + φ₂.size + 1
  | .forAll _ φ => φ.size + 1

@[simp]
theorem rename_size (φ : Formula PA_Sig) (x y : Var) : (rename φ x y).size = φ.size := by
  induction φ generalizing x y with
    | eq t1 t2 =>
        simp [rename, Formula.size]
    | neg φ ih =>
        simp [rename, Formula.size, ih]
    | imp φ₁ φ₂ ih₁ ih₂ =>
        simp [rename, Formula.size, ih₁, ih₂]
    | forAll z φ ih =>
        simp [rename, Formula.size]
        split_ifs <;> simp [Formula.size, ih]

def substFormula (φ : Formula PA_Sig) (x : Var) (s : Term PA_Sig) : Formula PA_Sig :=
  match φ with
  | Formula.eq t1 t2    => Formula.eq (substTerm t1 x s) (substTerm t2 x s)
  | Formula.neg ψ       => Formula.neg (substFormula ψ x s)
  | Formula.imp ψ ξ     => Formula.imp (substFormula ψ x s) (substFormula ξ x s)
  | Formula.forAll y ψ  =>
      if y = x then
        Formula.forAll y ψ
      else
        let fresh := freshVar (Formula.forAll y ψ)
        Formula.forAll fresh (substFormula (rename ψ y fresh) x s)
termination_by Formula.size φ


lemma eval_substTerm (M : Structure PA_Sig) (ρ : Env M.U) (t : Term PA_Sig) (x : Var) (s : Term PA_Sig) :
    evalTerm M ρ (substTerm t x s) = evalTerm M (updateEnv ρ x (evalTerm M ρ s)) t := by
  induction t with
  | var y =>
      simp [substTerm, evalTerm, updateEnv]
      split
      · simp [*]
      · rfl
  | const c =>
      simp [substTerm, evalTerm]
  | app1 f t1 ih =>
      simp [substTerm, evalTerm, ih]
  | app2 f t1 t2 ih1 ih2 =>
      simp [substTerm, evalTerm, ih1, ih2]

lemma eval_renameVarInTerm
  (M : Structure PA_Sig)
  (ρ : Env M.U)
  (t : Term PA_Sig)
  (x y : Var) :
  evalTerm M ρ (renameVarInTerm t x y) =
  evalTerm M (updateEnv ρ x (ρ y)) t := by
  induction t generalizing ρ with
  | var z =>
      simp [renameVarInTerm, evalTerm, updateEnv]
      split
      · rfl
      · rfl
  | const c =>
      simp [renameVarInTerm, evalTerm]
  | app1 f t ih =>
      simp [renameVarInTerm, evalTerm, ih]
  | app2 f t₁ t₂ ih₁ ih₂ =>
      simp [renameVarInTerm, evalTerm, ih₁, ih₂]

-- lemma eval_rename
--   (M : Structure PA_Sig)
--   (ρ : Env M.U)
--   (φ : Formula PA_Sig)
--   (x y : Var) :
--   evalFormula M ρ (rename φ x y) =
--   evalFormula M (updateEnv ρ x (ρ y)) φ := by
--   induction φ generalizing ρ with
--   | eq t1 t2 =>
--       simp [rename, evalFormula, eval_renameVarInTerm]
--   | neg ψ ih =>
--       simp [rename, evalFormula, ih]
--   | imp ψ χ ihψ ihχ =>
--       simp [rename, evalFormula, ihψ, ihχ]
--   | forAll z ψ ih =>
--       simp [rename, evalFormula]
--       split_ifs
--       · rename_i h_eq
--         rw [h_eq]
--         specialize ih ρ
--         apply Iff.intro
--         . intros ip
--           rw [evalFormula] at ip
--           intros v
--           specialize ip v
--           rw [←h_eq] at ip

--           sorry
--         . intros ip
--           intros v
--           specialize ip v
--           rw [←h_eq] at ip
--           sorry
--       · sorry

lemma updateEnv_idempotent {A : Type} (ρ : Var → A) (x : Var) :
  updateEnv ρ x (ρ x) = ρ := by
funext v
simp [updateEnv]
by_cases h : v = x
· simp [h]
· simp [h]

lemma updateEnv_comm {A : Type} (ρ : Var → A) (x y : Var) (vx vy : A) (h : x ≠ y) :
  updateEnv (updateEnv ρ x vx) y vy = updateEnv (updateEnv ρ y vy) x vx := by
  funext w
  simp [updateEnv]
  by_cases hxw : w = x
  · by_cases hyw : w = y
    . rw [hyw]
      simp
      intros i1
      rw [i1] at h
      contradiction
    . rw [hxw]
      simp
      intros i1
      contradiction
  · by_cases hyw : w = y
    · rw [hyw]
      simp
      intros i1
      rw [i1] at h
      contradiction
    · simp [hxw, hyw]

--basically updateting something 2 times erases the effects of the fisrt update
lemma updateEnv_shadow
  {U : Type}
  (ρ : Env U)
  (y : Var)
  (v₁ v₂ : U) :
  updateEnv (updateEnv ρ y v₁) y v₂ = updateEnv ρ y v₂ :=
by
  funext z
  unfold updateEnv
  by_cases h : z = y
  · simp [h]
  · simp [h]

-- lemma evalFormula_rename_forall_fresh
--   (M : Structure PA_Sig)
--   (ρ : Env M.U)
--   (ψ : Formula PA_Sig)
--   (y : Var) :
--   evalFormula M ρ (rename ψ y (freshVar (∀ₚ y ψ))) =
--   evalFormula M ρ ψ := by sorry

lemma eval_substFormula (M : Structure PA_Sig) (ρ : Env M.U) (φ : Formula PA_Sig) (x : Var) (s : Term PA_Sig) :
    evalFormula M ρ (substFormula φ x s) = evalFormula M (updateEnv ρ x (evalTerm M ρ s)) φ := by
  induction φ generalizing ρ with
  | eq t1 t2 =>
      simp [substFormula, evalFormula, eval_substTerm]
  | neg ψ ih =>
      simp [substFormula, evalFormula, ih]
  | imp ψ χ ihψ ihχ =>
      simp [substFormula, evalFormula, ihψ, ihχ]
  | forAll y ψ ih =>
      simp [evalFormula]
      constructor
      . intros ip
        intros val
        simp [substFormula] at ip
        by_cases h_eq : (x=y)
         --x=y
        . simp [h_eq] at ip
          simp [evalFormula] at ip
          specialize ip val
          rw [h_eq]
          specialize ih ρ
          rw [h_eq] at ih
          rw [updateEnv_shadow]
          exact ip
         --x!=y
        . have h' : (¬ y = x) := by
            simpa [eq_comm] using h_eq
          have ip' : evalFormula M ρ (∀ₚ (freshVar (∀ₚ y ψ)) (substFormula (rename ψ y (freshVar (∀ₚ y ψ))) x s)) := by
            simpa [h'] using ip
          simp [evalFormula] at ip'
          specialize ip' val
          specialize ih ((updateEnv ρ (freshVar (∀ₚy ψ)) val))
          have I₁: evalFormula M (updateEnv ρ (freshVar (∀ₚy ψ)) val) (substFormula (rename ψ y (freshVar (∀ₚy ψ))) x s) =
              evalFormula M (updateEnv (updateEnv ρ x (evalTerm M ρ s) ) (freshVar (∀ₚy ψ)) val) (substFormula ψ y (Term.var (freshVar (∀ₚy ψ)))) := by
                sorry
          rw [I₁] at ip'
          -- right now it's pretty obvious that ip' is actually the goal
          have obvious : (evalFormula M (updateEnv (updateEnv ρ x (evalTerm M ρ s)) (freshVar (∀ₚy ψ)) val)
  (substFormula ψ y (Term.var (freshVar (∀ₚy ψ))))) = (evalFormula M (updateEnv (updateEnv ρ x (evalTerm M ρ s)) y val) ψ) := by sorry
          rw [obvious] at ip'
          assumption
      . intros ip
        simp [substFormula]
        by_cases h_eq : (x=y)
        --x=y
        . simp [h_eq]
          simp [evalFormula]
          intros val
          specialize ip val
          rw [h_eq] at ip
          rw [updateEnv_shadow] at ip
          exact ip
        --x!=y
        . have h' : (¬ y = x) := by
            simpa [eq_comm] using h_eq
          sorry

-- def PA_ax7 (x  : Var) (A : Formula PA_Sig) : Formula PA_Sig :=
--     ((substFormula A x zero) ⋀ ∀ₚ x (A ⇒ substFormula A x (S (Term.var x)))) ⇒
--       ∀ₚ x A

-- theorem PA_ax7_satisfiable (x : Var) (A : Formula PA_Sig)
--   (h0 : ∀ ρ : Env ℕ, evalFormula PA_Std (updateEnv ρ x Nat.zero) (A))
--   (hS : ∀ ρ : Env ℕ, ∀ n : ℕ,
--           evalFormula PA_Std (updateEnv ρ x n) (A)→
--           evalFormula PA_Std (updateEnv ρ x n.succ) (A)):
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


def PA_ax7 (x y : Var) (A : Formula PA_Sig) : Formula PA_Sig :=
  ((substFormula A x zero) ⋀ ∀ₚ x ((substFormula A x (Term.var x)) ⇒ substFormula A x (S (Term.var x)))) ⇒
    ∀ₚ y (substFormula A x (Term.var y))

theorem PA_induction_satisfiable (x : Var): ∀ A : Formula PA_Sig, satisfiable (PA_ax7 x x A  ) := by
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
  induction k with
  | zero =>
      rw [eval_substFormula] at h₀
      rw [eval_substFormula]
      have I₂ : (updateEnv ρ x (PA_Std.constInterp PA_Const.zero)) = (updateEnv ρ x Nat.zero) := by
        rfl
      rw [evalTerm] at h₀
      rw [I₂] at h₀
      rw [evalTerm]
      have I₄ : updateEnv (updateEnv ρ x Nat.zero) x (updateEnv ρ x Nat.zero x) = (updateEnv ρ x Nat.zero) := by
        funext v
        simp [updateEnv]
        intros o₁
        intros o₂
        contradiction
      rw [I₄]
      exact h₀
  | succ numar ip =>
    specialize hᵢ numar ip
    have S₁ : evalFormula PA_Std (updateEnv ρ x numar.succ) (substFormula A x (Term.var x)) = evalFormula PA_Std (updateEnv ρ x numar.succ) A := by
      rw [eval_substFormula]
      have eval_x : evalTerm PA_Std (updateEnv ρ x numar.succ) (Term.var x) = numar.succ := by
        simp [evalTerm, updateEnv]
      rw [eval_x]
      have shadow : updateEnv (updateEnv ρ x numar.succ) x numar.succ = updateEnv ρ x numar.succ := by
        funext v
        simp [updateEnv]
        by_cases h : v = x
        · simp [h]
        · simp [h]
      rw [shadow]
    rw [S₁]
    rw [eval_substFormula] at hᵢ
    have eval_ceva : (evalTerm PA_Std (updateEnv ρ x numar) S(Term.var x)) = numar.succ := by
      simp
      simp [eval_succ]
      rw [evalTerm]
      simp [updateEnv]
    rw [eval_ceva] at hᵢ
    have shadow : (updateEnv (updateEnv ρ x numar) x numar.succ) = updateEnv ρ x numar.succ := by
      funext v
      simp [updateEnv]
      by_cases h : v = x
      . simp [h]
      . simp [h]
    rw [shadow] at hᵢ
    exact hᵢ



def ρ : Env ℕ := fun v => if v = "x" then 5 else 0
#eval ρ "x"   -- expects 5
#eval ρ "y"   -- expects 0
#eval (updateEnv (updateEnv ρ "x" Nat.zero) "x" Nat.zero) "x"
#eval (updateEnv ρ "x" Nat.zero) "x"
#eval (updateEnv (updateEnv ρ "x" Nat.zero.succ) "x" (Nat.succ (updateEnv ρ "x" Nat.zero.succ "x"))) "x"
#eval (updateEnv (updateEnv ρ "x" Nat.zero.succ.succ) "x" (ρ "x")) "x"
#check (Term.var ("x"))
