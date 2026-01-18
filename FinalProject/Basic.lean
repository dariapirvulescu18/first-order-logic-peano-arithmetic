set_option autoImplicit false

structure Signature where
  Rel   : Type
  Func  : Type
  Const : Type
  arityRel  : Rel → Nat
  arityFunc : Func → Nat

def Var := Nat
instance : DecidableEq Var := Nat.decEq

inductive Term (τ : Signature) where
| var  : Var → Term τ
| const : τ.Const → Term τ
| func : (f : τ.Func) → (Fin (τ.arityFunc f) → Term τ) → Term τ


inductive Formula (τ : Signature) where
| rel : (r : τ.Rel) → (Fin (τ.arityRel r) → Term τ) → Formula τ
| eq  : Term τ → Term τ → Formula τ
| neg : Formula τ → Formula τ
| imp : Formula τ → Formula τ → Formula τ
| forAll : Var → Formula τ → Formula τ

namespace Formula

infixr:70 " ⇒ " => imp

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
  U    : Type
  constInterp : τ.Const → U
  funcInterp  : (f : τ.Func) → (Fin (τ.arityFunc f) → U) → U
  relInterp   : (r : τ.Rel) → (Fin (τ.arityRel r) → U) → Prop

def Env (U : Type) := Var → U

def evalTerm {τ : Signature} (M : Structure τ) (ρ : Env M.U) : Term τ → M.U
| Term.var x     => ρ x
| Term.const c   => M.constInterp c
| Term.func f ts => M.funcInterp f (fun i => evalTerm M ρ (ts i))

def updateEnv {A : Type} (e : Var → A) (x : Var) (a : A) : Var → A :=
  fun v => if v = x then a else e v


def evalFormula {τ : Signature} (M : Structure τ) (ρ : Env M.U) : Formula τ → Prop
| Formula.eq t1 t2   => evalTerm M ρ t1 = evalTerm M ρ t2
| Formula.rel r ts   => M.relInterp r (fun i => evalTerm M ρ (ts i))
| Formula.neg φ      => ¬ evalFormula M ρ φ
| Formula.imp φ ψ    => evalFormula M ρ φ → evalFormula M ρ ψ
| Formula.forAll x φ => ∀ a : M.U, evalFormula M (fun v => if v = x then a else ρ v) φ


def satisfiable {τ : Signature} (φ : Formula τ) : Prop :=
  ∃ (M : Structure τ) (ρ : Env M.U), evalFormula M ρ φ


------------------------------------------

inductive PA_Const
| zero
deriving Repr, DecidableEq

inductive PA_Func
| succ  -- S(x)
| add   -- x + y
| mul   -- x * y
deriving Repr, DecidableEq

inductive PA_Rel
| eq
deriving Repr, DecidableEq

def PA_Sig : Signature :=
{ Rel := PA_Rel,
  Func := PA_Func,
  Const := PA_Const,
  arityRel := fun r =>
    match r with
    | PA_Rel.eq => 2,
  arityFunc := fun f =>
    match f with
    | PA_Func.succ => 1
    | PA_Func.add  => 2
    | PA_Func.mul  => 2
}


def x : Term PA_Sig := Term.var Nat.zero
def y : Term PA_Sig := Term.var (Nat.succ Nat.zero)
def z : Term PA_Sig := Term.var (Nat.succ (Nat.succ Nat.zero))


def zero : Term PA_Sig := Term.const PA_Const.zero

def S (t : Term PA_Sig) : Term PA_Sig :=
  Term.func PA_Func.succ (fun _ => t)

def addT (t1 t2 : Term PA_Sig) : Term PA_Sig :=
  Term.func PA_Func.add (fun i => if i.val = 0 then t1 else t2)

def mulT (t1 t2 : Term PA_Sig) : Term PA_Sig :=
  Term.func PA_Func.mul (fun i => if i.val = 0 then t1 else t2)

#check addT y z
#check S x


def fin0 : Fin 1 := ⟨0, by decide⟩
def fin0of2 : Fin 2 := ⟨0, by decide⟩
def fin1of2 : Fin 2 := ⟨1, by decide⟩

def PA_Std : Structure PA_Sig :=
{ U := Nat,
  constInterp := fun c =>
    match c with
    | PA_Const.zero => 0,
  funcInterp := fun f args =>
  match f with
  | PA_Func.succ => args fin0 + 1
  | PA_Func.add  => args fin0of2 + args fin1of2
  | PA_Func.mul  => args fin0of2 * args fin1of2
  relInterp := fun r args =>
  match r with
  | PA_Rel.eq => args ⟨0, by decide⟩ = args ⟨1, by decide⟩

}

def PA_ax1 : Formula PA_Sig :=
  Formula.forAll Nat.zero (Formula.neg (Formula.eq (S x) zero))

def PA_ax2 : Formula PA_Sig :=
  Formula.forAll Nat.zero (Formula.forAll (Nat.succ Nat.zero) (Formula.imp (Formula.eq (S x) (S y)) (Formula.eq x y)))

def PA_ax3 : Formula PA_Sig :=
  Formula.forAll  Nat.zero (Formula.eq (addT x zero) x)

def PA_ax4 : Formula PA_Sig :=
  Formula.forAll Nat.zero (Formula.forAll (Nat.succ Nat.zero) (Formula.eq (addT x (S y)) (S (addT x y))))

def PA_ax5 : Formula PA_Sig :=
  Formula.forAll Nat.zero (Formula.eq (mulT x zero) zero)

def PA_ax6 : Formula PA_Sig :=
  Formula.forAll Nat.zero (Formula.forAll (Nat.succ Nat.zero) (Formula.eq (mulT x (S y)) (addT (mulT x y) x)))

#check evalFormula PA_Std (fun _ => Nat.zero) PA_ax1


def t5 : Term PA_Sig :=
  S (S (S (S (S zero))))

#eval evalTerm PA_Std (fun _ => Nat.zero) (S t5)
