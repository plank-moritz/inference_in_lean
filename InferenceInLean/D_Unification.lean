import InferenceInLean.A_Syntax
import InferenceInLean.B_Semantics
import InferenceInLean.C_Models

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models

/- ### Unification -/

namespace Unification

@[simp]
def Equality (sig : Signature) (X : Variables) :=
  Term sig X × Term sig X

@[simp]
def EqualityProblem (sig : Signature) (X : Variables) :=
  List (Equality sig X)

instance {sig : Signature} {X : Variables} : Membership (Equality sig X) (EqualityProblem sig X) :=
  List.instMembership

@[simp]
def EqualityProblem.freeVars {sig : Signature} {X : Variables} : EqualityProblem sig X -> Set X
  | [] => ∅
  | (lhs, rhs) :: eqs => Term.freeVars sig X lhs ∪ Term.freeVars sig X rhs ∪ freeVars eqs

@[simp]
def Unifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  ∀ eq ∈ E, have ⟨lhs, rhs⟩ := eq; lhs.substitute σ = rhs.substitute σ

def example_unification_problem : EqualityProblem (Signature.mk String String) String :=
  [(Term.func "f" [Term.var "x"], Term.var "y")]

def example_unifier : Substitution (Signature.mk String String) String :=
  fun x => if x == "y" then Term.func "f" [Term.var "x"] else Term.var x

theorem example_unification : Unifier example_unification_problem example_unifier := by
  simp [example_unification_problem, example_unifier]

@[simp]
def MostGeneralUnifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  Unifier E σ ∧ (∀ τ : Substitution sig X, Unifier E τ → σ ≤ τ)

lemma mgu_imp_unifier {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X)
    (σ : Substitution sig X) : MostGeneralUnifier E σ → Unifier E σ := fun ⟨h, _⟩ => h

@[simp]
def Unifiable {sig : Signature} {X : Variables} [DecidableEq X]
  (E : EqualityProblem sig X) : Prop := ∃ σ : Substitution sig X, Unifier E σ

theorem unifiable_iff_mgu_idempot {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (E : EqualityProblem sig X) : Unifiable E ↔ ∃ σ : Substitution sig X,
      MostGeneralUnifier E σ ∧ Idempotent σ ∧ σ.domain ∪ σ.codomain ⊆ E.freeVars := by
  apply Iff.intro
  · sorry
    /- This direction would need the standard unification algorithm.
    I have played around with implementing it but it brings quite some chanllenge with it and feels
    like it's outside the scope of this project.
      -/
  · intro h
    obtain ⟨σ, ⟨⟨⟩⟩⟩ := h
    use σ
alias main_unification_theorem := unifiable_iff_mgu_idempot


/- Rule-Based Naive Standard Unification Algorithm -/

def var_includes {sig : Signature} {X : Variables} [DecidableEq X] (s : Term sig X) (var : List X) : Bool :=
match s with
  | Term.var x => (x ∈ var)
  | _ => false

def term_includes {sig : Signature} {X : Variables} [DecidableEq X] (s : Term sig X) (x : X) : Bool :=
match s with
  | Term.var y => (x == y)
  | Term.func _ [] => false
  | Term.func f (a :: args) =>
      if (term_includes a x) then true
      else (term_includes (Term.func f args) x)

def E_includes {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X) (x : X) : Bool :=
match E with
  | [] => false
  | (s, t) :: args =>
      if ((term_includes s x) || (term_includes t x)) then true
      else (E_includes args x)

def decomposition {sig : Signature} {X : Variables} (E : EqualityProblem sig X) (args bargs: List (Term sig X)) : Option (EqualityProblem sig X) :=

  let rec decomposition_rec (E : EqualityProblem sig X) (args bargs: List (Term sig X)) : EqualityProblem sig X :=
    match args, bargs with
      | (a :: aa), (b :: bb) =>
        let e : Equality sig X := (a, b)
        decomposition_rec (e :: E) aa bb
      | _, _ => E

decomposition_rec E args bargs

/-Termination proof still to be done; tried out different approaches so far but Lean still cannot observe eventual termination.
  Therefore, the definition is for now partial -/
partial def Naive_Standard_Unification {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
(E : EqualityProblem sig X) (var: List X) (σ : Substitution sig X) : Option (Substitution sig X) :=

match E with
| [] => some σ
| (s, t) :: E' =>

  let s' := (s.substitute σ)
  let t' := (t.substitute σ)

  if (eqTerm sig X s' t') then (Naive_Standard_Unification E' var σ)

  else let (s'', t'') :=
    match s', t' with
      | _, Term.var y =>
        if ¬(var_includes s' var) then (Term.var y, s')
        else (s', t')
      | _, _ => (s', t')

    match s'', t'' with

    | Term.func f args, Term.func g bargs =>
      if (f == g) && (args.length == bargs.length) then
        match (decomposition E args bargs) with
        | some Eq => (Naive_Standard_Unification Eq var σ)
        | none => none
      else none

    | Term.var x, _ =>
      if (E_includes E x) && ¬(term_includes t'' x) then
        let hσ := (σ.modify x t'')
        let E' := E.map (fun (s,t) => (s.substitute hσ, t.substitute hσ))
        let e : Equality sig X := (Term.var x, t'')
        Naive_Standard_Unification (e :: E') var hσ
      else if (term_includes t'' x) && ¬(eqTerm sig X s'' t'') then none
      else none

    | Term.func _ _, Term.var _ => none
