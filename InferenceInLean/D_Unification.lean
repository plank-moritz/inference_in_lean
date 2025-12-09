import InferenceInLean.A_Syntax
import InferenceInLean.B_Semantics
import InferenceInLean.C_Models

set_option autoImplicit false
set_option diagnostics false

open Syntax
open Semantics
open Models

/- ### Unification -/

namespace Unification


@[simp]
abbrev Equality (sig : Signature) (X : Variables) :=
Term sig X × Term sig X

@[simp]
abbrev EqualityProblem (sig : Signature) (X : Variables) :=
  List (Equality sig X)

instance {sig : Signature} {X : Variables} : Membership (Equality sig X) (EqualityProblem sig X) :=
  List.instMembership

@[simp]
def EqualityProblem.freeVars {sig : Signature} {X : Variables} [DecidableEq X] :
    EqualityProblem sig X -> Set X
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







----------------------------------------------------------------------------------------------------
--The project is still work in progress and therefore definitions and lemmas may include mistakes --
----------------------------------------------------------------------------------------------------





----------------------------
--Unification algoirthm --
----------------------------

/-One formal step of the unification algorithm:
  Based on Christian Sternagel and René Thiemann's Isabelle implementation of (abstract) unification:
  https://www.isa-afp.org/sessions/first_order_terms/#Abstract_Unification.html &
  https://www.isa-afp.org/sessions/first_order_terms/#Unification.html. License : LGPL -/

def sub_E {sig : Signature} {X : Variables} [DecidableEq X] (σ : Substitution sig X) [DecidableEq X] : EqualityProblem sig X -> EqualityProblem sig X
| [] => []
| (s,t) :: E => ((s.substitute σ, t.substitute σ) :: (sub_E σ E))

inductive Unification_Step  {sig : Signature} {X : Variables} [DecidableEq X] [BEq (sig.funs)]
: Substitution sig X -> EqualityProblem sig X -> EqualityProblem sig X -> Prop
where
| refl (t : Term sig X) (E: EqualityProblem sig X) (σ : Substitution sig X) : (Unification_Step σ ((t,t) :: E) E)
| decomposition  (f : sig.funs) (args brgs : List (Term sig X)) (E : EqualityProblem sig X) (σ : Substitution sig X)
  (len: args.length = brgs.length) : (Unification_Step σ ((Term.func f args, Term.func f brgs) :: E) ((List.zip args brgs) ++ E))
| var_left  (x : X) (t : Term sig X) (E : EqualityProblem sig X) (σ : Substitution sig X) (not_in : (x ∉ Term.freeVarsList sig X t)) :
  (Unification_Step  (σ.modify x t) ((Term.var x, t) :: E) (sub_E (σ.modify x t) E))
| var_right (x : X) (t : Term sig X) (E : EqualityProblem sig X) (σ : Substitution sig X) (not_in : (x ∉ Term.freeVarsList sig X t))  :
  (Unification_Step  (σ.modify x t) ((t,Term.var x) :: E) (sub_E (σ.modify x t) E))

----------------------

--One concret step of the unification algorithm --

def Naive_Standard_Unification {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
 (E : EqualityProblem sig X) (σ : Substitution sig X) : Option (EqualityProblem sig X × Substitution sig X) :=

match E with

| [] => some ([], σ)
| (s, t) :: E' =>

  if eqTerm sig X s t then some (E', σ)

  else match s, t with

    | Term.func f args, Term.func g gargs =>
      if (f == g) ∧ (args.length == gargs.length)
      then some ((List.zip args gargs) ++ E', σ)
      else none

    | Term.func _ _, Term.var x =>
      if (x ∉ Term.freeVarsList sig X s)
      then
        let hσ := σ.modify x s
        some ((sub_E hσ E'), hσ)
      else none

    | Term.var x, t'  =>
      if (x ∉ Term.freeVarsList sig X t')
      then
        let hσ := σ.modify x t'
        some (sub_E hσ E', hσ)
      else none

--Unification algorithm recursion --

partial def Naive_Standard_Unification_Rec {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
 (E : EqualityProblem sig X) (σ : Substitution sig X) : Option (Substitution sig X) :=

 match Naive_Standard_Unification E σ with
  | none => none
  | some ([], σ') => some σ'
  | some (E', σ') => Naive_Standard_Unification_Rec E' σ'

-- Initial substitution to start the algorithm --

def initSubst {sig : Signature} {X : Variables} : Substitution sig X := fun x => Term.var x

def initStart {sig X} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X) : Option (Substitution sig X) :=
Naive_Standard_Unification_Rec E initSubst

-- Unification_Step formalizes concrete steps of Naive_Standard_Unification --

lemma Unify_Step  {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E E' : EqualityProblem sig X)
(σ σ' : Substitution sig X) (algo : Naive_Standard_Unification E σ = some (E', σ')) : Unification_Step σ E E' := by
sorry


------------------------------------------------------------------------
--Proposition 3.10.3 & required definitions:
--If an EqualityProblem is in a SolvedForm then the Solution Sigma_Solved
--is a Most General Unifier of this EqualityProblem
------------------------------------------------------------------------

def Solved_Form {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X) : Prop :=
(∀ s t, (s, t) ∈ E -> ∃ x, s = Term.var x) ∧ --only variables on the left side
(∀ x t₁ t₂, (Term.var x, t₁) ∈ E -> (Term.var x, t₂) ∈ E -> (t₁ = t₂)) ∧ -- pairwise distinctness
(∀ x t, (Term.var x, t) ∈ E -> (x ∉ Term.freeVarsList sig X t)) -- no left-sided variables included in the term variables

def Sigma_Solved  {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X) : Substitution sig X :=
match E with
| [] => fun x => Term.var x
| (Term.var x, t) :: E' =>
    let σ := Sigma_Solved E'
    let t' := t.substitute σ
    σ.modify x t'
| _ :: E' => Sigma_Solved E'

lemma Solution {sig : Signature} {X : Variables} [DecidableEq X] (E:EqualityProblem sig X) (solved : Solved_Form E) :
Unifier E (Sigma_Solved E) := by
sorry

lemma Sigma {sig : Signature} {X : Variables} [DecidableEq X] (E:EqualityProblem sig X) (solved : Solved_Form E)
(τ : Substitution sig X) (hτ : Unifier E τ) : Sigma_Solved E ≤ τ := by
sorry

lemma Most_General_Sigma_Solved {sig : Signature} {X:Variables} [DecidableEq X] (E : EqualityProblem sig X) (solved : Solved_Form E) :
MostGeneralUnifier E (Sigma_Solved E) := by
constructor
· exact (Solution E solved)
· intro τ hτ
  exact (Sigma E solved τ hτ)

--Proposition 3.10.3 implies : if a MGU exists, then the resulting EquationProblem E' is in a Solved_Form with a Sigma_Solved for E'
lemma Ex_SolvedForm_Sigma {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X) (σ' : Substitution sig X)
(algo : Naive_Standard_Unification_Rec E initSubst = some σ') : ∃ E', Solved_Form E' ∧ (σ' = Sigma_Solved E') := by
sorry

-------------------------------------------------------------------------------------------------------
--Theorem 3.10.4
-- 1. If UNIF1 σ E E' / Naive_Standard_Unification then (∀ τ is a Unifier of E <-> τ is a Unifier of E')
-------------------------------------------------------------------------------------------------------

lemma unifier_eq_step {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E E' : EqualityProblem sig X)
(σ : Substitution sig X) (hUNIF : Unification_Step σ E E') : (∀ τ,  Unifier E τ ↔ Unifier E' τ) := by
intro τ
induction hUNIF with
| refl => simp [Unifier]
| decomposition f args bargs E σ hlen => sorry
| var_left x t E σ not_in => sorry
| var_right x t E σ not_in => sorry

lemma unifier_eq_algorithm {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E E' : EqualityProblem sig X)
(σ σ' : Substitution sig X) (algo : Naive_Standard_Unification E σ = some (E', σ')) : ∀ τ, Unifier E τ ↔ Unifier E' τ := by
intro τ
have hstep : Unification_Step σ E E' := Unify_Step E E' σ σ' algo
exact unifier_eq_step E E' σ hstep τ


--------------------------------------------------------------------------
--Theorem 3.10.4
-- 2. If E (Naive_Standard_Unification) -> ⊥, then E is not unifiable
--------------------------------------------------------------------------

lemma uneq_none {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X)
(σ : Substitution sig X) (hσ : Unifiable E) : Naive_Standard_Unification_Rec E initSubst ≠ none := by
sorry

lemma non_unifiable {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X)
(h_none : Naive_Standard_Unification_Rec E initSubst = none) : ¬(Unifiable E) := by
intro hUnif
rcases hUnif with ⟨σ, hσ⟩
have huneq_none : (Naive_Standard_Unification_Rec E initSubst ≠ none) := (uneq_none E σ (hσ := ⟨σ,hσ⟩))
exact huneq_none h_none

----------------------------------------------------------------------------------
--Theorem 3.10.4
-- 3. If E (Naive_Standard_Unification) -> E′(Solved_Form), then σE is a MGU of E
----------------------------------------------------------------------------------

lemma Solved_Form_Then_MGU {sig : Signature} {X : Variables} [DecidableEq X] (E E' : EqualityProblem sig X) (σE : Substitution sig X)
(solved : (Solved_Form E')) (τ_eq : (∀ τ, Unifier E τ ↔ Unifier E' τ)) (hσ : (σE = Sigma_Solved E')):
MostGeneralUnifier E σE := by

subst hσ
have mgs_solved : MostGeneralUnifier E' (Sigma_Solved E') := Most_General_Sigma_Solved E' solved
rcases mgs_solved with ⟨hU', hmgu⟩

constructor
· exact (τ_eq (Sigma_Solved E')).mpr hU'
· intro τ hτ
  have Unifier_E' : Unifier E' τ := (τ_eq τ).mp hτ
  exact hmgu τ Unifier_E'

-----------------------------------------------------------------------------
--Unifiable E ↔ ∃ σ : Substitution sig X, σ.domain ∪ σ.codomain ⊆ E.freeVars
-----------------------------------------------------------------------------

lemma E'_freeVars_Subset_E_freeVars {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E E' : EqualityProblem sig X)
(σ σ': Substitution sig X) (hUNIF : Unification_Step σ E E') : E'.freeVars ⊆ E.freeVars := by
intro x hx
induction hUNIF with
| refl t E => simp_all
| decomposition f args bargs E hlen => sorry
| var_left x t E σ not_in => sorry
| var_right x t E σ not_in => sorry

lemma Solved_Dom_Subset_fV  {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
(E : EqualityProblem sig X) (solved : Solved_Form E) : (Sigma_Solved E).domain ⊆ E.freeVars := by

induction E with
| nil => simp [Sigma_Solved]
| cons eq E ih =>

  rcases eq with ⟨s,t⟩
  have varx : ∃ x, s = Term.var x := solved.left s t (by simp)
  rcases varx with ⟨x,hx⟩

  intro y hy
  simp [Sigma_Solved, hx] at hy

  by_cases eq_yx : y = x

  · simp_all
  · have y_in_dom : y ∈ (Sigma_Solved E).domain := by simp_all

    have hsolved : Solved_Form E := by
      rcases solved with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · intro s t eqE
        exact h₁ s t (by simp [eqE])
      · intro x' t₁ t₂ ht₁ ht₂
        exact h₂ x' t₁ t₂ (by simp [ht₁]) (by simp [ht₂])
      · intro x' t eqE
        exact h₃ x' t (by simp [eqE])

    have y_in_fV : y ∈ EqualityProblem.freeVars ((s,t) :: E) := by
      have hy_in_fV : y ∈ EqualityProblem.freeVars E := ih hsolved y_in_dom
      simp [hy_in_fV]

    exact y_in_fV

lemma Solved_Codom_Subset_fV {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
(E : EqualityProblem sig X) (solved: Solved_Form E) : (Sigma_Solved E).codomain ⊆ E.freeVars := by

induction E with
| nil => simp [Sigma_Solved]
| cons eq E ih =>

  rcases eq with ⟨s,t⟩
  have varx : ∃ x, s = Term.var x := solved.left s t (by simp)
  rcases varx with ⟨x,hx⟩

  intro y hy
  simp [Sigma_Solved, hx] at hy

  by_cases eq_yx : y = x

  · simp_all
  · have y_in_dom : y ∈ (Sigma_Solved E).codomain := sorry

    have hsolved : Solved_Form E := by
      rcases solved with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · intro s t eqE
        exact h₁ s t (by simp [eqE])
      · intro x' t₁ t₂ ht₁ ht₂
        exact h₂ x' t₁ t₂ (by simp [ht₁]) (by simp [ht₂])
      · intro x' t eqE
        exact h₃ x' t (by simp [eqE])

    have y_in_fV : y ∈ EqualityProblem.freeVars ((s,t) :: E) := by
      have hy_in_fV : y ∈ EqualityProblem.freeVars E := ih hsolved y_in_dom
      simp [hy_in_fV]

    exact y_in_fV

lemma do_codom_subset_E {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X) (σ σ' : Substitution sig X)
(algo : Naive_Standard_Unification_Rec E initSubst = some σ') : σ'.domain ∪ σ'.codomain ⊆ E.freeVars := by sorry


---------------------------------------------------------
--Unifiable E ↔ ∃ σ : Substitution sig X, Idempotent σ
---------------------------------------------------------

lemma σ_solved_dom_codom_disj {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] (E : EqualityProblem sig X) (solved : Solved_Form E) :
(Sigma_Solved E).domain ∩ (Sigma_Solved E).codomain = ∅ := by
sorry

lemma new_idempotent {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs]
(E : EqualityProblem sig X) (solved : Solved_Form E) : Idempotent (Sigma_Solved E) := by
apply (idempotent_iff_inter_empty (σ := Sigma_Solved E)).mpr
exact σ_solved_dom_codom_disj E solved

------------------------------------------
-- Main Unfication Theorem --
------------------------------------------

theorem unifiable_iff_mgu_idempot {sig : Signature} {X : Variables} [DecidableEq X] [BEq sig.funs] [BEq (Equality sig X)] [LawfulBEq (Equality sig X)]
(E : EqualityProblem sig X) : Unifiable E ↔ ∃ σ : Substitution sig X, MostGeneralUnifier E σ ∧ Idempotent σ ∧ σ.domain ∪ σ.codomain ⊆ E.freeVars := by

  constructor

  · intro hunif
    rcases hunif with ⟨σ, hσ⟩
    cases halgo' : Naive_Standard_Unification_Rec E initSubst with

    | none =>
       have nnot := uneq_none E σ (hσ := ⟨σ,hσ⟩)
       exact (nnot halgo').elim

    | some σ_out =>
      obtain ⟨hE', hE'_solved, σ_solved⟩ := Ex_SolvedForm_Sigma E σ_out halgo'
      subst σ_solved

      have mgu_he' : MostGeneralUnifier hE' (Sigma_Solved hE') := Most_General_Sigma_Solved hE' hE'_solved
      have heq_τ : ∀ τ, Unifier E τ ↔ Unifier hE' τ := sorry
      have hmgu : MostGeneralUnifier E (Sigma_Solved hE') := sorry

      have hidempotent : Idempotent (Sigma_Solved hE') := new_idempotent hE' hE'_solved

      have dom_codom_fV : ((Sigma_Solved hE').domain ∪ (Sigma_Solved hE').codomain) ⊆ E.freeVars := sorry

      exact ⟨Sigma_Solved hE', hmgu, hidempotent, dom_codom_fV⟩

  · intro h
    obtain ⟨σ, ⟨⟨⟩⟩⟩ := h
    use σ

alias main_unification_theorem := unifiable_iff_mgu_idempot
