import Cslib.Foundations.Data.Relation
import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm

namespace Cslib

universe u v

namespace LambdaCalculus.LocallyNameless.Stlc

open Untyped Typing LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {Base : Type v} [DecidableEq Var] [HasFresh Var]

open LambdaCalculus.LocallyNameless.Stlc
open scoped Term





def fv (Ns : Context Var (Term Var)) : Finset Var :=
  match Ns with
  | [] => {}
  | ⟨ _, sub ⟩ :: Ns' => sub.fv ∪ fv Ns'

def multi_subst (σ : Context Var (Term Var)) (M : Term Var) : Term Var :=
  match σ with
  | [] => M
  | ⟨ i, sub ⟩ :: σ' => (multi_subst σ' M) [ i := sub ]

def multi_subst_fvar_fresh (Ns : Context Var (Term Var)) :
  ∀ x ∉ Ns.dom, multi_subst Ns (Term.fvar x) = Term.fvar x := by
  induction Ns <;> intro x h_fresh
  · case nil =>
      simp [multi_subst]
  · case cons N Ns ih =>
      simp only [multi_subst]
      simp only [Context.dom] at h_fresh
      rw[ih]
      · rw[subst_fvar]
        by_cases h : N.1 = x <;> simp_all
      · simp_all

lemma multi_subst_preserves_not_fvar {x : Var}
  (M : Term Var)
  (Ns : Context Var (Term Var))
  (nmem : x ∉ M.fv ∪ fv Ns) :
  x ∉ (multi_subst Ns M).fv := by
  induction Ns
  · case nil =>
      rw[multi_subst]
      simp_all
  · case cons N Ns ih =>
      rw[multi_subst]
      apply subst_preserve_not_fvar
      rw[fv] at nmem
      simp_all



def multi_subst_app (M N : Term Var) (Ps : Context Var (Term Var)) :
        multi_subst Ps (Term.app M N) = Term.app (multi_subst Ps M) (multi_subst Ps N) := by
  induction Ps
  · rfl
  · case cons N Ns ih => rw[multi_subst,multi_subst,ih]; rfl

def multi_subst_abs (M : Term Var) (Ns : Context Var (Term Var)) :
    multi_subst Ns (Term.abs M) =
    Term.abs (multi_subst Ns M) := by
  induction Ns
  · rfl
  · case cons N Ns ih => rw[multi_subst, ih]; rfl

lemma open'_fvar_subst (M N : Term Var) (x : Var) (H : x ∉ Term.fv M) :
  (i : Nat) → (M ⟦ i ↝ Term.fvar x ⟧) [x := N] = M ⟦ i ↝ N ⟧ := by
  induction M <;> intro i
  · case bvar j =>
      rw[Term.openRec_bvar, Term.openRec_bvar]
      by_cases h : i = j <;> simp[h, Term.subst_fvar, Term.subst_bvar]
  · case fvar y =>
      rw[Term.openRec_fvar, Term.openRec_fvar]
      simp only [Term.fv, Finset.mem_singleton] at H
      simp only [subst_fvar, ite_eq_right_iff]
      intro H
      contradiction
  · case abs M ih =>
      rw[Term.openRec_abs, Term.openRec_abs]
      rw[Term.subst_abs]
      rw[ih H]
  · case app l r ih_l ih_r =>
      rw[Term.openRec_app, Term.openRec_app]
      rw[Term.subst_app]
      simp only [Term.fv, Finset.mem_union, not_or] at H
      rw[ih_l H.1]
      rw[ih_r H.2]

lemma swap_subst_fresh (M N P : Term Var) (x y : Var) :
  (M [x := N]) [y := P] = (M [y := P]) [x := N] := by
  sorry


lemma multi_subst_open (M P : Term Var) (Ns : Context Var (Term Var)) (x : Var) :
  x ∉ M.fv ∪ fv Ns →
  (multi_subst Ns (M ^ (Term.fvar x))) [x := P] =
  (multi_subst Ns M) ^ P := by
  intro h_fresh
  induction Ns
  · unfold Term.open'
    rw[multi_subst, multi_subst, open'_fvar_subst]
    simp_all
  · case cons N Ns ih =>
      rw[multi_subst, multi_subst]
      rw[←swap_subst_fresh]
      rw[ih]
      rw[subst_open]
      sorry


def is_saturated (S : Set (Term Var)) : Prop :=
 (∀ M ∈ S, SN M) ∧
 (∀ M, neutral M → M ∈ S) ∧
 (∀ M N P, SN N → multi_app (M ^ N) P ∈ S → multi_app ((Term.abs M).app N) P ∈ S)

def semanticMap (τ : Ty Base) : Set (Term Var) :=
  match τ with
  | Ty.base _ => { t : Term Var | SN t }
  | Ty.arrow τ₁ τ₂ =>
    { t : Term Var | ∀ s : Term Var, s ∈ semanticMap τ₁ → (Term.app t s) ∈ semanticMap τ₂ }

def semanticMap_saturated (τ : Ty Base) :
    @is_saturated Var (semanticMap τ) := by
  induction τ
  · case base b =>
      constructor
      · intro M hM
        exact hM
      · constructor
        · intro M hneut
          apply neutral_sn
          assumption
        · intro M N P sn_N h_app
          apply multi_app_sn <;> assumption
  · case arrow τ₁ τ₂ ih₁ ih₂ =>
      constructor
      · intro M hM
        apply sn_app_left M (Term.fvar (fresh {}))
        · constructor
        · apply ih₂.1
          apply hM
          apply ih₁.2.1
          constructor
      · constructor
        · intro M hneut s hs
          apply ih₂.2.1
          apply neutral.app
          · assumption
          · apply ih₁.1
            exact hs
        · intro M N P sn_N h_app s hs
          apply ih₂.2.2 M N (s::P)
          · apply sn_N
          · apply h_app
            assumption





def entails_context (Ns : Context Var (Term Var)) (Γ : Context Var (Ty Base)) :=
  ∀ {x τ}, ⟨ x, τ ⟩ ∈ Γ → (multi_subst Ns (Term.fvar x)) ∈ semanticMap τ

lemma entails_context_empty {Γ : Context Var (Ty Base)} :
  entails_context [] Γ := by
  intro x τ h_mem
  rw[multi_subst]
  apply (semanticMap_saturated τ).2.1
  constructor


lemma entails_context_cons (Ns : Context Var (Term Var)) (Γ : Context Var (Ty Base))
  (x : Var) (τ : Ty Base) (sub : Term Var) :
  x ∉ Ns.dom ∪ fv Ns ∪ Γ.dom →
  sub ∈ semanticMap τ →
  entails_context Ns Γ → entails_context (⟨ x, sub ⟩ :: Ns) (⟨ x, τ ⟩ :: Γ) := by
  intro h_fresh h_mem h_entails y σ h_mem
  rw[multi_subst]
  rw[entails_context] at h_entails
  cases h_mem
  · case head =>
    rw[multi_subst_fvar_fresh]
    · rw[subst_fvar]
      simp_all
    · simp_all
  · case tail h_mem =>
    specialize (h_entails h_mem)
    rw [subst_fresh]
    · assumption
    · apply multi_subst_preserves_not_fvar
      apply List.mem_keys_of_mem at h_mem
      aesop




def entails (Γ : Context Var (Ty Base)) (t : Term Var) (τ : Ty Base) :=
  ∀ Ns, (entails_context Ns Γ) → (multi_subst Ns t) ∈ semanticMap τ




theorem soundness {Γ : Context Var (Ty Base)} {t : Term Var} {τ : Ty Base} :
  Γ ⊢ t ∶ τ → entails Γ t τ := by
  intro derivation_t
  induction derivation_t
  · case var Γ xσ_mem_Γ =>
      intro Ns hsat
      apply hsat xσ_mem_Γ
  · case' abs σ Γ t τ L IH derivation_t =>
      intro Ns hsat s hsat_s
      rw[multi_subst_abs]
      apply (semanticMap_saturated _).2.2 _ _ []
      · apply (semanticMap_saturated _).1
        assumption
      · rw[multi_app]
        set x := fresh (t.fv ∪ L ∪ Ns.dom ∪ fv Ns ∪ Context.dom Γ)
        have hfresh : x ∉ t.fv ∪ L ∪ Ns.dom ∪ fv Ns ∪ Context.dom Γ := by apply fresh_notMem
        have hfreshL : x ∉ L := by simp_all
        have H1 := derivation_t x hfreshL
        rw[entails] at H1
        specialize H1 (⟨x,s⟩ :: Ns)
        rw [multi_subst, multi_subst_open] at H1
        · apply H1
          apply entails_context_cons <;> simp_all
        · simp_all
  · case app derivation_t derivation_t' IH IH' =>
      intro Ns hsat
      rw[multi_subst_app]
      apply IH Ns hsat
      apply IH' Ns hsat

theorem strong_norm {Γ} {t : Term Var} {τ : Ty Base} (der : Γ ⊢ t ∶ τ) : SN t := by
  have H := soundness der
  specialize H [] entails_context_empty
  apply (semanticMap_saturated τ).1
  assumption

end LambdaCalculus.LocallyNameless.Stlc

end Cslib
