module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

public section

namespace Cslib

universe u

variable {Var : Type u}


namespace LambdaCalculus.LocallyNameless.Untyped.Term

attribute [grind =] Finset.union_singleton

inductive SN {α} : Term α → Prop
| sn t : (∀ t', (t ⭢βᶠ t') → SN t') → SN t

@[aesop safe]
lemma sn_step {t t' : Term Var} (t_st_t' : t ⭢βᶠ t') (sn_t : SN t) : SN t' := by
  cases sn_t; grind

lemma sn_fvar {x : Var} : SN (Term.fvar x) := by
  constructor
  intro t' hstep
  cases hstep

lemma sn_app (t s : Term Var) :
  SN t →
  SN s →
  (∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN (t' ^ s')) →
  SN (t.app s) := by
  intro h_sn_t h_sn_s hβ
  induction h_sn_t generalizing s with | sn t ht ih_t =>
  induction h_sn_s with | sn s hs ih_s =>
  constructor
  intro u hstep
  cases hstep with
  | beta _ _ => apply hβ <;> rfl
  | appL _ h_s_red =>
    apply ih_s _ h_s_red
    intro t' s'' hstep1 hstep2
    exact hβ hstep1 (Relation.ReflTransGen.head h_s_red hstep2)
  | appR _ h_t_red =>
    apply ih_t _ h_t_red _ (SN.sn s hs)
    intro t' s' hstep1 hstep2
    exact hβ (Relation.ReflTransGen.head h_t_red hstep1) hstep2



lemma sn_app_left (M N : Term Var) : Term.LC N → SN (M.app N) → SN M := by
  intro lc_N h_sn
  generalize Heq : M.app N = P
  rw[Heq] at h_sn
  revert M N
  induction h_sn
  · case sn P h_sn ih =>
    intro M N lc_N Heq
    rw[←Heq] at ih
    constructor
    intro M' h_step
    apply ih (M'.app N)
    apply Term.FullBeta.appR <;> assumption
    · apply lc_N
    · rfl

@[aesop safe constructors]
inductive neutral : Term Var → Prop
| bvar : ∀ n, neutral (Term.bvar n)
| fvar : ∀ x, neutral (Term.fvar x)
| app : ∀ t1 t2, neutral t1 → SN t2 → neutral (Term.app t1 t2)

@[aesop safe]
lemma neutral_step {t : Term Var} :
  neutral t → ∀ t', t ⭢βᶠ t' → neutral t' := by
  intro Hneut
  induction Hneut <;> intro t' step
  · case bvar n =>
      cases step
  · case fvar x =>
      cases step
  · case app IH Hneut =>
      cases step <;> try aesop
      · contradiction

@[aesop safe]
lemma neutral_mst {t t' : Term Var} :
  neutral t → t ↠βᶠ t' → neutral t' := by
  intro Hneut h_red
  induction h_red <;> aesop

lemma neutral_sn {t : Term Var} (Hneut : neutral t) : SN t := by
  induction Hneut
  · case bvar n => constructor; intro t' hstep; cases hstep
  · case fvar x => constructor; intro t' hstep; cases hstep
  · case app t1 t'_neut t1_sn t1'_sn =>
      apply sn_app <;> try assumption
      intro t1' t2' hstep1 hstep2
      have H_neut := neutral_mst t'_neut hstep1
      contradiction
def multi_app (f : Term Var) (args : List (Term Var)) :=
  match args with
  | []      => f
  | a :: as => Term.app (multi_app f as) a

lemma abs_sn : ∀ {M N : Term Var},
  SN (M ^ N)  → SN (Term.abs M) := by
  intro M N sn_M
  generalize h : (M ^ N) = M_open at sn_M
  revert N M
  induction sn_M with
  | sn M_open h_sn ih =>
      intro M N h
      constructor
      intro M' h_step
      cases h_step with
      | @abs h_M_red M' L H =>
        specialize ih (M' ^ N)
        rw[←h] at ih
        apply ih
        · sorry -- True, maybe lc issue
        · rfl

lemma step_open : ∀ {M M' N : Term Var},
  --LC N →
  M ⭢βᶠ M' →
  (M ^ N) ⭢βᶠ (M' ^ N) := by
  intros M M' lc_n h_step
  induction h_step with
  | beta abs_lc n_lc => sorry
  | appL lc_z st ih =>
    apply FullBeta.appL
    · sorry
    · assumption
  | appR lc_z st ih =>
    apply FullBeta.appR
    · sorry
    · assumption
  | abs L st ih => sorry

/-
lemma open_sn : ∀ {M N : Term Var},
  SN (M ^ N) →
  SN M := by
  intro M N sn_M
  generalize h : M ^ N = M_open at sn_M
  revert M N
  induction sn_M with
  | sn M_open h_sn ih =>
      intro M N h
      constructor
      intro M' h_step
      apply ih (M' ^ N)
      · rw[←h] at *
        apply step_open
        apply h_step
      · rfl
-/

lemma multi_app_sn : ∀ {l} {t s : Term Var},
  SN s →
  SN (multi_app (t ^ s) l) →
  -------------------------------------
  SN (multi_app ((Term.abs t).app s) l) := by
  intro l
  induction l <;> intros t s sn_s tu_sn
  · case nil =>
      rw[multi_app]
      rw[multi_app] at tu_sn
      apply sn_app <;> try assumption
      · apply (abs_sn tu_sn)
      · intro t' s' hstep1 hstep2
        sorry
  · case cons a l ih =>
      rw[multi_app]
      apply sn_app
      · apply ih
        · assumption
        · sorry
      sorry
      sorry
