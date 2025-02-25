(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Environment Transform config BasicAst uGraph.
From MetaCoq.Template Require Pretty Typing WcbvEval EtaExpand.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram PCUICWeakeningEnvSN.
Set Warnings "+notation-overridden".
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl.
From MetaCoq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness Extract
   EOptimizePropDiscr ERemoveParams EProgram.
From MetaCoq.TemplatePCUIC Require Import PCUICTransform.

Import PCUICAst (term) PCUICProgram PCUICTransform (eval_pcuic_program) Extract EProgram
    EAst Transform ERemoveParams.
Import EEnvMap EGlobalEnv EWellformed.

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env_map) (wfΣ : ∥ PCUICTyping.wf Σ ∥) : wf_env :=
  {| wf_env_referenced := {| referenced_impl_env := Σ.(trans_env_env); referenced_impl_wf := wfΣ |} ;
     wf_env_map := Σ.(trans_env_map);
     wf_env_map_repr := Σ.(trans_env_repr);
 |}.


Notation NormalisationIn_erase_pcuic_program_1 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p.1 -> PCUICSN.NormalisationIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p.1)
       (only parsing).

Notation NormalisationIn_erase_pcuic_program_2 p
  := (@PCUICTyping.wf_ext config.extraction_checker_flags p.1 -> PCUICWeakeningEnvSN.NormalisationInAdjustUniversesIn (cf:=config.extraction_checker_flags) (no:=PCUICSN.extraction_normalizing) p.1)
       (only parsing).

(* TODO: Where should this go? *)
#[local]
Lemma referenced_impl_env_iter_pop_eq'
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  (wfe' := ErasureFunction.iter referenced_pop (S n) (referenced_impl_env wfe))
  : referenced_impl_env X' = wfe'.
Proof.
  subst X' wfe'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local]
Lemma referenced_impl_env_iter_pop_eq
  (cf := config.extraction_checker_flags)
  (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl}
  (wfe : wf_env)
  (n : nat)
  (X' := ErasureFunction.iter abstract_pop_decls (S n) wfe)
  : referenced_impl_env X'
    = {| PCUICAst.PCUICEnvironment.universes := PCUICAst.PCUICEnvironment.universes (referenced_impl_env wfe)
      ; PCUICAst.PCUICEnvironment.declarations := skipn (S n) (PCUICAst.PCUICEnvironment.declarations (referenced_impl_env wfe))
      ; PCUICAst.PCUICEnvironment.retroknowledge := PCUICAst.PCUICEnvironment.retroknowledge (referenced_impl_env wfe) |}.
Proof.
  subst X'.
  revert wfe; cbn; induction n as [|n IHn]; cbn; intros;
    [ | rewrite IHn ].
  all: destruct wfe as [[[? [|[]]]]]; cbv [optim_pop]; cbn; reflexivity.
Qed.

#[local] Lemma erase_pcuic_program_normalisation_helper
  (cf := config.extraction_checker_flags) (no := PCUICSN.extraction_normalizing)
  {guard : abstract_guard_impl} (p : pcuic_program)
  {normalisation_in : NormalisationIn_erase_pcuic_program_1 p}
  {normalisation_in_adjust_universes : NormalisationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  : (let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)) in
     forall n : nat,
       n < #|PCUICAst.PCUICEnvironment.declarations p.1|
      -> forall kn cb pf,
        hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
          Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
        forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
          PCUICTyping.wf_ext Σ ->
          Σ
            ∼_ext @abstract_make_wf_env_ext extraction_checker_flags
            (@optimized_abstract_env_impl extraction_checker_flags _) wfe
            (PCUICAst.PCUICEnvironment.cst_universes cb) pf -> PCUICSN.NormalisationIn Σ)
    /\
      (let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)) in
       forall n : nat,
         n < #|PCUICAst.PCUICEnvironment.declarations p.1|
        -> let X' :=
             ErasureFunction.iter abstract_pop_decls (S n) wfe in
           forall kn cb pf,
             hd_error (skipn n (PCUICAst.PCUICEnvironment.declarations p.1)) =
               Some (kn, PCUICAst.PCUICEnvironment.ConstantDecl cb) ->
             let Xext :=
               @abstract_make_wf_env_ext extraction_checker_flags
                 (@optimized_abstract_env_impl extraction_checker_flags _) X'
                 (PCUICAst.PCUICEnvironment.cst_universes cb) pf in
             forall Σ : PCUICAst.PCUICEnvironment.global_env_ext,
               PCUICTyping.wf_ext Σ -> Σ ∼_ext Xext -> PCUICSN.NormalisationIn Σ).
Proof.
  match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
  cbv beta zeta; split.
  all: cbn; intros; subst;
    repeat match goal with
      | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
      | [ H : squash _ |- _ ] => destruct H
      | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
      end.
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalisationIn _ |- _ => revert H end.
    eapply normalisation_in_adjust_universes; try assumption.
    cbv [PCUICSN.NormalisationIn]; cbn.
    let H := match goal with H : PCUICTyping.wf_ext _ |- _ => H end in
    rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
    [ eapply PCUICAst.NoDup_on_global_decls, H
    | eexists; eassumption ]. }
  { destruct p as [Σ ?]; cbn in *.
    match goal with H : PCUICSN.NormalisationIn _ |- _ => revert H end.
    move => normalisation_in.
    rewrite referenced_impl_env_iter_pop_eq.
    repeat match goal with H : _ |- _ => rewrite referenced_impl_env_iter_pop_eq in H end.
    eapply normalisation_in_adjust_universes in normalisation_in; eauto; revgoals.
    { repeat match goal with H : PCUICTyping.wf_ext _ |- _ => destruct H end;
        split; eassumption. }
    { let H := multimatch goal with H : PCUICTyping.wf_ext _ |- _ => H end in
      rewrite /PCUICAst.PCUICEnvironment.lookup_env -PCUICAst.PCUICEnvironment.lookup_global_Some_iff_In_NoDup -?hd_error_skipn_iff_In;
      [ eapply PCUICAst.NoDup_on_global_decls, H
      | eexists; eassumption ]. }
    revert normalisation_in.
    apply PCUICWeakeningEnvSN.weakening_env_normalisation_in; eauto;
      try match goal with H : PCUICTyping.wf_ext _ |- _ => refine (@PCUICTyping.wf_ext_wf _ _ H) end.
    apply PCUICAst.PCUICEnvironment.extends_decls_extends, PCUICAst.PCUICEnvironment.strictly_extends_decls_extends_decls; split; cbn; try reflexivity.
    eauto using firstn_skipn. }
Qed.

Program Definition erase_pcuic_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalisation_in : NormalisationIn_erase_pcuic_program_1 p}
  {normalisation_in_adjust_universes : NormalisationIn_erase_pcuic_program_2 p}
  (wfΣ : ∥ PCUICTyping.wf_ext (H := config.extraction_checker_flags) p.1 ∥)
  (wt : ∥ ∑ T, PCUICTyping.typing (H := config.extraction_checker_flags) p.1 [] p.2 T ∥) : eprogram_env :=
  let wfe := build_wf_env_from_env p.1.1 (map_squash (PCUICTyping.wf_ext_wf _) wfΣ) in
  let wfext := @abstract_make_wf_env_ext _ optimized_abstract_env_impl wfe p.1.2 _ in
  let t := ErasureFunction.erase (normalisation_in:=_) optimized_abstract_env_impl wfext nil p.2
    (fun Σ wfΣ => let '(sq (T; ty)) := wt in PCUICTyping.iswelltyped ty) in
  let Σ' := ErasureFunction.erase_global_fast (normalisation_in:=_) optimized_abstract_env_impl
    (EAstUtils.term_global_deps t) wfe (p.1.(PCUICAst.PCUICEnvironment.declarations)) _ in
    (EEnvMap.GlobalContextMap.make Σ' _, t).

Next Obligation. unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto. Qed.
Next Obligation.
  eapply wf_glob_fresh.
  eapply ErasureFunction.erase_global_fast_wf_glob.
  unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto.
Qed.

Obligation Tactic := idtac.

Import Extract.

Definition erase_program {guard : abstract_guard_impl} (p : pcuic_program)
  {normalisation_in normalisation_in_adjust_universes}
  (wtp : ∥ wt_pcuic_program (cf:=config.extraction_checker_flags) p ∥)
  : eprogram_env :=
  @erase_pcuic_program guard p normalisation_in normalisation_in_adjust_universes (map_squash fst wtp) (map_squash snd wtp).

Lemma expanded_erase_program {guard : abstract_guard_impl} p {normalisation_in normalisation_in_adjust_universes} (wtp : ∥ wt_pcuic_program p ∥) :
  PCUICEtaExpand.expanded_pcuic_program p ->
  EEtaExpandedFix.expanded_eprogram_env (@erase_program guard p normalisation_in normalisation_in_adjust_universes wtp).
Proof.
  intros [etaenv etat]. split;
  unfold erase_program, erase_pcuic_program.
  eapply ErasureFunction.expanded_erase_global_fast, etaenv; try reflexivity; eauto.
  unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto.
  apply: (ErasureFunction.expanded_erase_fast (X_type:=optimized_abstract_env_impl)).
  unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto.
  reflexivity. exact etat.
Qed.

Lemma expanded_eprogram_env_expanded_eprogram_cstrs p :
  EEtaExpandedFix.expanded_eprogram_env p ->
  EEtaExpanded.expanded_eprogram_env_cstrs p.
Proof.
  move=> [] etaenv etat.
  apply /andP.
  split.
  - eapply EEtaExpanded.isEtaExpFix_env_isEtaExp_env. now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  - eapply EEtaExpanded.isEtaExpFix_isEtaExp. now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Obligation Tactic := try solve [ eauto ].

Program Definition erase_transform {guard : abstract_guard_impl} : Transform.t pcuic_program eprogram_env PCUICAst.term EAst.term
  eval_pcuic_program (eval_eprogram_env EWcbvEval.default_wcbv_flags) :=
 {| name := "erasure";
    pre p :=
     ∥ wt_pcuic_program (cf := config.extraction_checker_flags) p ∥
     /\ PCUICEtaExpand.expanded_pcuic_program p
     /\ NormalisationIn_erase_pcuic_program_1 p
     /\ NormalisationIn_erase_pcuic_program_2 p ;
   transform p hp := let nhs := proj2 (proj2 hp) in
                     @erase_program guard p (proj1 nhs) (proj2 nhs) (proj1 hp) ;
    post p := [/\ wf_eprogram_env all_env_flags p & EEtaExpandedFix.expanded_eprogram_env p];
   obseq g g' v v' := let Σ := g.1 in Σ ;;; [] |- v ⇝ℇ v' |}.

Next Obligation.
  cbn -[erase_program].
  intros ? p (wtp&etap&?&?).
  destruct erase_program eqn:e.
  split.
  - unfold erase_program, erase_pcuic_program in e.
    set (egf := ErasureFunction.erase_global_fast _ _ _ _ _) in e.
    set (ef := ErasureFunction.erase _ _ _ _ _) in e.
    cbn -[egf ef] in e. injection e. intros <- <-.
    split.
    eapply ErasureFunction.erase_global_fast_wf_glob; eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto.
    apply: (ErasureFunction.erase_wellformed_fast (X_type:=optimized_abstract_env_impl)); eauto;
      try match goal with H : _ |- _ => eapply H end.
    unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; eauto.
  - rewrite -e. cbn.
    now eapply expanded_erase_program.
Qed.

Next Obligation.
  red. move=> guard p v [[wf [T [HT1 HT2]]]]. unfold eval_pcuic_program, eval_eprogram.
  unshelve edestruct erase_pcuic_program_normalisation_helper; cbn in *; try now destruct wf; eauto.
  destruct p as [Σ t].
  intros [ev].
  destruct erase_program eqn:e.
  unfold erase_program, erase_pcuic_program in e. simpl in e. injection e; intros <- <-.
  simpl. clear e. cbn in *.
  destruct wf; cbn in *.
  set (Σ' := build_wf_env_from_env _ _).
  assert (ev' :forall Σ0 : PCUICAst.PCUICEnvironment.global_env, Σ0 = Σ' -> PCUICWcbvEval.eval Σ0 t v).
  { intros; now subst. }
  eapply (ErasureFunction.erase_correct optimized_abstract_env_impl Σ' Σ.2 _ _ _ _ _ (EAstUtils.term_global_deps _)) in ev'.
  4:{ erewrite <- ErasureFunction.erase_global_deps_fast_spec. reflexivity. }
  all:trea.
  2:eapply Kernames.KernameSet.subset_spec; reflexivity.
  destruct ev' as [v' [he [hev]]]. exists v'; split => //.
  red. cbn.
  sq. exact hev. Unshelve.
  { intros; cbn in *.
    subst Σ'.
    multimatch goal with
    | [ H : _ |- _ ] => eapply H
    end; try eassumption;
    rewrite referenced_impl_env_iter_pop_eq;
    repeat match goal with H : _ |- _ => rewrite referenced_impl_env_iter_pop_eq in H end;
    assumption. }
  cbn; intros. sq. now subst.
Qed.

Obligation Tactic := idtac.

(** This transformation is the identity on terms but changes the evaluation relation to one
    where fixpoints are not guarded. It requires eta-expanded fixpoints and evaluation
    to use the guarded fixpoint rule as a precondition. *)

Import EWcbvEval (WcbvFlags, with_prop_case, with_guarded_fix).

Program Definition guarded_to_unguarded_fix {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} {efl : EEnvFlags} (wguard : with_guarded_fix) :
  Transform.t eprogram_env eprogram_env EAst.term EAst.term
    (eval_eprogram_env fl) (eval_eprogram_env (EWcbvEval.switch_unguarded_fix fl)) :=
  {| name := "switching to unguarded fixpoints";
    transform p pre := p;
    pre p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    post p := wf_eprogram_env efl p /\ EEtaExpandedFix.expanded_eprogram_env p;
    obseq g g' v v' := v' = v |}.
Next Obligation. cbn. eauto. Qed.
Next Obligation.
  cbn.
  move=> fl wcon efl wguard [Σ t] v [wfp [etae etat]]. cbn in *.
  intros [ev]. exists v. split => //.
  red. sq. cbn in *.
  unshelve eapply EEtaExpandedFix.eval_opt_to_target => //. auto. 2:apply wfp.
  now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
  now eapply EEtaExpandedFix.expanded_isEtaExp.
Qed.

Definition rebuild_wf_env {efl} (p : eprogram) (hwf : wf_eprogram efl p): eprogram_env :=
  (GlobalContextMap.make p.1 (wf_glob_fresh p.1 (proj1 hwf)), p.2).

Program Definition rebuild_wf_env_transform {fl : EWcbvEval.WcbvFlags} {efl} (with_exp : bool) :
  Transform.t eprogram eprogram_env EAst.term EAst.term (eval_eprogram fl) (eval_eprogram_env fl) :=
  {| name := "rebuilding environment lookup table";
     pre p := wf_eprogram efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_cstrs p);
     transform p pre := rebuild_wf_env p (proj1 pre);
     post p := wf_eprogram_env efl p /\ (with_exp ==> EEtaExpanded.expanded_eprogram_env_cstrs p);
     obseq g g' v v' := v = v' |}.
Next Obligation.
  cbn. intros fl efl [] input [wf exp]; cbn; split => //.
Qed.
Next Obligation.
  cbn. intros fl efl [] input v [] ev p'; exists v; split => //.
Qed.

Program Definition remove_params_optimization {fl : EWcbvEval.WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags):
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters";
    transform p pre := ERemoveParams.strip_program p;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  split. now eapply ERemoveParams.strip_program_wf.
  now eapply ERemoveParams.strip_program_expanded.
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //. now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Program Definition remove_params_fast_optimization (fl : EWcbvEval.WcbvFlags) {wcon : EWcbvEval.with_constructor_as_block = false}
  (efl := all_env_flags) :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "stripping constructor parameters (faster?)";
    transform p _ := (ERemoveParams.Fast.strip_env p.1, ERemoveParams.Fast.strip p.1 [] p.2);
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_no_params efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = (ERemoveParams.strip g.1 v) |}.
Next Obligation.
  move=> fl wcon efl [Σ t] [wfp etap].
  simpl.
  cbn -[ERemoveParams.strip] in *.
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  split.
  now eapply (ERemoveParams.strip_program_wf (Σ, t)).
  now eapply (ERemoveParams.strip_program_expanded (Σ, t)).
Qed.

Next Obligation.
  red. move=> ? wcon [Σ t] /= v [[wfe wft] etap] [ev].
  rewrite -ERemoveParams.Fast.strip_fast -ERemoveParams.Fast.strip_env_fast.
  unshelve eapply ERemoveParams.strip_eval in ev; eauto.
  eexists; split => /= //.
  now sq. cbn in *.
  now move/andP: etap.
  now eapply wellformed_closed_env.
  now eapply wellformed_closed.
  now move/andP: etap.
Qed.

Import EOptimizePropDiscr EWcbvEval.

Program Definition optimize_prop_discr_optimization {fl : WcbvFlags} {wcon : with_constructor_as_block = false} {efl : EEnvFlags} {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram (disable_prop_cases fl)) :=
  {| name := "optimize_prop_discr";
    transform p _ := optimize_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram efl p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = EOptimizePropDiscr.optimize g.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon efl hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EOptimizePropDiscr.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  eapply wellformed_closed_env, wfe.
  eapply wellformed_closed, wfe.
  Unshelve. eauto.
Qed.

From MetaCoq.Erasure Require Import EInlineProjections.

Program Definition inline_projections_optimization {fl : WcbvFlags} {wcon : EWcbvEval.with_constructor_as_block = false} (efl := switch_no_params all_env_flags)
  {hastrel : has_tRel} {hastbox : has_tBox} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env fl) (eval_eprogram fl) :=
  {| name := "primitive projection inlining";
    transform p _ := EInlineProjections.optimize_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (disable_projections_env_flag efl) p /\ EEtaExpanded.expanded_eprogram_cstrs p;
    obseq g g' v v' := v' = EInlineProjections.optimize g.1 v |}.

Next Obligation.
  move=> fl wcon efl hastrel hastbox [Σ t] [wfp etap].
  cbn in *. split.
  - now eapply optimize_program_wf.
  - now eapply optimize_program_expanded.
Qed.
Next Obligation.
  red. move=> fl wcon hastrel hastbox [Σ t] /= v [wfe wft] [ev].
  eapply EInlineProjections.optimize_correct in ev; eauto.
  eexists; split => //. red. sq; auto. cbn. apply wfe.
  cbn. eapply wfe. Unshelve. auto.
Qed.

From MetaCoq.Erasure Require Import EConstructorsAsBlocks.

Program Definition constructors_as_blocks_transformation (efl : EEnvFlags)
  {has_app : has_tApp} {has_pars : has_cstr_params = false} {has_cstrblocks : cstr_as_blocks = false} :
  Transform.t eprogram_env eprogram EAst.term EAst.term (eval_eprogram_env target_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "transforming to constuctors as blocks";
    transform p _ := EConstructorsAsBlocks.transform_blocks_program p ;
    pre p := wf_eprogram_env efl p /\ EEtaExpanded.expanded_eprogram_env_cstrs p;
    post p := wf_eprogram (switch_cstr_as_blocks efl) p ;
    obseq g g' v v' := v' = EConstructorsAsBlocks.transform_blocks g.1 v |}.

Next Obligation.
  move=> efl hasapp haspars hascstrs [Σ t] [] [wftp wft] /andP [etap etat].
  cbn in *. split.
  - eapply transform_wf_global; eauto.
  - eapply transform_wellformed; eauto.
Qed.
Next Obligation.
  red. move=> efl hasapp haspars hascstrs [Σ t] /= v [[wfe1 wfe2] wft] [ev].
  eexists. split; [ | eauto].
  unfold EEtaExpanded.expanded_eprogram_env_cstrs in *.
  revert wft. move => /andP // [e1 e2].
  econstructor.
  cbn -[transform_blocks].
  eapply transform_blocks_eval; cbn; eauto.
Qed.
