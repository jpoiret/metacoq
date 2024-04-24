From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
(* From MetaCoq.Translations Require Import translation_utils. *)

Import MCMonadNotation.

Record TransKit : Type :=
  { ctx : Type;
    ty : Type;
    tm : Type;
    emp_ctx : ctx;
    ext_ctx : ctx -> ty -> ctx;
    pop_ctx : ctx -> ctx;
    var_tm : ctx -> tm;
    wk_tm : ctx -> tm -> tm;
    el : ctx -> tm -> ty;
    sort_tsl : ctx -> sort -> tm;
    prod_tsl : ctx -> aname -> tm -> tm -> tm;
    app_tsl : ctx -> tm -> tm -> tm;
    lambda_tsl : ctx -> aname -> tm -> tm -> tm
  }.

Arguments emp_ctx {_}.
Arguments ext_ctx {_}.
Arguments pop_ctx {_}.
Arguments var_tm {_}.
Arguments wk_tm {_}.
Arguments el {_}.
Arguments sort_tsl {_}.
Arguments prod_tsl {_}.
Arguments app_tsl {_}.
Arguments lambda_tsl {_}.

Axiom todo : forall {A : Type}, forall s : string, A.

Fixpoint tsl_rel {k : TransKit} (Γ : ctx k) (n : nat) : tm k :=
  match n with
    | 0 => var_tm Γ
    | S n => let popped := pop_ctx Γ in wk_tm popped (tsl_rel popped n)
    end.

Fixpoint tsl_kit_tm {k : TransKit} (Γ : ctx k) (t : term) {struct t} : tm k :=
  match t with
    | tRel n => tsl_rel Γ n
    | tSort s => sort_tsl Γ s
    | tProd a A B => let A' := tsl_kit_tm Γ A in prod_tsl Γ a A' (tsl_kit_tm (ext_ctx Γ (el Γ A')) B)
    | tApp f l => List.fold_left (fun t a => app_tsl Γ t (tsl_kit_tm Γ a)) l (tsl_kit_tm Γ f)
    | tLambda b A t => let A' := tsl_kit_tm Γ A in lambda_tsl Γ b A' (tsl_kit_tm (ext_ctx Γ (el Γ A')) t)
    | _ => todo "oops"
    end.

Definition paramBinder n :=
  {| binder_name := match n.(binder_name) with
       | nAnon => nAnon
       | nNamed n => nNamed (n ^ "ᵖ")
       end;
     binder_relevance := n.(binder_relevance) |}.

Definition relAnon := {| binder_name := nAnon ; binder_relevance := Relevant |}.
Definition relNamed (n : ident) := {| binder_name := nNamed n ; binder_relevance := Relevant |}.


Fixpoint double_context_up_to (n : nat) (t : term) : term :=
  match t with
  | tRel k => if Nat.leb n k then tRel (1 + (2 * (k - n)) + n) else t
  | tProd a A B => tProd a (double_context_up_to n A) (double_context_up_to (1+n) B)
  | tApp f l => tApp (double_context_up_to n f) (List.map (double_context_up_to n) l)
  | tLambda b A t => tLambda b (double_context_up_to n A) (double_context_up_to (1+n) t)
  | _ => t
  end.

Definition param_kit : TransKit
 :=
 {| ctx := list term;
    ty := term × term;
    tm := term × term;
    emp_ctx := [];
    ext_ctx := (fun Γ '(T , Tparam) => Γ ,, (double_context_up_to 0 T) ,, tApp (lift0 1 Tparam) [tRel 0]);
    pop_ctx Γ := match Γ with
      | [] => []
      | [a] => []
      | _ :: _ :: Γ => Γ
      end;
    var_tm Γ := (tRel 0, tRel 0);
    wk_tm Γ '(a , b) := (lift0 1 a,lift0 2 b);
    el Γ '(a , b) := (a , b);
    sort_tsl Γ s := let u := tSort s in (u , tLambda (relNamed "A") u (tProd relAnon (tRel 0) (tSort s)));

    prod_tsl Γ a '(A , Aparam) '(B , Bparam) :=
    let A' := double_context_up_to 0 A in
    let B' := double_context_up_to 1 B in
    (tProd a A B , tLambda (relNamed "f") (tProd a A' B') (tProd a (lift0 1 A') (tProd (paramBinder a) (tApp (lift0 2 Aparam) [tRel 0]) (tApp (lift 1 2 Bparam) [tApp (tRel 2) [tRel 1]]))));

    app_tsl Γ '(f , fparam) '(a , aparam) :=
    (tApp f [a] , tApp fparam [(double_context_up_to 0 a) ; aparam]);

    lambda_tsl Γ b '(A , Aparam) '(t , tparam) :=
    let u := tLambda b A t in
    let A' := double_context_up_to 0 A in
    (u , tLambda b A' (tLambda (paramBinder b) (tApp (lift0 1 Aparam) [tRel 0]) tparam))|}.

Definition test := fun (A B : Type) (f : A -> B) (a : A) => f a.

MetaCoq Run (tm <- (tmEval all test >>= tmQuote) ;;
             let '(u , v) := (tsl_kit_tm (k := param_kit) [] tm) in
             (* tmEval all v >>= tmPrint ;; *)
             unq <- tmUnquote v ;;
             tmEval all unq.(my_projT2) >>= tmPrint).
