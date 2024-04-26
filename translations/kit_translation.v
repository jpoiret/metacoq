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
    var_tm : ctx -> nat -> tm;
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
Arguments el {_}.
Arguments sort_tsl {_}.
Arguments prod_tsl {_}.
Arguments app_tsl {_}.
Arguments lambda_tsl {_}.

Axiom todo : forall {A : Type}, forall s : string, A.

Fixpoint tsl_kit_tm {k : TransKit} (Γ : ctx k) (t : term) {struct t} : tm k :=
  match t with
    | tRel n => var_tm Γ n
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


(* (Unary) Parametricity translation *)
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
    var_tm Γ n := (tRel n, tRel (2 * n));
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

(* Prefascist translation *)

Definition Reader (I : Type) (A : Type) := I -> A.

#[export] Instance Reader_Instance (I : Type) : Monad (Reader I) :=
  {| ret _ a _ := a ;
     bind _ _ a f i := f (a i) i
  |}.

Definition ask {I : Type} : Reader I I := fun i => i.

Definition local {I J A : Type} (j : J) (r : Reader J A) : Reader I A := fun _ => r j.

Compute (u <- ask ;; local (2 + u) ask ;; ask) 2.

Class PreCat : Type :=
  { ob : Type ;
    mor : ob -> ob -> Type;
    id : forall (a : ob), mor a a;
    comp : forall {a b c : ob}, mor a b -> mor b c -> mor a c;
  }.

Notation "'force' α : q → p , A" := (forall (q : ob) (α : mor q p), A) (at level 80, α name, q name, p at next level, right associativity).

Record PPsh {ℂ : PreCat} (p : ob) : Type :=
  { T : force α : q → p, Type;
    R : (force α : q → p, T q α) -> SProp
  }.

MetaCoq Quote Definition ppsh_build := @Build_PPsh.

MetaCoq Quote Definition comp_term := @comp.
MetaCoq Quote Definition ob_term := @ob.
MetaCoq Quote Definition mor_term := @mor.
MetaCoq Quote Definition id_term := @id.

Section Prefascist.
  Context (ℂ_impl : term).

  (* Definition pushProd : prefascist_monad term -> prefascist_monad term
   *   := fun f '(init , p , β) =>
   *      tProd relAnon (tApp ob_term [ℂ_impl])
   *        (tProd relAnon (tApp mor_term [ℂ_impl; tRel 0; lift0 1 p])
   *          (f (lift0 2 init , tRel 1 , tApp comp_term [tRel 1; lift0 2 p; lift0 2 init; tRel 0; lift0 2 β]))).
   * 
   * Definition pushLam : prefascist_monad term -> prefascist_monad term
   *   := fun f '(init , p , β) =>
   *      tLambda relAnon (tApp ob_term [ℂ_impl])
   *        (tLambda relAnon (tApp mor_term [ℂ_impl; tRel 0; lift0 1 p])
   *          (f (lift0 2 init , tRel 1 , tApp comp_term [tRel 1; lift0 2 p; lift0 2 init; tRel 0; lift0 2 β]))). *)

  (* The state S represents the list of generated binders, with first term being
  its stage and the second being whether it is a forcing quantification *)
  Definition State := (list (term * bool) * term).

  (* b denotes whether the binding is a forcing quantification *)
  Definition push_binding '((vars , p) : State) (b : bool) : State :=
    (vars ,, (p , b) , if b then tRel 1 else lift0 2 p).

  Fixpoint lookup_var (n : nat) (l : list (term * bool)) : nat * term * term :=
    match n , l with
    | n , (p , true) :: l => let '(k , q , α) := lookup_var n l in
      (S (S k) , tRel 1 , tApp comp_term [lift0 2 ℂ_impl; tRel 1; lift0 2 q; lift0 2 p; tRel 0; lift0 2 α])
    | 0 , (p , false) :: l => (0 , lift0 2 p , tApp id_term [ℂ_impl; lift0 2 p])
    | S n , (p , false) :: l => let '(k , q , α) := lookup_var n l in
      (S (S k) , lift0 2 q , lift0 2 α)
    | _ , _ => (0 , tVar "oops" , tVar "oops")
    end.

  Definition pref_kit : TransKit :=
    let M := Reader State in
    {| (* ctx takes the initial p, and returns the context as well as the
          variable bindings done therein, so that we may eval the type for
          context extension *)
       ctx := term -> (list term) * State;
       ty := M (term * term);
       tm := M (term * term);
       emp_ctx p := ([] , ([] , p));
       ext_ctx Γ T p := ([] , ([] , p));
       pop_ctx Γ p := ([] , ([] , p));
       var_tm _ n := '(l , p) <- ask ;;
         let '(n , q , α) := lookup_var n l
         in ret (tApp (tRel (1 + n)) [q;α] , tApp (tRel n) [q;α]);
       el := todo "el";
       sort_tsl _ s :=
         let boxT := todo "FIXME" in
         let boxR := todo "FIXME" in
         ret (tApp ppsh_build [boxT;boxR] , todo "FIXME");
       prod_tsl := todo "prod_tsl";
       app_tsl := todo "app_tsl";
       lambda_tsl := todo "lambda_tsl"
    |}.

End Prefascist.
