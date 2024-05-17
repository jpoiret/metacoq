From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
(* From MetaCoq.Translations Require Import translation_utils. *)

Import MCMonadNotation.

Set Universe Polymorphism.

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
Definition irrNamed (n : ident) := {| binder_name := nNamed n ; binder_relevance := Irrelevant |}.


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
Set Definitional UIP.
Set Primitive Projections.
Unset MetaCoq Strict Unquote Universe Mode.
Set Printing Universes.

Section Prefascist.

  Definition Reader (I : Type) (A : Type) := I -> A.

  #[export] Instance Reader_Instance (I : Type) : Monad (Reader I) :=
    {| ret _ a _ := a ;
       bind _ _ a f i := f (a i) i
    |}.

  Definition ask {I : Type} : Reader I I := fun i => i.

  Definition local {I J A : Type} (f : I -> J) (r : Reader J A) : Reader I A := fun i => r (f i).

  Compute (local (fun u => 2 + u) ask ;; ask) 2.

Class PreCat@{u v} : Type :=
    { ob : Type@{u} ;
      mor : ob -> ob -> Type@{v};
      id : forall (a : ob), mor a a;
      comp : forall {a b c : ob}, mor a b -> mor b c -> mor a c;
    }.

  Notation "'force' α : q → p , A" := (forall (q : ob) (α : mor q p), A) (at level 80, α name, q name, p at next level, right associativity).

  Record PPsh@{u v w} {ℂ : PreCat@{v w}} (p : ob) : Type :=
    { T : force α : q → p, Type@{u};
      R : (force α : q → p, T q α) -> SProp
    }.

  Print PPsh.

  Inductive seq@{u} {A : Type@{u}} (a:A) : A -> SProp :=
      srefl : seq a a.

  Lemma cast@{u v} {A B : Type@{u}} (e : seq@{v} A B) (a : A) : B.
  Proof.
    inversion e as [H]. rewrite <- H. exact a.
  Defined.

  MetaCoq Run (ref <- tmLocate1 "PreCat" ;;
               match ref with
               | IndRef ind => tmDefinition "precat_term" (tInd ind [Level.lvar 1; Level.lvar 0]) ;;
                               tmDefinition "precat_build" (tConstruct ind 0 [fresh_level; fresh_level]) ;;
                               tmDefinition "ob_term" (fun t => tProj (mkProjection ind 0 0) t) ;;
                               tmDefinition "mor_term" (fun t => tProj (mkProjection ind 0 1) t) ;;
                               tmDefinition "id_term" (fun t => tProj (mkProjection ind 0 2) t) ;;
                               tmDefinition "comp_term" (fun t => tProj (mkProjection ind 0 3) t)
               | _ => tmFail "Not an inductive"
               end).

  MetaCoq Run (ref <- tmLocate1 "seq" ;;
               match ref with
               | IndRef ind => tmDefinition "seq_term" (tInd ind [fresh_level]) ;;
                               tmDefinition "srefl_term" (tConstruct ind 0 [fresh_level])
               | _ => tmFail "Not an inductive"
               end).
  MetaCoq Run (ref <- tmLocate1 "cast" ;;
               match ref with
               | ConstRef c => tmDefinition "cast_term" (tConst c [fresh_level;fresh_level])
               | _ => tmFail "Not a constant"
               end).

  MetaCoq Run (ref <- tmLocate1 "PPsh" ;;
               match ref with
               | IndRef ind => tmQuoteInductive ind.(inductive_mind) >>= tmPrint ;;
                               tmDefinition "ppsh_term" (fun s => tInd ind [s; Level.lvar 1; Level.lvar 0]) ;;
                               tmDefinition "ppsh_build" (tConstruct ind 0 [fresh_level; Level.lvar 1; Level.lvar 0]) ;;
                               tmDefinition "T_term" (fun t => tProj (mkProjection ind 2 0) t) ;;
                               tmDefinition "R_term" (fun t => tProj (mkProjection ind 2 1) t)
               | _ => tmFail "Not an inductive"
               end).

  Check @Build_PPsh.

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
  its stage and the second being whether it is a forcing quantification.  We
  also remember the current stage and category implementation *)

  Definition State := (list (term * bool) * term * term).

  (* b denotes whether the binding is a forcing quantification *)
  Definition push_binding (b : bool) '((vars , p , cat) : State) : State :=
    (vars ,, (p , b) , if b then tRel 1 else lift0 2 p , lift0 2 cat).

  Fixpoint lookup_var (n : nat) (ℂ_impl : term) (l : list (term * bool)) : nat * term * term :=
    match n , l with
    | n , (p , true) :: l => let '(k , q , α) := lookup_var n ℂ_impl l in
      (S (S k) , tRel 1 , mkApps (comp_term ℂ_impl) [tRel 1; lift0 2 q; lift0 2 p; tRel 0; lift0 2 α])
    | 0 , (p , false) :: l => (0 , lift0 2 p , mkApps (id_term ℂ_impl) [lift0 2 p])
    | S n , (p , false) :: l => let '(k , q , α) := lookup_var n ℂ_impl l in
      (S (S k) , lift0 2 q , lift0 2 α)
    | _ , _ => (0 , tVar "oops" , tVar "oops")
    end.

  (* FIXME EXPAND THIS
   * Translation returns stuff with universe variables for the cat *)
  Definition pref_kit : TransKit :=
    let M := Reader State in
    let el _ AM :=
         '(_ , p , ℂ_impl) <- ask;;
         '(A , Aparam) <- local (push_binding true) AM ;;
         '(A' , _) <- local (push_binding true ∘ push_binding true) AM ;;
         let f := fun wc cont => tProd (relNamed "q") (ob_term (lift0 wc ℂ_impl)) (tProd (relNamed "α") (mkApps (mor_term (lift0 (S wc) ℂ_impl)) [tRel 0; lift0 (S wc) p]) cont) in
         let elT := mkApps (T_term A) [tRel 1; mkApps (id_term (lift0 2 ℂ_impl)) [tRel 1]] in
         ret (f 0 elT
           , tLambda (relNamed "x0") (f 0 elT)
             (f 1 (mkApps (R_term (lift 1 2 A))
               [ tLambda relAnon (ob_term (lift0 3 ℂ_impl))
                   (tLambda relAnon (mkApps (mor_term (lift0 4 ℂ_impl)) [tRel 0; tRel 2])
                     (mkApps cast_term
                       [ mkApps (T_term (lift 1 4 A')) [tRel 1; mkApps (id_term (lift0 5 ℂ_impl)) [tRel 1]]
                       ; mkApps (T_term (lift0 2 (lift 1 2 A))) [tRel 1; tRel 0]
                       ; mkApps (lift0 2 (lift 1 2 Aparam)) [tRel 1; tRel 0]
                       ; mkApps (tRel 4)
                           [tRel 1
                           ; mkApps (comp_term (lift0 5 ℂ_impl)) [tRel 1; tRel 3; lift0 5 p; tRel 0; tRel 2]]]))]))) in
    {| (* ctx takes the initial p as well as the category itself, and returns
          the context as well as the variable bindings done therein, so that we
          may eval the type for context extension *)
       ctx := term -> term -> (list term) * State;
       ty := M (term * term);
       tm := M (term * term);
       emp_ctx p ℂ_impl := ([] , ([] , p, ℂ_impl));
       ext_ctx Γ T p ℂ_impl := ([] , ([] , p, ℂ_impl));
       pop_ctx Γ p ℂ_impl := ([] , ([] , p, ℂ_impl));
       var_tm _ n := '(l , p, ℂ_impl) <- ask ;;
         let '(n , q , α) := lookup_var n ℂ_impl l
         in ret (mkApps (tRel (1 + n)) [q;α] , mkApps (tRel n) [q;α]);
       el := el;
       sort_tsl _ s :=
         let l := match s with
           | sType u => match (Universe.get_is_level u) with
             | Some l => l
             | _ => todo "oops"
             end
           | _ => todo "FIXME: We only handle Type for now"
           end in
         '(_ , p , ℂ_impl) <- ask ;;
         let f := fun wc k cont => k (relNamed "q") (ob_term (lift0 wc ℂ_impl)) (k (relNamed "α") (mkApps (mor_term (lift0 (S wc) ℂ_impl)) [tRel 0; lift0 (S wc) p]) cont) in
         let boxT := f 0 tLambda (mkApps (ppsh_term l) [lift0 2 ℂ_impl; tRel 1]) in
         let boxR := tLambda (relNamed "A") (f 0 tProd (mkApps (ppsh_term l) [lift0 2 ℂ_impl; tRel 1]))
           (f 1 tProd
             (mkApps seq_term
               [ tSort s
               ; mkApps (T_term (mkApps (tRel 2) [tRel 1; tRel 0]))
                        [tRel 1; mkApps (id_term (lift0 3 ℂ_impl)) [tRel 1]]
               ; mkApps (T_term (mkApps (tRel 2) [ lift0 3 p
                                             ; mkApps (id_term (lift0 3 ℂ_impl))
                                                 [lift0 3 p]]))
                        [tRel 1; tRel 0]])) in
         ret ( mkApps ppsh_build [ℂ_impl; p; boxT;boxR]
             , f 0 tLambda (mkApps srefl_term [tSort (sType (Universe.make' fresh_level)); mkApps (ppsh_term l) [lift0 2 ℂ_impl; tRel 1]]));
       prod_tsl Γ a AM BM :=
         '(_ , p , ℂ_impl) <- ask ;;
         '(A , Aparam) <- el Γ AM ;;
         '(A' , Aparam') <- local (push_binding true) (el Γ AM) ;;
         '(B , Bparam) <- local (push_binding false) BM ;;
         '(B' , Bparam') <- local (push_binding true ∘ push_binding false) BM ;;
         let boxT := tLambda (relNamed "q") (ob_term ℂ_impl) (tLambda (relNamed "α") (mkApps (mor_term (lift0 1 ℂ_impl)) [tRel 0; lift0 1 p]) (tProd (relNamed "x0") A' (tProd (irrNamed "xε") (mkApps (lift0 1 Aparam') [tRel 0]) (mkApps (T_term B') [tRel 3; mkApps (id_term (lift0 4 ℂ_impl)) [tRel 3]])))) in
         let boxR := tLambda (relNamed "f") (tProd (relNamed "q") (ob_term ℂ_impl) (tProd (relNamed "α") (mkApps (mor_term (lift0 1 ℂ_impl)) [tRel 0; lift0 1 p]) (tProd (relNamed "x0") A' (tProd (irrNamed "xε") (mkApps (lift0 1 Aparam') [tRel 0]) (mkApps (T_term B') [tRel 3; mkApps (id_term (lift0 4 ℂ_impl)) [tRel 3]]))))) (tProd (relNamed "x0") (lift0 1 A) (tProd (irrNamed "xε") (mkApps (lift0 2 Aparam) [tRel 0]) (mkApps (R_term (lift 1 2 B))
         [ tLambda (relNamed "q") (ob_term (lift0 3 ℂ_impl))
                   (tLambda (relNamed "α") (mkApps (mor_term (lift0 4 ℂ_impl)) [tRel 0; lift0 4 p])
                     (mkApps cast_term
                       [ mkApps (T_term (lift 1 4 B')) [tRel 1; mkApps (id_term (lift0 5 ℂ_impl)) [tRel 1]]
                       ; mkApps (T_term (lift0 2 (lift 1 2 B))) [tRel 1; tRel 0]
                       ; mkApps (lift0 2 (lift 1 2 Bparam)) [tRel 1; tRel 0]
                       ; mkApps (tRel 4)
                           [tRel 1
                           ; mkApps (comp_term (lift0 5 ℂ_impl)) [tRel 1; tRel 3; lift0 5 p; tRel 0; tRel 2]]]))]
                           ))) in
         ret (mkApps ppsh_build [ℂ_impl; p; boxT; boxR] , todo "Hello");
       app_tsl := todo "app_tsl";
       lambda_tsl := todo "lambda_tsl"
    |}.

  Universe i.

  Instance SCat : PreCat@{i Set} :=
    {| ob := Set
     ; mor A B := A -> B : Set
     ; id A x := x
     ; comp _ _ _ f g x := g (f x) |}.

  (* Simple check that this is indeed a strict category. *)
  Goal forall (A B : ob) (f : mor A B), seq (comp f (id B)) f.
  Proof.
    intros A B f.
    exact (srefl f).
  Qed.

  MetaCoq Quote Definition scat_term := @SCat.

  Definition test2 := forall (A : Set), Set.
  MetaCoq Run (tm <- (tmEval all test2 >>= tmQuote) ;;
             i_level <- tmQuoteLevel@{i _ _} ;;
             let r := (tsl_kit_tm (k := pref_kit) (fun p impl => ([] , ([] , p , impl))) tm) in
             let '(u , v) := r ([] , tRel 0 , lift0 1 scat_term) in
             let u := (tLambda (relNamed "p") <% Set : Type@{i} %> (u @[ [Level.lzero; i_level] ])) in
             tmEval all u >>= tmPrint ;;
             unq <- tmUnquote u ;;
             tmEval all unq.(my_projT2) >>= tmPrint).


End Prefascist.
