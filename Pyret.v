Require Import Prelude.
Require Import ListExt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Module Pyret (Import AtomM : ATOM) (Import String : STRING).

Module Atom := AtomM.AtomUOT.
Module Atoms := Coq.MSets.MSetList.Make (Atom).
Module AtomEnv := Coq.FSets.FMapList.Make (AtomM.Atom_as_OT).


Lemma eq_atom_refl : forall (a : atom), Atom.eq a a.
Proof. reflexivity. Qed.
Lemma eq_atom_sym : forall (a1 a2 : atom), Atom.eq a1 a2 -> Atom.eq a2 a1.
Proof. intros. symmetry. assumption. Qed.
Lemma eq_atom_trans : forall (a1 a2 a3 : atom), Atom.eq a1 a2 -> Atom.eq a2 a3 -> Atom.eq a1 a3.
Proof. intros. transitivity a2; assumption. Qed.

Add Relation AtomM.atom Atom.eq
  reflexivity proved by eq_atom_refl
  symmetry proved by eq_atom_sym
  transitivity proved by eq_atom_trans
as Eq_atom.


Ltac destruct_eq_dec a b :=
  let Eq := fresh "Eq" in
  destruct (Atom.eq_dec a b) eqn:Eq;
    try (unfold atom_eq_dec; rewrite Eq); auto;
    try solve [match goal with
                 | [ H : ?x <> ?x |- _ ]
                   => exfalso; apply H; reflexivity end].

Definition atom := AtomM.atom. (* free variables *)
Definition loc := AtomM.atom.
Definition string := String.string.

Parameter __check__ : atom.
Parameter __brand__ : atom.
Parameter __has_brand__ : atom.
Parameter __add_brand__ : atom.

Axiom check_brand_distinct : __check__ <> __brand__.
Axiom has_add_distinct : __has_brand__ <> __add_brand__.

(* Tests *)
Goal (if Atom.eq_dec __check__ __check__ then 5 else 6) = 5.
destruct_eq_dec __check__ __check__.
Defined.
Goal (if Atom.eq_dec __check__ __brand__ then 5 else 6) = 6.
destruct_eq_dec __check__ __brand__.
  exfalso. apply check_brand_distinct; auto. Qed.

Inductive brand : Set :=
  | mkbrand : atom -> brand.

Unset Elimination Schemes.
Inductive exp : Set :=
  | elam : list brand -> atom -> exp -> exp
  | eapp : exp -> exp -> exp
  | eid : atom -> exp
  | eobj : list brand -> list (atom * exp) -> exp
  | ebool : list brand -> bool -> exp
  | ebrand : brand -> exp
  | edelta : atom -> exp -> exp -> exp
  | egetfield : atom -> exp -> exp.
Set Elimination Schemes.

Definition exp_ind :=
  fun (P : exp -> Prop)
  (exp_rec_lam :
     forall (bs : list brand)
            (a : atom) (e : exp), P e -> P (elam bs a e))
  (exp_rec_app :
     forall a e : exp, P a -> P e -> P (eapp a e))
  (exp_rec_id :
     forall a : atom, P (eid a))
  (exp_rec_obj :
     forall (bs : list brand)
            (fs : list (atom * exp)),
       Forall P (map snd fs) ->
       P (eobj bs fs))
  (exp_rec_bool :
     forall (l : list brand) (b : bool), P (ebool l b))
  (exp_rec_brand :
     forall (b : brand), P (ebrand b))
  (exp_rec_delta :
     forall (a : atom) (e1 : exp) (e2 : exp), P e1 -> P e2 -> P (edelta a e1 e2))
  (exp_rec_getfield :
     forall (a : atom) (e : exp), P e -> P (egetfield a e)) =>
fix F (e : exp) : P e :=
  match e as e0 return (P e0) with
  | elam bs a e => exp_rec_lam bs a e (F e)
  | eapp a e => exp_rec_app a e (F a) (F e)
  | eid a => exp_rec_id a
  | eobj bs fs =>
    exp_rec_obj
      bs fs
      ((fix forall_rec
            (ls : list (atom * exp)) : Forall P (map snd ls) :=
          match ls with
            | nil => Forall_nil P
            | (_,e)::rest => Forall_cons e (F e) (forall_rec rest)
          end) fs)
  | ebool l b => exp_rec_bool l b
  | ebrand b => exp_rec_brand b
  | edelta a e1 e2 => exp_rec_delta a e1 e2 (F e1) (F e2)
  | egetfield a e => exp_rec_getfield a e (F e)
  end.

Definition values l := map (@snd atom exp) l.

Inductive value : exp -> Prop :=
  | vbool : forall l b, value (ebool l b)
  | vobj : forall l fs, Forall value (map snd fs) -> value (eobj l fs)
  | vlam : forall bs xs b, value (elam bs xs b)
  | vbrand : forall b, value (ebrand b).

 Hint Constructors value.


Inductive E : Set :=
  | E_hole : E
  | E_app1 : E -> exp -> E
  | E_app2 : exp -> E -> E
  | E_getfield : atom -> E -> E
  | E_obj : forall (bs : list brand)
                   (vs : list (atom * exp))
                   (es : list (atom * exp)),
              (Forall value (values vs)) ->  atom -> E -> E
  | E_delta1 : atom -> E -> exp -> E
  | E_delta2 : atom -> exp -> E -> E.

Inductive ae : exp -> Prop :=
  | redex_app  : forall e1 e2, value e1 -> value e2 -> ae (eapp e1 e2)
  | redex_getfield : forall a e1, value e1 -> ae (egetfield a e1)
  | redex_delta : forall a e1 e2, value e1 -> value e2
                                  -> ae (edelta a e1 e2).


Inductive decompose : exp -> E -> exp -> Prop :=
  | ctxt_hole : forall e,
      ae e ->
      decompose e E_hole e
  | ctxt_app1 : forall E e1 e2 e',
      decompose e1 E e' ->
      decompose (eapp e1 e2) (E_app1 E e2) e'
  | ctxt_app2 : forall E v e e',
      value v ->
      decompose e E e' ->
      decompose (eapp v e) (E_app2 v E) e'
  | ctxt_getfield : forall a e E e',
                      decompose e E e' ->
                      decompose (egetfield a e) (E_getfield a E) e'
  | ctxt_obj : forall bs vs es a e E e'
                      (are_vals : Forall value (values vs)),
      decompose e E e' ->
      decompose (eobj bs (vs++(a,e)::es))
                (E_obj bs vs es are_vals a E) e'
  | ctxt_delta1 : forall a E e1 e2 e',
                    decompose e1 E e' ->
                    decompose (edelta a e1 e2) (E_delta1 a E e2) e'
  | ctxt_delta2 : forall a v E e e',
                    value v ->
                    decompose e E e' ->
                    decompose (edelta a v e) (E_delta2 a v E) e'.


Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole => e
  | E_app1 ctxt e2 => eapp (plug e ctxt) e2
  | E_app2 v ctxt => eapp v (plug e ctxt)
  | E_getfield a ctxt => egetfield a (plug e ctxt)
  | E_obj bs vs es _ a ctxt => eobj bs (vs++(a,plug e ctxt)::es)
  | E_delta1 a ctxt e' => edelta a (plug e ctxt) e'
  | E_delta2 a v ctxt => edelta a v (plug e ctxt)
  end.


SearchAbout sumbool.

SearchAbout pair.

SearchAbout beq_nat.

Fixpoint subst (x:atom) (e:exp) (b:exp) :=
  match b with
    | elam bs arg body =>
      if Atom.eq_dec x arg
      then b
      else elam bs arg (subst x e body)
    | eapp fn arg =>
      eapp (subst x e fn) (subst x e arg)
    | eid x' =>
      if Atom.eq_dec x x' then e else b
    | edelta a arg1 arg2 => edelta a (subst x e arg1) (subst x e arg2)
    | eobj bs vs =>
      eobj bs (map (fun v => (fst v, subst x e (snd v))) vs)
    | egetfield a o => egetfield a (subst x e o)
    | ebool _ _ => b
    | ebrand _ => b
  end.

Fixpoint subst_many (xs : list atom) (es : list exp) (b : exp) :=
  match (xs,es) with
    | (cons x xs', cons e es') => subst_many xs' es' (subst x e b)
    | _ => b
  end.

Inductive eq_brand_i : brand -> brand -> Type :=
  | eq_brand : forall b1 b2, b1 = b2 ->
                             eq_brand_i (mkbrand b1)
                                        (mkbrand b2).

Fixpoint beq_brand (b1:brand) (b2:brand) :=
  match (b1,b2) with
    | (mkbrand x1, mkbrand x2) =>
      if Atom.eq_dec x1 x2 then true else false
  end.

Fixpoint brand_list (e:exp) : list brand :=
  match e with
    | eobj l _ => l
    | ebool l _ => l
    | _ => nil
  end.

Fixpoint brand_elem (l:list brand) (b:brand) : bool :=
  match l with
    | nil => false
    | (cons x xs) => if beq_brand x b then true else brand_elem xs b
  end.

Fixpoint has_brand (b:brand) (e:exp) : bool :=
  brand_elem (brand_list e) b.

Fixpoint add_brand (b:brand) (e:exp) : exp :=
  if has_brand b e then e else
  match e with
    | eobj l vs => eobj (cons b l) vs
    | ebool l v => ebool (cons b l) v
    | elam l a body => elam (cons b l) a body
    | _ => e
  end.

SearchAbout list.

Fixpoint snoc {A:Type} (l:list A) (e:A) : list A :=
  match l with
    | [] => [e]
    | l::ls => l::(snoc ls e)
  end.

SearchAbout nth.


Inductive step : exp -> exp -> Prop :=
  | sdecompose : forall e E e' e'',
                   decompose e E e' ->
                   step e' e''
                   -> step e (plug e'' E)
  | sapp : forall x e b l,
             value e ->
             step (eapp (elam l x b) e)
                  (subst x e b)
  | sobj : forall bs vs a e e' es,
             Forall value (values vs) ->
             Forall (fun x => ~ value x) (map snd es) ->
             ~ value e ->
             step e e' ->
             step (eobj bs (vs ++ (cons (a,e) es)))
                  (eobj bs (vs ++ (cons (a,e') es)))
  | sgetfield : forall bs vs es a e,
                  Forall value (values vs) ->
                  Forall value (values es) ->
                  step (egetfield a (eobj bs (vs ++ (cons (a,e) es))))
                       e
  | sdelta1 : forall a e1 e1' e2,
               step e1 e1' ->
               step (edelta a e1 e2) (edelta a e1' e2)
  | sdelta2 : forall a e1 e2 e2',
               value e1 ->
               step e2 e2' ->
               step (edelta a e1 e2) (edelta a e1 e2')
  | sdelta_hb : forall e b,
                  value e ->
                  step (edelta __has_brand__ (ebrand b) e)
                       (ebool nil (has_brand b e))
  | sdelta_ab : forall e b,
                  value e ->
                  step (edelta __add_brand__ (ebrand b) e)
                       (add_brand b e).


Parameter __some_brand__ : atom.

Example step_has_brand1 :
  step (edelta __has_brand__ (ebrand (mkbrand __some_brand__))
               (ebool nil true))
       (ebool nil false).
Proof.
  apply sdelta_hb. constructor.
Qed.

Example step_add_brand1 :
  step (edelta __add_brand__ (ebrand (mkbrand __some_brand__))
               (ebool nil true))
       (ebool [mkbrand __some_brand__] true).
Proof.
  apply sdelta_ab. constructor.
Qed.

Definition multistep := multi step.

Example step_add_has_brand1 :
  multistep
    (edelta __has_brand__
            (ebrand (mkbrand __some_brand__))
            (edelta __add_brand__ (ebrand (mkbrand __some_brand__))
                    (ebool nil true)))
    (ebool nil true).
Proof.
  apply multi_step with
  (y := (edelta __has_brand__ (ebrand (mkbrand __some_brand__))
                (ebool (cons (mkbrand __some_brand__) nil) true))).
  apply sdelta2.
  constructor.
  apply sdelta_ab.
  constructor.
  eapply multi_step.
  apply sdelta_hb.
  constructor.
  simpl.
  destruct_eq_dec __some_brand__ __some_brand__.
  eapply multi_refl.
Qed.

Parameter f1 : atom.
Parameter f2 : atom.

SearchAbout fold_right.

Lemma app_split : forall A : Type, forall x y : list A,
                    x ++ y = fold_right cons y x.
Proof.
  intros.
  induction x.
  reflexivity.
  simpl. rewrite IHx. reflexivity.
Qed.

Lemma fold_cons : forall A : Type, forall x : A, forall y : list A,
                    x :: y = fold_right cons y [x].
Proof.
  intros.
  reflexivity.
Qed.

(* Example step_obj1 : *)
(*   multistep *)
(*     (eobj nil *)
(*           ((f1,ebool nil true) *)
(*              ::(f2, edelta __has_brand__ *)
(*                        (ebrand (mkbrand __some_brand__)) *)
(*                        (ebool nil true)) *)
(*              ::nil)) *)
(*     (eobj nil ((f1,ebool nil true)::(f2,ebool nil false)::nil)). *)
(* Proof. *)
(*   SearchAbout Forall. *)
(*   eapply multi_step. *)
(*   replace  ((f1,ebool nil true) *)
(*              ::(f2, edelta __has_brand__ *)
(*                        (ebrand (mkbrand __some_brand__)) *)
(*                        (ebool nil true)) *)
(*              ::nil) with  ([(f1,ebool nil true)] *)
(*              ++ ((f2, edelta __has_brand__ *)
(*                        (ebrand (mkbrand __some_brand__)) *)
(*                        (ebool nil true)) *)
(*              ::nil)) by auto. *)
(*   eapply sdecompose. *)
(*   apply ctxt_obj. *)
(*   apply ctxt_hole. *)
(*   apply redex_delta. *)
(*   constructor. constructor. *)
(*   eapply sdelta_hb. *)
(*   constructor. *)
(*   simpl. *)
(*   eapply multi_refl. *)
(* Qed. *)


Parameter __arg__ : atom.

Example step_app_lam1 :
  multistep
    (eapp (elam nil __arg__ (eid __arg__)) (ebool nil true))
    (ebool nil true).
Proof.
  eapply multi_step with (y := (subst __arg__ (ebool nil true) (eid __arg__))).
  apply sapp.
  constructor.
  simpl.
  destruct_eq_dec __arg__ __arg__.
  apply multi_refl.
Qed.

Example step_getfield1 :
  multistep
    (egetfield f1 (eobj [] [(f1, ebool nil true)]))
    (ebool nil true).
Proof.
  eapply multi_step.
  change [(f1, ebool nil true)] with ([] ++ [(f1, ebool nil true)]).
  eapply sgetfield.
  constructor.
  constructor.
  eapply multi_refl.
Qed.


(* Start the actual proofs of things that are actually interesting. *)
Theorem values_dont_step : forall e e', value e -> ~ step e e'.
Proof.
  admit.
Qed.


(* Note: following couple of lemmas taken dirently or adapted from lambda js *)
Lemma decompose_ae : forall e E e',
  decompose e E e' -> ae e'.
Proof with auto. intros. induction H... Qed.

Lemma plug_ok : forall e E e',
  decompose e E e' -> plug e' E = e.
Proof.
  intros.
  induction H; try (auto || simpl; rewrite IHdecompose; reflexivity).
Qed.

Lemma values_dec : forall e, value e \/ ~ value e.
Proof with eauto.
unfold not. intro.
induction e; try solve [left; constructor | right; intro H; inversion H].
Case "e_obj".
apply (forall_dec_dec_forall value (l:=(map (@snd atom exp) fs))) in H.
inversion H.
left; constructor; unfold values; auto... right. intro. inversion H1. contradiction.
Qed.

(* My lemmas start *)

Lemma values_dont_decompose : forall e E e', value e -> ~ decompose e E e'.
Proof.
  intros. unfold not. intro.
  (* This is absolute insanity. the whole point is that active expressions are not compatible with *)
  (* values, but I can't seem to get coq to recognize that in a non-heinous manner.  *)
  induction H0.
  inversion H. inversion H0. subst. inversion H4. subst.
  inversion H3. subst. inversion H4. inversion H0. subst. inversion H5. subst. inversion H4.
  subst. inversion H5. inversion H0. subst. inversion H4. subst. inversion H3. subst. inversion H4.
  inversion H0. subst. inversion H4. subst. inversion H3. subst. inversion H4. inversion H.
  inversion H. inversion H.
  (* Object case sucks! *)
  inversion H. inversion H0. subst. SearchAbout Forall. rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  SearchAbout Forall.
  inversion H2. simpl in H5. apply IHdecompose. assumption.
  (* apparently I don't know how to make the repeat tactic work. *)
(*      repeat (this stuff) only does it one time. copy-paste works 6 times.*)
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H10. apply IHdecompose. assumption.
  inversion H. inversion H.
Qed.

(* This was sort of a baby-lemma, to get more familiar, so I could then prove
   the real thing, decompose_det *)
Lemma decompose_det_exp : forall x C y0 y1,
                        decompose x C y0 ->
                        decompose x C y1 -> y0 = y1.
Proof.
  intros.
  generalize dependent y1.
  induction H.
  Case "ctxt_hole".
  intros. inversion H0. reflexivity.
  Case "ctxt_app1".
  intros. inversion H0. subst. apply IHdecompose in H5. assumption.
  Case "ctxt_app2".
  intros. inversion H1. subst. apply IHdecompose in H7. assumption.
  Case "ctxt_getfield".
  intros. inversion H0. subst. apply IHdecompose in H5. assumption.
  Case "ctxt_obj".
  intros. inversion H0. subst. apply app_inv_head in H3. inversion H3. subst.
  apply IHdecompose in H8. assumption.
  Case "ctxt_delta1".
  intros. inversion H0. apply IHdecompose in H6. assumption.
  Case "ctxt_delta2".
  intros. inversion H1. apply IHdecompose in H8. assumption.
Qed.




Lemma forall_head : forall A (l0 : list A) (e0 : A) (t0 : list A)
                           (l1 : list A) (e1 : A) (t1 : list A)
                           (P : A -> Prop) (dec : forall (x : A), (P x) \/ ~ (P x)),
                      (l0 ++ e0 :: t0) = (l1 ++ e1 :: t1) -> Forall P l0 -> Forall P l1 ->
                      ~ P e0 -> ~ P e1 -> l0 = l1 /\ e0 = e1 /\ t0 = t1.
Proof.
  (* Not my prettiest proof... *)
  intros. generalize dependent l1.
  induction l0. intros.
  induction l1. split. reflexivity. split. simpl in H. inversion H. reflexivity.
  simpl in H. inversion H. reflexivity.
  simpl in H. inversion H. subst. inversion H1. contradiction.
  intros. induction l1. simpl in H. inversion H. subst. inversion H0. contradiction.
  inversion H. apply IHl0 in H6. split. assert (l0 = l1).
  apply proj1 in H6. assumption. rewrite H4. reflexivity.
  apply proj2 in H6. assumption.
  inversion H0. assumption. inversion H1. assumption.
Qed.

Lemma decompose_det : forall x C0 C1 y0 y1,
                        decompose x C0 y0 ->
                        decompose x C1 y1 -> y0 = y1 /\ C0 = C1.
Proof.
  intros.
  generalize dependent y1.
  generalize dependent C1.
  induction H.
  (* Focus 2. *)
  Case "ctxt_hole".
  intros. inversion H0.
  SCase "ctxt_hole".
  split ; reflexivity.
  SCase "ctxt_app1". subst.  inversion H. inversion H0.
  apply values_dont_decompose with (E := E0) (e' := y1) in H4. contradiction.
  SCase "ctxt_app2". subst.
  inversion H. apply values_dont_decompose with (E := E0) (e' := y1) in H6. contradiction.
  SCase "ctxt_getfield".
  inversion H. subst. inversion H7. subst. inversion H6. subst.
  apply values_dont_decompose with (E := E0) (e' := y1) in H5. contradiction.
  subst. inversion H7.
  SCase "ctxt_obj". subst. inversion H.
  SCase "ctxt_delta1". inversion H. subst. inversion H7. subst. inversion H6. subst.
  inversion H7. subst. apply values_dont_decompose with (E := E0) (e' := y1) in H5. contradiction.
  SCase "ctxt_delta2". inversion H. subst. inversion H8. subst. inversion H7. subst. inversion H8.
  subst. apply values_dont_decompose with (E := E0) (e' := y1) in H7. contradiction.
  Case "ctxt_app1".
  intros.
  (* The induction is confusing me here. x is (eapp e1 e2). C0 should be (E_app1 E0 e2), but
     is missing, for unknown reason. y0 is e'. C1 is anything, y1 is anything.  and of course
     we want to show that e' = y1. *)
  inversion H0. subst. inversion H1. apply values_dont_decompose with (E := E0) (e' := e') in H4.
  exfalso. auto.
  subst. apply IHdecompose in H5. split. apply proj1 in H5. assumption. apply proj2 in H5. subst.
  reflexivity.
  apply values_dont_decompose with (E := E0) (e' := e') in H3. exfalso. auto.
  Case "ctxt_app2".
  intros.
  inversion H1. subst. inversion H2. apply values_dont_decompose with (E := E0) (e' := e') in H6.
  exfalso. auto.
  subst. apply values_dont_decompose with (E := E1) (e' := y1) in H. exfalso. auto.
  subst. apply IHdecompose in H7. split. apply proj1 in H7. assumption. assert (E0 = E1).
  apply proj2 in H7. assumption. subst. reflexivity.
  case "ctxt_getfield".
  intros.
  inversion H0. subst. inversion H1. apply values_dont_decompose with (E := E0) (e' := e') in H3.
  exfalso. auto.
  subst. apply IHdecompose in H5. split. apply proj1 in H5. assumption. apply proj2 in H5. subst.
  reflexivity.
  Case "ctxt_obj".
  intros.
  inversion H0. subst. inversion H1.
  subst. assert (~ value e0). unfold not. intro.
  apply values_dont_decompose with (E := E1) (e' := y1) in H1. auto.
  assert (~ value e).
  unfold not. intro.
  apply values_dont_decompose with (E := E0) (e' := e') in H2. auto.
  assert (vs0 = vs).
    apply forall_head with (P := fun p : atom*exp => value ((@snd atom exp) p)) in H3.
    apply proj1 in H3. assumption. intro. destruct x. simpl. apply values_dec.
    unfold values in are_vals0. rewrite <- forall_map_comm. assumption.
    rewrite <- forall_map_comm. assumption. simpl. assumption. simpl. assumption.
  subst. apply app_inv_head in H3. inversion H3. subst. apply IHdecompose in H5.
  split. apply proj1 in H5. assumption. apply proj2 in H5. subst.
  (* NOTE: How can I prove that are_vals and are_vals0 are the same? ie that Forall is one-to-one. *)
  admit.
  Case "ctxt_delta1".
  intros.
  inversion H0. inversion H1. apply values_dont_decompose with (E := E0) (e' := e') in H7.
  contradiction.
  subst. apply IHdecompose in H6. split. apply proj1 in H6. assumption. apply proj2 in H6. subst.
  reflexivity.
  subst. apply values_dont_decompose with (E := E0) (e' := e') in H6. contradiction.
  Case "ctxt_delta2".
  intros.
  inversion H1. inversion H2.
  apply values_dont_decompose with (E := E0) (e' := e') in H10. contradiction.
  subst. apply values_dont_decompose with (E := E1) (e' := y1) in H. contradiction.
  subst. apply IHdecompose in H8. split. apply proj1 in H8. assumption. apply proj2 in H8. subst.
  reflexivity.
Qed.



Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem pyret_step_deterministic : forall x y0 y1,
                        step x y0 ->
                        step x y1 -> y0 = y1.

Proof with eauto.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1.
  Case "sdecompose".
  intros y2 Hy2.
  inversion Hy2.
  SCase "sdecompose".
  subst. assert (e' = e'0 /\ E0 = E1). apply decompose_det with (x := e) (C0 := E0) (C1 := E1) ; assumption.
  remember H2 as H2'.
  clear HeqH2'.
  apply proj1 in H2'.
  subst. apply IHHy1 in H1. subst.
  apply proj2 in H2. subst. reflexivity. SearchAbout Forall.

  assert (E0 = E1).
  assert ()
  apply decompose_det with (x := e) (C0 := E0) (C1 := E1).



  subst.
  inversion
  apply plug_ok in H0. apply plug_ok in H.



  intros.
  rewrite plug_ok with (e := e).



  Case "sapp".
  inversion H0.

  Case "elam".
  apply values_dont_step in H. exfalso. assumption. constructor.
  Case "eapp".
  admit.
  Case "eid".
  inversion H. inversion H1.
  (* Why can't I get a contradiction; there is clearly no way to step from eid *)


End Pyret.