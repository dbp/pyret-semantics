Require Import Prelude.
Require Import ListExt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import ProofIrrelevance.

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

Axiom check_brand_distinct : __check__ <> __brand__.

(* Tests *)
Goal (if Atom.eq_dec __check__ __check__ then 5 else 6) = 5.
destruct_eq_dec __check__ __check__.
Defined.
Goal (if Atom.eq_dec __check__ __brand__ then 5 else 6) = 6.
destruct_eq_dec __check__ __brand__.
  exfalso. apply check_brand_distinct; auto. Qed.

Inductive brand : Set :=
  | mkbrand : atom -> brand.

Inductive delta_op : Set :=
  | has_brand_delta : delta_op
  | add_brand_delta : delta_op.

Unset Elimination Schemes.
Inductive exp : Set :=
  | elam : list brand -> atom -> exp -> exp
  | eapp : exp -> exp -> exp
  | eid : atom -> exp
  | eobj : list brand -> list (atom * exp) -> exp
  | ebool : list brand -> bool -> exp
  | ebrand : brand -> exp
  | edelta : delta_op -> exp -> exp -> exp
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
     forall (a : delta_op) (e1 : exp) (e2 : exp), P e1 -> P e2 -> P (edelta a e1 e2))
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
  | E_delta1 : delta_op -> E -> exp -> E
  | E_delta2 : delta_op -> exp -> E -> E.

Inductive ae : exp -> Prop :=
  | redex_app : forall e1 e2, value e1 -> value e2 -> ae (eapp e1 e2)
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

Inductive has_brand_rel : exp -> brand -> Prop :=
  | has_brand_obj : forall l b vs, Forall value (values vs) ->
                                   In b l -> has_brand_rel (eobj l vs) b
  | has_brand_bool : forall l b v, In b l -> has_brand_rel (ebool l v) b
  | has_brand_lam : forall l a b body, In b l -> has_brand_rel (elam l a body) b.

Fixpoint add_brand (b:brand) (e:exp) {struct e} : exp :=
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


Inductive red : exp -> exp -> Prop :=
  | red_app : forall x e b l,
             value e ->
             red (eapp (elam l x b) e)
                 (subst x e b)
  | red_getfield : forall bs vs es a e,
                     Forall value (values vs) ->
                     Forall value (values es) ->
                     ~ In a (map (@fst atom exp) vs) ->
                     value e ->
                     red (egetfield a (eobj bs (vs ++ (cons (a,e) es))))
                         e
  | red_delta_hb : forall e b,
                     value e ->
                     red (edelta has_brand_delta (ebrand b) e)
                         (ebool nil (has_brand b e))
  | red_delta_ab : forall e b,
                     value e ->
                     red (edelta add_brand_delta (ebrand b) e)
                         (add_brand b e).



Inductive step : exp -> exp -> Prop :=
  | sdecompose : forall e E e' e'',
                   decompose e E e' ->
                   red e' e''
                   -> step e (plug e'' E).


Parameter __some_brand__ : atom.

Example step_has_brand1 :
  step (edelta has_brand_delta (ebrand (mkbrand __some_brand__))
               (ebool nil true))
       (ebool nil false).
Proof.
  assert ((ebool [] false) = (plug (ebool nil false) E_hole)). reflexivity.
  rewrite H.
  apply sdecompose with (e' := (edelta has_brand_delta (ebrand (mkbrand __some_brand__))
               (ebool nil true))).
  apply ctxt_hole. apply redex_delta. constructor. constructor. apply red_delta_hb. constructor.
Qed.

Example step_add_brand1 :
  step (edelta add_brand_delta (ebrand (mkbrand __some_brand__))
               (ebool nil true))
       (ebool [mkbrand __some_brand__] true).
Proof.
  assert ((ebool [mkbrand __some_brand__] true) = (plug (ebool [mkbrand __some_brand__] true) E_hole)).
  reflexivity.
  rewrite H.
  apply sdecompose with (e' := (edelta add_brand_delta (ebrand (mkbrand __some_brand__))
               (ebool nil true))).
  apply ctxt_hole. apply redex_delta. constructor. constructor. apply red_delta_ab. constructor.
Qed.

Definition multistep := multi step.

Example step_add_has_brand1 :
  multistep
    (edelta has_brand_delta
            (ebrand (mkbrand __some_brand__))
            (edelta add_brand_delta (ebrand (mkbrand __some_brand__))
                    (ebool nil true)))
    (ebool nil true).
Proof.
  apply multi_step with
  (y := (edelta has_brand_delta (ebrand (mkbrand __some_brand__))
                (ebool (cons (mkbrand __some_brand__) nil) true))).
  assert ((edelta has_brand_delta (ebrand (mkbrand __some_brand__))
                  (ebool [mkbrand __some_brand__] true))
          =
          (plug (ebool [mkbrand __some_brand__] true) (E_delta2 has_brand_delta (ebrand (mkbrand __some_brand__)) E_hole))).
  reflexivity.
  rewrite H.
  apply sdecompose with (e' := (edelta add_brand_delta (ebrand (mkbrand __some_brand__))
           (ebool [] true))).
  apply ctxt_delta2. constructor. apply ctxt_hole. constructor. constructor. constructor.
  apply red_delta_ab. constructor.
  apply multi_step with (y := (ebool [] true)).
  assert ((ebool [] true) =
          (plug (ebool [] true) E_hole)). reflexivity.
  rewrite H.
  apply sdecompose with (e' := (edelta has_brand_delta (ebrand (mkbrand __some_brand__))
        (ebool [mkbrand __some_brand__] true))).
  apply ctxt_hole. constructor. constructor. constructor.
  assert ((has_brand (mkbrand __some_brand__) (ebool [mkbrand __some_brand__] true))
          = true). simpl. destruct_eq_dec __some_brand__ __some_brand__.
  rewrite <- H0 at 2.
  apply red_delta_hb. constructor.
  apply multi_refl.
Qed.

Parameter f1 : atom.
Parameter f2 : atom.

(* SearchAbout fold_right. *)

(* Lemma app_split : forall A : Type, forall x y : list A, *)
(*                     x ++ y = fold_right cons y x. *)
(* Proof. *)
(*   intros. *)
(*   induction x. *)
(*   reflexivity. *)
(*   simpl. rewrite IHx. reflexivity. *)
(* Qed. *)

(* Lemma fold_cons : forall A : Type, forall x : A, forall y : list A, *)
(*                     x :: y = fold_right cons y [x]. *)
(* Proof. *)
(*   intros. *)
(*   reflexivity. *)
(* Qed. *)

Example step_obj1 :
  multistep
    (eobj nil
          ((f1,ebool nil true)
             ::(f2, edelta has_brand_delta
                       (ebrand (mkbrand __some_brand__))
                       (ebool nil true))
             ::nil))
    (eobj nil ((f1,ebool nil true)::(f2,ebool nil false)::nil)).
Proof.
  eapply multi_step.
  replace  ((f1,ebool nil true)
             ::(f2, edelta has_brand_delta
                       (ebrand (mkbrand __some_brand__))
                       (ebool nil true))
             ::nil) with  ([(f1,ebool nil true)]
             ++ ((f2, edelta has_brand_delta
                       (ebrand (mkbrand __some_brand__))
                       (ebool nil true))
             ::nil)) by auto.
  eapply sdecompose.
  apply ctxt_obj.
  apply ctxt_hole.
  apply redex_delta.
  constructor. constructor.
  eapply red_delta_hb.
  constructor.
  simpl.
  eapply multi_refl.
  (* Errg. we've proven it, but didn't satisfy the proof of values, so we have a dangling
     existential. just admit, for now *)
Admitted.


Parameter __arg__ : atom.

Example step_app_lam1 :
  multistep
    (eapp (elam nil __arg__ (eid __arg__)) (ebool nil true))
    (ebool nil true).
Proof.
  eapply multi_step with (y := (subst __arg__ (ebool nil true) (eid __arg__))).
  simpl. destruct_eq_dec __arg__ __arg__.
  assert ((ebool [] true) = (plug (ebool [] true) E_hole)). reflexivity. rewrite H at 2.
  eapply sdecompose.
  apply ctxt_hole. constructor. constructor. constructor.
  assert ((ebool [] true) = (subst __arg__ (ebool [] true) (eid __arg__))). simpl.
  destruct_eq_dec __arg__ __arg__.
  rewrite H0 at 2.
  apply red_app.
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
  assert ((ebool [] true) = (plug (ebool [] true) E_hole)). reflexivity. rewrite H at 2.
  eapply multi_step.
  apply sdecompose with (e' := (egetfield f1 (eobj [] [(f1, ebool [] true)]))).
  apply ctxt_hole. constructor. constructor. simpl. apply Forall_cons. constructor. constructor.
  change [(f1, ebool nil true)] with ([] ++ [(f1, ebool nil true)]).
  apply red_getfield. simpl. constructor. simpl. constructor. simpl. auto. constructor.
  eapply multi_refl.
Qed.


(* Start the actual proofs of things that are actually interesting. *)


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

Lemma map_cons : forall (A B : Type) (x : A) (l : list A) (f : A -> B),
                   map f (x::l) = (f x) :: (map f l).
Proof. intros. auto. Qed.

Lemma red_ae : forall e e', red e e' -> ae e.
Proof.
  intros.
  inversion H; try (repeat constructor || assumption).
  Case "egetfield".
  subst. SearchAbout app. rewrite map_app. rewrite forall_app.
  split. assumption. rewrite map_cons. simpl. constructor. assumption. assumption.
Qed.

Lemma values_dont_decompose : forall e E e', value e -> ~ decompose e E e'.
Proof.
  intros. unfold not. intro.
  (* This is absolute insanity. the whole point is that active expressions are not compatible with *)
  (* values, but I can't seem to get coq to recognize that in a non-heinous manner.  *)
  induction H0.
  inversion H.
  Case "ebool".
  inversion H0. subst. inversion H4. subst.
  inversion H3. subst. inversion H4.
  Case "eobj". subst. inversion H0.
  Case "elam". subst. inversion H0.
  Case "ebrand". subst. inversion H0.
  Case "eapp". inversion H.
  Case "eapp(?)". inversion H.
  Case "egetfield". inversion H.
  Case "eobj".
  inversion H. subst. rewrite forall_map_comm in H2.
  rewrite forall_app in H2. apply proj2 in H2.
  inversion H2. simpl in H4. apply IHdecompose. assumption.
  Case "edelta". inversion H.
  Case "edelta". inversion H.
Qed.

Theorem values_dont_step : forall e e', value e -> ~ step e e'.
Proof.
  intros. unfold not. intro. inversion H0.
  apply values_dont_decompose with (E := E0) (e' := e'0) in H.
  contradiction.
Qed.

(* This was sort of a baby-lemma, to get more familiar, so I could then prove
   the real thing, decompose_det. there is no point in having it, but I spent time on it
   so I don't want to delete it. *)
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
  f_equal. apply proof_irrelevance.
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

Lemma not_in_cons : forall (A : Type) (x : A) (a : A) (l : list A),
                 ~ In x (a :: l) -> ~ In x l.
Proof.
  intros.
  unfold not in *. intro. apply in_cons with (a := a) in H0. contradiction.
Qed.

Lemma not_in_forall : forall (A : Type) (x : A) (l : list A),
                        ~ In x l -> Forall (fun y => ~ x = y) l.
Proof.
  intros. induction l.
  Case "[]".
  constructor.
  Case "a::l".
  apply Forall_cons. unfold not. intro. subst.
  unfold not in H. apply H. apply in_eq.
  apply not_in_cons in H. apply IHl in H. assumption.
Qed.

Lemma red_det : forall x y0 y1,
                  red x y0 ->
                  red x y1 -> y0 = y1.
Proof.
  intros.
  generalize dependent y1.
  induction H.
  Case "red_app".
  intros. inversion H0. reflexivity.
  Case "red_getfield".
  intros. inversion H3. subst. SearchAbout sumbool.
  apply forall_head with (P := fun p : atom*exp => ~ (a = (fst p))) in H6.
  apply proj2 in H6. apply proj1 in H6. inversion H6. reflexivity.
  (* The next three lines are needed to prove what seems like a trivial thing;
     that ~ eq is decidable on atoms *)
  intro. destruct x. simpl. rewrite or_comm. apply not_and. apply dec_not. apply AtomM.atom_dec_eq.
  unfold not at 1. intro. remember H4 as H5. clear HeqH5. apply proj1 in H4.
  apply proj2 in H5. contradiction.
  apply not_in_forall in H10. rewrite forall_map_comm in H10. assumption.
  apply not_in_forall in H1. rewrite forall_map_comm in H1. assumption.
  simpl. auto.
  simpl. auto.
  Case "red_delta_hb".
  intros. inversion H0. subst. reflexivity.
  Case "red_delta_ab".
  intros. inversion H0. subst. reflexivity.
Qed.

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
  subst. assert (e' = e'0 /\ E0 = E1). apply decompose_det with (x := e) (C0 := E0) (C1 := E1) ;
                                       assumption.
  remember H3 as H3'.
  clear HeqH3'.
  apply proj2 in H3'.
  subst. f_equal. apply red_det with (x := e'). apply proj1 in H3. subst. assumption.
  apply proj1 in H3. subst. assumption.
Qed.

(* Now let's prove some stuff about pyret *)

Inductive no_deltas : exp -> Prop :=
  | nd_lam : forall l a body, no_deltas body -> no_deltas (elam l a body)
  | nd_app : forall fn arg, no_deltas fn -> no_deltas arg -> no_deltas (eapp fn arg)
  | nd_obj : forall l vs, Forall no_deltas (values vs) -> no_deltas (eobj l vs)
  | nd_getfield : forall a o, no_deltas o -> no_deltas (egetfield a o)
  | nd_bool : forall l b, no_deltas (ebool l b).

Inductive sub_exp : exp -> exp -> Prop :=
  | sub_eq : forall e e', e = e' -> sub_exp e e'
  | sub_lam : forall bs a e e', sub_exp e e' -> sub_exp e (elam bs a e')
  | sub_app1 : forall fn arg e, sub_exp e fn -> sub_exp e (eapp fn arg)
  | sub_app2 : forall fn arg e, sub_exp e arg -> sub_exp e (eapp fn arg)
  | sub_obj : forall bs vs e, Exists (fun e' => sub_exp e e') (values vs) ->
                              sub_exp e (eobj bs vs)
  | sub_delta1 : forall a e1 e2 e, sub_exp e e1 -> sub_exp e (edelta a e1 e2)
  | sub_delta2 : forall a e1 e2 e, sub_exp e e2 -> sub_exp e (edelta a e1 e2)
  | sub_getfield : forall a o e, sub_exp e o -> sub_exp e (egetfield a o).

Example sub_exp_lam1 : sub_exp (ebool [] true) (elam [] __arg__ (ebool [] true)).
Proof.
  apply sub_lam. apply sub_eq. reflexivity.
Qed.

Example sub_exp_obj2 : ~ sub_exp (ebool [] true) (eobj [] [(f1, ebool [] false)]).
Proof.
  unfold not. intro.
  inversion H. subst. inversion H0. subst. inversion H2. subst. inversion H1.
  subst. inversion H0. subst. apply Exists_nil in H1. assumption.
Qed.

(* Is this the only way of doing this? seems crazy *)
Inductive not_lam : exp -> Prop :=
  | not_lam_app : forall fn arg, not_lam (eapp fn arg)
  | not_lam_id : forall i, not_lam (eid i)
  | not_lam_obj : forall l vs, not_lam (eobj l vs)
  | not_lam_bool : forall l v, not_lam (ebool l v)
  | not_lam_brand : forall b, not_lam (ebrand b)
  | not_lam_delta : forall a e1 e2, not_lam (edelta a e1 e2)
  | not_lam_getfield : forall a o, not_lam (egetfield a o).

Inductive not_obj : exp -> Prop :=
  | not_obj_lam : forall l a b, not_obj (elam l a b)
  | not_obj_app : forall fn arg, not_obj (eapp fn arg)
  | not_obj_id : forall i, not_obj (eid i)
  | not_obj_bool : forall l v, not_obj (ebool l v)
  | not_obj_brand : forall b, not_obj (ebrand b)
  | not_obj_delta : forall a e1 e2, not_obj (edelta a e1 e2)
  | not_obj_getfield : forall a o, not_obj (egetfield a o).

Inductive not_brand : exp -> Prop :=
  | not_brand_lam : forall l a b, not_brand (elam l a b)
  | not_brand_app : forall fn arg, not_brand (eapp fn arg)
  | not_brand_id : forall i, not_brand (eid i)
  | not_brand_obj : forall l vs, not_brand (eobj l vs)
  | not_brand_bool : forall l v, not_brand (ebool l v)
  | not_brand_delta : forall a e1 e2, not_brand (edelta a e1 e2)
  | not_brand_getfield : forall a o, not_brand (egetfield a o).

Inductive stuck : exp -> Prop :=
  (* First the non-recursive cases *)
  | stuck_app : forall e a, not_lam e -> stuck (eapp e a)
  | stuck_id : forall a, stuck (eid a)
  | stuck_getfield : forall a e, not_obj e -> stuck (egetfield a e)
  | stuck_delta_hb : forall e b, not_brand b -> stuck (edelta has_brand_delta b e)
  | stuck_delta_ab : forall e b, not_brand b -> stuck (edelta add_brand_delta b e)
  (* Now the recursive ones *)
  | stuck_app1 : forall fn arg, stuck fn -> stuck (eapp fn arg)
  | stuck_app2 : forall fn arg, stuck arg -> stuck (eapp fn arg)
  | stuck_obj : forall l vs, Exists stuck (values vs) -> stuck (eobj l vs)
  | stuck_delta1 : forall a e1 e2, stuck e1 -> stuck (edelta a e1 e2)
  | stuck_delta2 : forall a e1 e2, stuck e2 -> stuck (edelta a e1 e2)
  | stuck_getfieldr : forall a o, stuck o -> stuck (egetfield a o).

Theorem pyret_progress : forall e, value e \/ stuck e \/ (exists e', step e e').
Proof.
  intros.
  induction e.
  Case "elam". left. constructor.
  Case "eapp". inversion IHe1.
  SCase "value e1". inversion H; try (right; left;  constructor; constructor).
  SSCase "elam".
  inversion IHe2.
  SSSCase "value e2".
  right. right. exists (subst xs e2 b).
  assert (plug (subst xs e2 b) E_hole = subst xs e2 b). auto. rewrite <- H2.
  apply sdecompose with (e' := (eapp (elam bs xs b) e2)). constructor. constructor. constructor.
  assumption. constructor. assumption.
  inversion H1.
  SSSCase "stuck e2".
  right. left. apply stuck_app2. assumption.
  SSSCase "step e2".
  inversion H2. right. right. inversion H3. subst. exists (plug e'' (E_app2 (elam bs xs b) E0)).
  apply sdecompose with (e' := e'). constructor. constructor. assumption. assumption.
  inversion H.
  SCase "stuck e1". right. left. apply stuck_app1. assumption.
  SCase "step e1".
  inversion H0. right. right. inversion H1. subst. exists (plug e'' (E_app1 E0 e2)).
  apply sdecompose with (e' := e'). constructor. assumption. assumption.
  Case "eid". right. left. constructor.
  Case "eobj".
  (* This is the hard case *) admit.
  Case "ebool". left. constructor.
  Case "ebrand". left. constructor.
  Case "edelta".
  inversion IHe1.
  inversion H; try solve [right; left; destruct a; repeat constructor].
  SCase "ebrand". inversion IHe2. right. right. destruct a.
  repeat econstructor; auto.
  inversion H1.
  SSCase "ebool".
  exists (plug (ebool (b::l) b0) E_hole). eapply sdecompose. constructor.
  constructor. constructor. constructor. assert (ebool (b::l) b0 = add_brand b (ebool l b0)).
  reflexivity. rewrite H3. constructor. constructor.
  SSCase "eobj".
  (* Here *)


  constructor.
  assert (plug x (E_app2 (elam bs xs b) E_hole) = (eapp (elam bs xs b) x)). constructor.
  rewrite <- H4.


  apply sdecompose with (e' := e2). constructor. constructor. constructor.


  inversion H3. inversion H5. assumption. subst. constructor. apply decompose_ae in H9.
  inversion H9. subst.
  apply red_ae with (e' := x). inversion H3. subst.

  SSCase "eobj".


Theorem brands_unforgable : forall (b : brand) (e1 : exp) (e2 : exp) (p : exp) (r : exp),
                              has_brand_rel e1 b -> no_deltas p ->
                              (forall e, sub_exp e p -> ~ e = e1 -> ~ has_brand_rel e b) ->
                              sub_exp e1 p -> sub_exp e2 p -> multistep p r ->
                              has_brand_rel r b -> r = e1.


(* TODO: progress (untyped) - define stuck states, forall e e', e <> e' ->
                                                   value e \/ stuck e \/ step e e'*)




End Pyret.