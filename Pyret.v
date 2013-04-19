Require Import Prelude.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Module Pyret (Import Atom : ATOM) (Import String : STRING).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom).
Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Atom_as_OT).


Lemma eq_atom_refl : forall (a : atom), Atom.eq a a.
Proof. reflexivity. Qed.
Lemma eq_atom_sym : forall (a1 a2 : atom), Atom.eq a1 a2 -> Atom.eq a2 a1.
Proof. intros. symmetry. assumption. Qed.
Lemma eq_atom_trans : forall (a1 a2 a3 : atom), Atom.eq a1 a2 -> Atom.eq a2 a3 -> Atom.eq a1 a3.
Proof. intros. transitivity a2; assumption. Qed.

Add Relation Atom.atom Atom.eq
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


Definition atom := Atom.t. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.

Parameter __check__ : atom.
Parameter __brand__ : atom.
Parameter __has_brand__ : atom.
Parameter __add_brand__ : atom.

Axiom check_brand_distinct : __check__ <> __brand__.
Axiom has_add_distinct : __has_brand__ <> __add_brand__.

(* Tests *)
Goal (if Atom.eq_dec __check__ __check__ then 5 else 6) = 5.
destruct_eq_dec __check__ __check__. Defined.
Goal (if Atom.eq_dec __check__ __brand__ then 5 else 6) = 6.
destruct_eq_dec __check__ __brand__.
  exfalso. apply check_brand_distinct; auto. Qed.


Inductive brand : Type :=
  | mkbrand : atom -> brand.

Unset Elimination Schemes.
Inductive exp : Type :=
  | elam : list brand -> atom -> exp -> exp
  | eapp : exp -> exp -> exp
  | eid : atom -> exp
  | eobj : list brand -> list (atom * exp) -> exp
  | ebool : list brand -> bool -> exp
  | ebrand : brand -> exp
  | edelta : atom -> exp -> exp -> exp
  | egetfield : atom -> exp -> exp.
Set Elimination Schemes.

Definition exp_rec :=
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

Inductive value : exp -> Prop :=
  | vbool : forall l b, value (ebool l b)
  | vobj : forall l fs, Forall value (map snd fs) -> value (eobj l fs)
  | vlam : forall bs xs b, value (elam bs xs b)
  | vbrand : forall b, value (ebrand b).

 Hint Constructors value.

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
  | sapp : forall x e b l,
             value e ->
             step (eapp (elam l x b) e)
                  (subst x e b)
  | sobj : forall bs vs a e e' es,
             Forall value (map snd vs) ->
             Forall (fun x => ~ value x) (map snd es) ->
             ~ value e ->
             step e e' ->
             step (eobj bs (vs ++ (cons (a,e) es)))
                  (eobj bs (vs ++ (cons (a,e') es)))
  | sgetfield : forall bs vs a,
                  Forall value (map snd vs) ->
                  In a (map fst vs) ->
                  step (eobj bs vs)
                       (GET THE FIELD)
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

Example step_obj1 :
  multistep
    (eobj nil
          ((f1,ebool nil true)
             ::(f2, edelta __has_brand__
                       (ebrand (mkbrand __some_brand__))
                       (ebool nil true))
             ::nil))
    (eobj nil ((f1,ebool nil true)::(f2,ebool nil false)::nil)).
Proof.
  rewrite fold_cons.
  rewrite <- app_split.
  eapply multi_step with
  (y := (eobj nil ([(f1, ebool [] true)] ++ [(f2, ebool [] false)] ++ nil))).
  apply sobj.
  simpl.
  constructor.
  constructor.
  constructor.
  constructor.
  unfold not.
  intros.
  inversion H.
  apply sdelta_hb.
  constructor.
  rewrite app_split.
  simpl.
  apply multi_refl.
Qed.


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



End Pyret.