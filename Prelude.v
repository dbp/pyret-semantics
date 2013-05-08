Require Export Coq.Arith.EqNat.
Require Export Coq.Arith.Le.
Require Export Coq.Arith.Lt.
Require Export Coq.MSets.MSetList.
Require Export Coq.FSets.FMapList.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Decidable.
Require Export Omega.
Require Export SfLib.
Set Implicit Arguments.
Require Export Setoid SetoidClass.
Require Export SetoidDec.


Module UOT_to_OrderedTypeLegacy (UOT:OrderedType) <: (IsEqOrig UOT) <: OrderedType.OrderedType.
  Definition t := UOT.t.
  Definition lt := UOT.lt.
  Definition eq := UOT.eq.
  Definition eq_refl := let (r, _, _) := UOT.eq_equiv in r.
  Definition eq_sym := let (_, s, _) := UOT.eq_equiv in s.
  Definition eq_trans := let (_, _, t) := UOT.eq_equiv in t.
  Lemma lt_trans : forall x y z : t, UOT.lt x y -> UOT.lt y z -> UOT.lt x z.
  Proof. destruct UOT.lt_strorder as [i t]. apply t. Qed.
  Lemma lt_not_eq : forall x y : t, UOT.lt x y -> ~ UOT.eq x y.
  Proof. destruct UOT.lt_strorder as [i t]. intros. intro. rewrite H0 in *. exact (i y H). Qed.
  Definition compare (x y : t) : OrderedType.Compare UOT.lt UOT.eq x y :=
    match (CompareSpec2Type (UOT.compare_spec x y)) with
      | CompLtT l => OrderedType.LT l
      | CompEqT e => OrderedType.EQ e
      | CompGtT g => OrderedType.GT g
    end.
  Definition eq_dec := UOT.eq_dec.
  Definition eq_equiv := UOT.eq_equiv.
  Definition lt_strorder := UOT.lt_strorder.
  Definition lt_compat := UOT.lt_compat.
End UOT_to_OrderedTypeLegacy.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module AtomUOT : Orders.UsualOrderedType
      with Definition t := atom.
  Module Atom_as_OT : OrderedType.OrderedType
    with Definition t := atom
    with Definition eq := AtomUOT.eq
      := UOT_to_OrderedTypeLegacy(AtomUOT).
  Parameter atom_fresh_for_list : forall (xs : list atom),
    exists x : atom, ~ List.In x xs.
  Definition atom_eq_dec := AtomUOT.eq_dec.
  Lemma atom_dec_eq : forall (a1 a2 : atom), AtomUOT.eq a1 a2 \/ ~ AtomUOT.eq a1 a2.
  Proof. intros. assert (H := atom_eq_dec a1 a2). unfold AtomUOT.eq. destruct H; subst; auto. Qed.

End ATOM.

Module Type STRING.

  Parameter string : Set.
  Declare Module String : Orders.UsualOrderedType with Definition t := string.
  Module String_as_OT : OrderedType.OrderedType with Definition t := string := UOT_to_OrderedTypeLegacy(String).
  Definition string_eq_dec := String.eq_dec.
  Lemma string_dec_eq : forall (s1 s2 : string), s1 = s2 \/ s1 <> s2.
  Proof. intros. assert (H := string_eq_dec s1 s2). destruct H; subst; auto. Qed.

End STRING.

