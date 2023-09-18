From stdpp Require Export gmap.
From ffpl.lib Require Export prelude.

(** * Finite maps *)
(** This file provides lemmas on finite maps (functions with a finite domain) [gmap].
  The stdpp library provides a definitions and lemmas on finite maps [gmap], but states lemmas axiomatically in terms of the [FinMap] typeclass, which may make them hard to read for novice users of stdpp.
  We therefore instantiate the most important lemmas specifically for [gmap] to make the statements easier to comprehend.

  The most important operations are:
   - the empty map empty contains no elements
   - the singleton map {[ i := v ]} defines a singleton map that maps key i to value v
   - the insert operation <[ i := v ]> m inserts the association i |-> v to the map m, overriding any mappings for i in m
   - the delete operatin delete i m deletes the mapping for key i from m
   - the lookup operation m !! i lookups a key i, and yields the optional value associated with i
   - the fmap operation f <$> m maps a function f over all values stored in the map
   - the subset relation m1 `subseteq` m2 states that all associations of map m1 are also included in map m2
   - the dom operation dom m yields a finite set ([gset]) of the domain of the map

  stdpp's maps satisfy extensional Leibniz equality -- that is, two maps X and Y are equal (X = Y) iff they represent the same finite function.

  We also diverge from the std++ lemmas in one key point:
  the lemma [lookup_insert] is actually the universal lemma that works for all lookups;
  [lookup_insert_eq] is the one that works when looked-up and inserted key are equal.
 *)

Section map.
  (* keys need to be countable, i.e., have an injection into positive integers *)
  Context {K} {A B : Type} `{Countable K}.
  Implicit Types (m : gmap K A).

  Lemma lookup_empty i : (empty : gmap K A) !! i = None.
  Proof. apply lookup_empty. Qed.

  Lemma lookup_fmap (f : A -> B) (m : gmap K A) i : (f <$> m) !! i = f <$> m !! i.
  Proof. apply lookup_fmap. Qed.
  Lemma map_fmap_mono (f : A -> B) m1 m2 : m1 `subseteq` m2 -> f <$> m1 `subseteq` f <$> m2.
  Proof. apply map_fmap_mono. Qed.
  Lemma fmap_insert (f : A -> B) m i x : f <$> <[i := x]> m = <[i := f x]> (f <$> m).
  Proof. apply fmap_insert. Qed.
  Lemma fmap_empty (f : A -> B) : f <$> (empty : gmap K A) = empty.
  Proof. apply fmap_empty. Qed.
  Lemma map_fmap_compose {C} (f : A -> B) (g : B -> C) m : (compose g f) <$> m = g <$> (f <$> m).
  Proof. apply map_fmap_compose. Qed.
  Lemma map_fmap_ext (f1 f2 : A -> B) m :
    (forall i x, m !! i = Some x -> f1 x = f2 x) ->
    f1 <$> m = f2 <$> m.
  Proof. apply map_fmap_ext. Qed.

  Lemma map_eq_iff m1 m2 : m1 = m2 <-> forall i, m1 !! i = m2 !! i.
  Proof. apply map_eq_iff. Qed.
  Lemma map_subseteq_spec m1 m2 :
    m1 `subseteq` m2 <-> forall i x, m1 !! i = Some x -> m2 !! i = Some x.
  Proof. apply map_subseteq_spec. Qed.
  Lemma lookup_weaken m1 m2 i x :
    m1 !! i = Some x -> m1 `subseteq` m2 -> m2 !! i = Some x.
  Proof. apply lookup_weaken. Qed.
  Lemma lookup_weaken_is_Some m1 m2 i :
    is_Some (m1 !! i) -> m1 `subseteq` m2 -> is_Some (m2 !! i).
  Proof. apply lookup_weaken_is_Some. Qed.
  Lemma lookup_weaken_None m1 m2 i :
    m2 !! i = None -> m1 `subseteq` m2 -> m1 !! i = None.
  Proof. apply lookup_weaken_None. Qed.
  Lemma lookup_weaken_inv m1 m2 i x y :
    m1 !! i = Some x -> m1 `subseteq` m2 -> m2 !! i = Some y -> x = y.
  Proof. apply lookup_weaken_inv. Qed.
  Lemma lookup_ne m i j : m !! i != m !! j -> i != j.
  Proof. apply lookup_ne. Qed.
  Lemma map_empty m : m = empty <-> forall i, m !! i = None.
  Proof. apply map_empty. Qed.
  Lemma lookup_empty_is_Some i : ~is_Some ((empty : gmap K A) !! i).
  Proof. apply lookup_empty_is_Some. Qed.
  Lemma lookup_empty_Some i (x : A) : ~(empty : gmap K A) !! i = Some x.
  Proof. apply lookup_empty_Some. Qed.
  Lemma map_empty_subseteq m : empty `subseteq` m.
  Proof. apply map_empty_subseteq. Qed.


  Lemma lookup_delete_eq m i : delete i m !! i = None.
  Proof. apply lookup_delete. Qed.
  Lemma lookup_delete_ne m i j : i != j -> delete i m !! j = m !! j.
  Proof. apply lookup_delete_ne. Qed.
  Lemma lookup_delete m i j :
    delete i m !! j = if decide (i = j) then None else m !! j.
  Proof. case_decide; simplify_eq; eauto using lookup_delete_eq, lookup_delete_ne. Qed.
  Lemma lookup_delete_Some m i j y :
    delete i m !! j = Some y <-> i != j /\ m !! j = Some y.
  Proof. apply lookup_delete_Some. Qed.
  Lemma lookup_delete_is_Some m i j :
    is_Some (delete i m !! j) <-> i != j /\ is_Some (m !! j).
  Proof. apply lookup_delete_is_Some. Qed.
  Lemma lookup_delete_None m i j :
    delete i m !! j = None <-> i = j \/ m !! j = None.
  Proof. apply lookup_delete_None. Qed.
  Lemma delete_empty i : delete i empty = (empty : gmap K A).
  Proof. apply delete_empty. Qed.
  Lemma delete_commute m i j :
    delete i (delete j m) = delete j (delete i m).
  Proof. apply delete_commute. Qed.
  Lemma delete_insert_ne m i j x :
    i != j -> delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
  Proof. apply delete_insert_ne. Qed.
  Lemma delete_notin m i : m !! i = None -> delete i m = m.
  Proof. apply delete_notin. Qed.
  Lemma delete_idemp m i :
    delete i (delete i m) = delete i m.
  Proof. apply delete_idemp. Qed.
  Lemma delete_insert m i x :
    m !! i = None -> delete i (<[i:=x]>m) = m.
  Proof. apply delete_insert. Qed.
  Lemma delete_insert_delete m i x :
    delete i (<[i:=x]>m) = delete i m.
  Proof. apply delete_insert_delete. Qed.
  Lemma delete_subseteq m i : delete i m `subseteq` m.
  Proof. apply delete_subseteq. Qed.
  Lemma delete_mono m1 m2 i : m1 `subseteq` m2 -> delete i m1 `subseteq` delete i m2.
  Proof. apply delete_mono. Qed.

  (** ** Properties of the [insert] operation *)
  Lemma lookup_insert_eq m i x : <[i:=x]>m !! i = Some x.
  Proof. apply lookup_insert. Qed.
  Lemma lookup_insert_rev m i x y : <[i:=x]>m !! i = Some y -> x = y.
  Proof. apply lookup_insert_rev. Qed.
  Lemma lookup_insert_ne m i j x : i != j -> <[i:=x]>m !! j = m !! j.
  Proof. apply lookup_insert_ne. Qed.
  Lemma lookup_insert m i j x :
    <[i:=x]>m !! j = if decide (i = j) then Some x else m !! j.
  Proof. case_decide; simplify_eq; eauto using lookup_insert_eq, lookup_insert_ne. Qed.
  Lemma insert_insert m i x y : <[i:=x]>(<[i:=y]>m) = <[i:=x]>m.
  Proof. apply insert_insert. Qed.
  Lemma insert_commute m i j x y :
    i != j -> <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
  Proof. apply insert_commute. Qed.
  Lemma lookup_insert_Some m i j x y :
    <[i:=x]>m !! j = Some y <-> (i = j /\ x = y) \/ (i != j /\ m !! j = Some y).
  Proof. apply lookup_insert_Some. Qed.
  Lemma lookup_insert_is_Some m i j x :
    is_Some (<[i:=x]>m !! j) <-> i = j \/ i != j /\ is_Some (m !! j).
  Proof. apply lookup_insert_is_Some. Qed.
  Lemma lookup_insert_None m i j x :
    <[i:=x]>m !! j = None <-> m !! j = None /\ i != j.
  Proof. apply lookup_insert_None. Qed.
  Lemma insert_id m i x : m !! i = Some x -> <[i:=x]>m = m.
  Proof. apply insert_id. Qed.
  Lemma insert_non_empty m i x : <[i:=x]>m != empty.
  Proof. apply insert_non_empty. Qed.
  Lemma insert_delete_insert m i x : <[i:=x]>(delete i m) = <[i:=x]> m.
  Proof. apply insert_delete_insert. Qed.
  Lemma insert_delete m i x :
    m !! i = Some x -> <[i:=x]> (delete i m) = m.
  Proof. apply insert_delete. Qed.

  Lemma insert_subseteq m i x : m !! i = None -> m `subseteq` <[i:=x]>m.
  Proof. apply insert_subseteq. Qed.
  Lemma insert_mono m1 m2 i x : m1 `subseteq` m2 -> <[i:=x]> m1 `subseteq` <[i:=x]>m2.
  Proof. apply insert_mono. Qed.
  Lemma insert_subseteq_r m1 m2 i x :
    m1 !! i = None -> m1 `subseteq` m2 -> m1 `subseteq` <[i:=x]>m2.
  Proof. apply insert_subseteq_r. Qed.
  Lemma insert_subseteq_l m1 m2 i x :
    m2 !! i = Some x -> m1 `subseteq` m2 -> <[i:=x]> m1 `subseteq` m2.
  Proof. apply insert_subseteq_l. Qed.

  Lemma insert_delete_subseteq m1 m2 i x :
    m1 !! i = None -> <[i:=x]> m1 `subseteq` m2 -> m1 `subseteq` delete i m2.
  Proof. apply insert_delete_subseteq. Qed.
  Lemma delete_insert_subseteq m1 m2 i x :
    m1 !! i = Some x -> delete i m1 `subseteq` m2 -> m1 `subseteq` <[i:=x]> m2.
  Proof. apply delete_insert_subseteq. Qed.

  Lemma map_delete_subseteq (k : K) m :
    delete k m `subseteq` m.
  Proof.
    apply map_subseteq_spec.
    intros i x. rewrite lookup_delete_Some. intros [ ]; done.
  Qed.

  Lemma insert_union_singleton_l (k : K) m x :
    <[ k := x ]> m = {[ k := x ]} `union` m.
  Proof. apply insert_union_singleton_l. Qed.
  Lemma insert_union_singleton_r (k : K) m x :
    m !! k = None -> <[ k := x ]> m = m `union` {[ k := x ]}.
  Proof. apply insert_union_singleton_r. Qed.

  Lemma lookup_union m1 m2 i :
    (m1 `union` m2) !! i = (m1 !! i) `union` (m2 !! i).
  Proof. apply lookup_union_with. Qed.
  Lemma lookup_union_Some_l m1 m2 (k : K) x :
    m1 !! k = Some x -> (m1 `union` m2) !! k = Some x.
  Proof. apply lookup_union_Some_l. Qed.
  Lemma lookup_union_r m1 m2 (k : K) :
    m1 !! k = None -> (m1 `union` m2) !! k = m2 !! k.
  Proof. apply lookup_union_r. Qed.

  (** map disjoint *)
  Lemma map_disjoint_spec m1 m2 :
    map_disjoint m1 m2 <-> forall i x y, m1 !! i = Some x -> m2 !! i = Some y -> False.
  Proof. apply map_disjoint_spec. Qed.
  Lemma map_disjoint_alt m1 m2 :
    map_disjoint m1 m2 <-> forall i, m1 !! i = None \/ m2 !! i = None.
  Proof. apply map_disjoint_alt. Qed.
  Lemma map_not_disjoint m1 m2 :
    ~ map_disjoint m1 m2 <-> exists i x1 x2, m1 !! i = Some x1 /\ m2 !! i = Some x2.
  Proof. apply map_not_disjoint. Qed.
  Global Instance map_disjoint_sym : Symmetric (map_disjoint (M:=gmap K) (A:=A)).
  Proof. apply map_disjoint_sym. Qed.
  Lemma map_disjoint_empty_l m : map_disjoint empty m.
  Proof. apply map_disjoint_empty_l. Qed.
  Lemma map_disjoint_empty_r m : map_disjoint m empty.
  Proof. apply map_disjoint_empty_r. Qed.

  (** Domain *)
  Lemma elem_of_dom m i : i `elem` dom m <-> is_Some (m !! i).
  Proof. apply elem_of_dom. Qed.


  Lemma elem_of_dom_2 m i x : m !! i = Some x -> i `elem` dom m.
  Proof. apply elem_of_dom_2. Qed.
  Lemma not_elem_of_dom m i : ~(i `elem` dom m) <-> m !! i = None.
  Proof. apply not_elem_of_dom. Qed.
  Lemma subseteq_dom m1 m2 : m1 `subseteq` m2 -> dom m1 `subseteq` dom m2.
  Proof. apply subseteq_dom. Qed.

  Lemma dom_empty : dom (empty : gmap K A) = empty.
  Proof. apply dom_empty_L. Qed.
  Lemma dom_empty_iff m : dom m = empty <-> m = empty.
  Proof. apply dom_empty_iff_L. Qed.

  Lemma dom_insert m i x : dom (<[i:=x]>m) = {[ i ]} `union` dom m.
  Proof. apply dom_insert_L. Qed.
  Lemma dom_insert_lookup m i x :
    is_Some (m !! i) -> dom (<[i:=x]>m) = dom m.
  Proof. apply dom_insert_lookup_L. Qed.
  Lemma dom_insert_subseteq m i x : dom m `subseteq` dom (<[i:=x]>m).
  Proof. apply dom_insert_subseteq. Qed.


  Lemma dom_singleton (i : K) (x : A) : dom ({[i := x]} : gmap K A) = {[ i ]}.
  Proof. apply dom_singleton_L. Qed.
  Lemma dom_delete m i : dom (delete i m) = dom m `difference` {[ i ]}.
  Proof. apply dom_delete_L. Qed.

  Lemma dom_fmap (f : A -> B) (m : gmap K A) : dom (f <$> m) = dom m.
  Proof. apply dom_fmap_L. Qed.

  (** difference *)
  Lemma lookup_difference m1 m2 i :
    (m1 `difference` m2) !! i = match m2 !! i with None => m1 !! i | _ => None end.
  Proof.
    unfold difference, map_difference; rewrite lookup_difference_with.
    destruct (m1 !! i), (m2 !! i); done.
  Qed.

  (* TODO: upstream? *)
  Lemma map_difference_mono m1 m2 m3 :
    m1 `subseteq` m2 ->
    m1 `difference` m3 `subseteq` m2 `difference` m3.
  Proof.
    intros ?. apply map_subseteq_spec.
    intros i x. rewrite !lookup_difference_Some.
    intros [? ?]; split; [ | done]. by eapply map_subseteq_spec.
  Qed.

  (* Upstream? *)
  Lemma map_difference_union' m1 m2 m3 :
    map_disjoint m1 m2 ->
    (m1 `union` m2) `difference` m3 = (m1 `difference` m3) `union` (m2 `difference` m3).
  Proof.
    intros Hdisj. apply map_eq.
    intros i. destruct (((m1 `union` m2) `difference` m3) !! i) as [ s | ] eqn:Hlook.
    - apply lookup_difference_Some in Hlook as [Hlook1 Hlook2].
      apply lookup_union_Some in Hlook1; [ | done].
      symmetry. apply lookup_union_Some.
      { eapply map_disjoint_weaken; [ done | | ]; apply map_subseteq_difference_l; done. }
      destruct Hlook1 as [ Hlook1 | Hlook1]; [left | right]; apply lookup_difference_Some; done.
    - symmetry. apply lookup_difference_None in Hlook as [ Hlook | Hlook].
      + apply lookup_union_None in Hlook as [ ? ?].
        apply lookup_union_None; split; apply lookup_difference_None; eauto.
      + apply lookup_union_None; split; apply lookup_difference_None; eauto.
  Qed.

  (* TODO: upstream the first inclusion as a lemma? *)
  Lemma map_disjoint_difference m1 m2 :
    map_disjoint m1 m2 ->
    m1 = m1 `difference` m2.
  Proof.
    intros Hdisj. apply (partial_order_anti_symm (R := subseteq)).
    - apply map_subseteq_spec.
      intros i x Hlook. apply lookup_difference_Some. split; [done | ].
      by eapply map_disjoint_Some_l.
    - by apply map_subseteq_difference_l.
  Qed.

End map.

Global Hint Extern 0 (map_disjoint (_ _)) => symmetry; eassumption : core.
